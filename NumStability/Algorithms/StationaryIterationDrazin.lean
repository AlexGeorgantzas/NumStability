-- Algorithms/StationaryIterationDrazin.lean
--
-- Higham Chapter 17 "Stationary Iterative Methods", §17.4 "Singular Systems":
-- the Drazin-inverse vocabulary of eqs (17.23)-(17.26) and the infinite
-- singular bounds (17.30)-(17.32), built on the semiconvergent block-form
-- data of eq (17.22) from `StationaryIterationSemiconvergent.lean`.
--
-- The printed development takes `G = P·diag(I, Γ)·P⁻¹` with `ρ(Γ) < 1`
-- (eq (17.22)) and derives:
--   * (17.23)  `I − G = P·diag(0, I−Γ)·P⁻¹`;
--   * (17.24)  `(I−G)^D = P·diag(0, (I−Γ)⁻¹)·P⁻¹` (`I−Γ` nonsingular);
--   * (17.25)  `lim Gᵐ = I − (I−G)^D (I−G)`;
--   * (17.26)  `lim x_m = (I − (I−G)^D(I−G))x₀ + (I−G)^D M⁻¹ b`;
--   * (17.30)  `GⁱE = P·diag(0, Γⁱ)·P⁻¹ = (GE)ⁱ` for `i ≥ 1`, where
--              `E = (I−G)^D(I−G)`;
--   * (17.31)  the all-m normwise forward bound with the infinite-sum
--              constant `Σ'ᵢ ‖GⁱEM⁻¹‖∞ + (m+1)‖(I−E)M⁻¹‖∞`;
--   * (17.32)  the componentwise analogue with the constant
--              `c(A)|(I−G)^D M⁻¹| + (m+1)|(I−E)M⁻¹|`.
--
-- Conventions, mirroring `StationaryIterationSemiconvergent.lean`: the
-- (17.22) block form is HYPOTHESIS data `(r, J, X, X⁻¹)` with `hJtop`
-- (identity top rows), `hJcross` (vanishing bottom-left block), a row-sum
-- contraction certificate `q < 1` for the bottom rows (an ∞-norm
-- strengthening of the printed `ρ(Γ) < 1`), and two-sided inverse data
-- `hXr`/`hXl`/`hsim`.  The bottom-block inverse `(I−Γ)⁻¹` of the printed
-- (17.24) enters as data `W` with `hWshape` (`W` vanishes outside the
-- bottom-right block) and the two-sided identities
-- `(I−J)·W = W·(I−J) = diag(0, I_{n−r})` (`hW1`/`hW2`).  The existence of
-- all this data — Jordan-form background and invertibility of `I−Γ` — is
-- not formalized; UNIQUENESS of the Drazin inverse is likewise not
-- formalized (only the defining identities are proved, matching core
-- scope).  In the book's notation `E = (I−G)^D(I−G)` is the range
-- projector and `I−E = lim Gᵐ`; in this repository those are
-- `semiconvergentE` and `oneEigenProjector` respectively.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import NumStability.Analysis.MatrixAlgebra
import NumStability.Algorithms.MatrixPowers
import NumStability.Algorithms.StationaryIteration
import NumStability.Algorithms.StationaryIterationSemiconvergent

namespace NumStability

open scoped BigOperators

-- ============================================================
-- §17.4  A. The bottom-block projector diag(0, I_{n−r})
-- ============================================================

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    eqs (17.23)-(17.24): the coordinate projector `diag(0, I_{n−r})` onto the
    bottom (`Γ`) block of the semiconvergent form of eq (17.22) — the
    complement of `topProjector`. -/
noncomputable def bottomProjector (n r : ℕ) : Fin n → Fin n → ℝ :=
  fun i j => if i = j ∧ ¬(i : ℕ) < r then 1 else 0

/-- Bottom rows of `bottomProjector` are identity rows. -/
theorem bottomProjector_apply_bottom {n r : ℕ} {k : Fin n}
    (hk : ¬(k : ℕ) < r) (l : Fin n) :
    bottomProjector n r k l = if k = l then 1 else 0 := by
  unfold bottomProjector
  by_cases h : k = l
  · rw [if_pos ⟨h, hk⟩, if_pos h]
  · rw [if_neg (fun hc => h hc.1), if_neg h]

/-- Top rows of `bottomProjector` vanish. -/
theorem bottomProjector_apply_top {n r : ℕ} {k : Fin n}
    (hk : (k : ℕ) < r) (l : Fin n) :
    bottomProjector n r k l = 0 := by
  unfold bottomProjector
  exact if_neg (fun hc => hc.2 hk)

/-- The top and bottom coordinate projectors are complementary:
    `diag(I_r, 0) + diag(0, I_{n−r}) = I`. -/
theorem topProjector_add_bottomProjector (n r : ℕ) (i j : Fin n) :
    topProjector n r i j + bottomProjector n r i j = idMatrix n i j := by
  unfold topProjector bottomProjector idMatrix
  by_cases hij : i = j
  · by_cases hi : (i : ℕ) < r
    · rw [if_pos ⟨hij, hi⟩, if_neg (fun hc => hc.2 hi), if_pos hij]
      ring
    · rw [if_neg (fun hc => hi hc.2), if_pos ⟨hij, hi⟩, if_pos hij]
      ring
  · rw [if_neg (fun hc => hij hc.1), if_neg (fun hc => hij hc.1), if_neg hij]
    ring

/-- Right multiplication by `bottomProjector` selects the bottom columns. -/
theorem matMul_bottomProjector_right (n r : ℕ) (B : Fin n → Fin n → ℝ)
    (i j : Fin n) :
    matMul n B (bottomProjector n r) i j =
      if ¬(j : ℕ) < r then B i j else 0 := by
  have hsum : matMul n B (bottomProjector n r) i j =
      B i j * bottomProjector n r j j := by
    calc matMul n B (bottomProjector n r) i j
        = ∑ k : Fin n, B i k * bottomProjector n r k j := rfl
      _ = B i j * bottomProjector n r j j :=
        Finset.sum_eq_single j
          (fun k _ hk => by
            have hzero : bottomProjector n r k j = 0 := by
              unfold bottomProjector
              exact if_neg (fun hc => hk hc.1)
            rw [hzero, mul_zero])
          (fun h => absurd (Finset.mem_univ j) h)
  rw [hsum]
  by_cases hj : (j : ℕ) < r
  · rw [if_neg (not_not_intro hj), bottomProjector_apply_top hj j, mul_zero]
  · rw [if_pos hj]
    have hone : bottomProjector n r j j = 1 := by
      unfold bottomProjector
      exact if_pos ⟨rfl, hj⟩
    rw [hone, mul_one]

/-- Left multiplication by `bottomProjector` selects the bottom rows. -/
theorem matMul_bottomProjector_left (n r : ℕ) (B : Fin n → Fin n → ℝ)
    (i j : Fin n) :
    matMul n (bottomProjector n r) B i j =
      if ¬(i : ℕ) < r then B i j else 0 := by
  by_cases hi : (i : ℕ) < r
  · rw [if_neg (not_not_intro hi)]
    exact matMul_row_zero n (bottomProjector n r) B i j
      (bottomProjector_apply_top hi)
  · rw [if_pos hi]
    exact matMul_row_id n (bottomProjector n r) B i j
      (bottomProjector_apply_bottom hi)

/-- The bottom-block projector `diag(0, I_{n−r})` is idempotent. -/
theorem bottomProjector_idempotent (n r : ℕ) :
    matMul n (bottomProjector n r) (bottomProjector n r) =
      bottomProjector n r := by
  ext i j
  rw [matMul_bottomProjector_left]
  by_cases hi : (i : ℕ) < r
  · rw [if_neg (not_not_intro hi)]
    exact (bottomProjector_apply_top hi j).symm
  · rw [if_pos hi]

-- ============================================================
-- §17.4  B. Entrywise (I − ·) multiplication helpers
-- ============================================================

/-- Left multiplication by a complement, entrywise:
    `((I − A)·B)_{ij} = B_{ij} − (A·B)_{ij}`. -/
theorem matSub_id_matMul_apply (n : ℕ) (A B : Fin n → Fin n → ℝ)
    (i j : Fin n) :
    matMul n (matSub_id n A) B i j = B i j - matMul n A B i j := by
  calc matMul n (matSub_id n A) B i j
      = ∑ k : Fin n, (idMatrix n i k - A i k) * B k j := rfl
    _ = ∑ k : Fin n, (idMatrix n i k * B k j - A i k * B k j) :=
        Finset.sum_congr rfl fun k _ => by ring
    _ = (∑ k : Fin n, idMatrix n i k * B k j) -
          ∑ k : Fin n, A i k * B k j := by
        rw [Finset.sum_sub_distrib]
    _ = B i j - matMul n A B i j := by
        have h := congrArg (fun T : Fin n → Fin n → ℝ => T i j)
          (matMul_id_left n B)
        have h' : ∑ k : Fin n, idMatrix n i k * B k j = B i j := by
          simpa [matMul] using h
        rw [h']
        rfl

/-- Right multiplication by a complement, entrywise:
    `(B·(I − A))_{ij} = B_{ij} − (B·A)_{ij}`. -/
theorem matMul_matSub_id_apply (n : ℕ) (A B : Fin n → Fin n → ℝ)
    (i j : Fin n) :
    matMul n B (matSub_id n A) i j = B i j - matMul n B A i j := by
  calc matMul n B (matSub_id n A) i j
      = ∑ k : Fin n, B i k * (idMatrix n k j - A k j) := rfl
    _ = ∑ k : Fin n, (B i k * idMatrix n k j - B i k * A k j) :=
        Finset.sum_congr rfl fun k _ => by ring
    _ = (∑ k : Fin n, B i k * idMatrix n k j) -
          ∑ k : Fin n, B i k * A k j := by
        rw [Finset.sum_sub_distrib]
    _ = B i j - matMul n B A i j := by
        have h := congrArg (fun T : Fin n → Fin n → ℝ => T i j)
          (matMul_id_right n B)
        have h' : ∑ k : Fin n, B i k * idMatrix n k j = B i j := by
          simpa [matMul] using h
        rw [h']
        rfl

-- ============================================================
-- §17.4  C. Eq (17.23): I − G = X·(I − J)·X⁻¹
-- ============================================================

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    eq (17.23): given the (17.22) similarity data `X⁻¹GX = J`, the
    complement conjugates: `I − G = X·(I − J)·X⁻¹`.  Together with
    `matSub_id_J_top_row` and `matSub_id_J_cross` below (which say `I − J`
    is `diag(0, I−Γ)`-shaped under the (17.22) block hypotheses), this is
    the printed `I − G = P·diag(0, I−Γ)·P⁻¹`. -/
theorem eq_17_23_block (n : ℕ) (G J X X_inv : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv)
    (hsim : matMul n X_inv (matMul n G X) = J) :
    matSub_id n G = matMul n X (matMul n (matSub_id n J) X_inv) := by
  have hG := eq_conjugate_of_similarity n G X X_inv J hXr hsim
  ext i j
  calc matSub_id n G i j
      = idMatrix n i j - G i j := rfl
    _ = (∑ k : Fin n, X i k * X_inv k j) -
          matMul n X (matMul n J X_inv) i j := by
        rw [hXr i j, ← hG]
        rfl
    _ = ∑ k : Fin n, (X i k * X_inv k j -
          X i k * matMul n J X_inv k j) := by
        rw [Finset.sum_sub_distrib]
        rfl
    _ = ∑ k : Fin n, X i k * (X_inv k j - matMul n J X_inv k j) :=
        Finset.sum_congr rfl fun k _ => by ring
    _ = ∑ k : Fin n, X i k * matMul n (matSub_id n J) X_inv k j :=
        Finset.sum_congr rfl fun k _ => by
          rw [matSub_id_matMul_apply n J X_inv k j]
    _ = matMul n X (matMul n (matSub_id n J) X_inv) i j := rfl

/-- Under the (17.22) top-row hypothesis, the top rows of `I − J` vanish —
    the zero top block of the printed (17.23) form `diag(0, I−Γ)`. -/
theorem matSub_id_J_top_row (n r : ℕ) (J : Fin n → Fin n → ℝ)
    (hJtop : ∀ i j : Fin n, (i : ℕ) < r → J i j = if i = j then 1 else 0)
    {i : Fin n} (hi : (i : ℕ) < r) (j : Fin n) :
    matSub_id n J i j = 0 := by
  unfold matSub_id idMatrix
  rw [hJtop i j hi]
  exact sub_self _

/-- Under the (17.22) cross-block hypothesis, the bottom-left block of
    `I − J` vanishes — the zero bottom-left block of the printed (17.23)
    form `diag(0, I−Γ)`. -/
theorem matSub_id_J_cross (n r : ℕ) (J : Fin n → Fin n → ℝ)
    (hJcross : ∀ i j : Fin n, ¬(i : ℕ) < r → (j : ℕ) < r → J i j = 0)
    {i j : Fin n} (hi : ¬(i : ℕ) < r) (hj : (j : ℕ) < r) :
    matSub_id n J i j = 0 := by
  unfold matSub_id idMatrix
  rw [hJcross i j hi hj,
    if_neg (fun h : i = j => hi (by rw [h]; exact hj))]
  ring

-- ============================================================
-- §17.4  D. Eq (17.24): the index-one Drazin inverse of I − G
-- ============================================================

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    eq (17.24): the printed Drazin inverse
    `(I−G)^D = P·diag(0, (I−Γ)⁻¹)·P⁻¹`, built from the block data as
    `X·W·X⁻¹` where `W` is the bottom-block inverse data (the
    `diag(0, (I−Γ)⁻¹)` of the printed formula, supplied by
    `hWshape`/`hW1`/`hW2`).  `drazinIG_spec` proves the defining index-one
    Drazin identities; uniqueness of the Drazin inverse is not
    formalized. -/
noncomputable def drazinIG (n : ℕ) (X W X_inv : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  matMul n X (matMul n W X_inv)

/-- The bottom-block inverse data absorbs the bottom projector on the
    right: `W·diag(0, I_{n−r}) = W`. -/
theorem W_mul_bottomProjector (n r : ℕ) (W : Fin n → Fin n → ℝ)
    (hWshape : ∀ i j : Fin n, (i : ℕ) < r ∨ (j : ℕ) < r → W i j = 0) :
    matMul n W (bottomProjector n r) = W := by
  ext i j
  rw [matMul_bottomProjector_right]
  by_cases hj : (j : ℕ) < r
  · rw [if_neg (not_not_intro hj)]
    exact (hWshape i j (Or.inr hj)).symm
  · rw [if_pos hj]

/-- Under the (17.22) block hypotheses, `I − J` absorbs the bottom
    projector on the right: `(I − J)·diag(0, I_{n−r}) = I − J`. -/
theorem matSub_id_J_mul_bottomProjector (n r : ℕ) (J : Fin n → Fin n → ℝ)
    (hJtop : ∀ i j : Fin n, (i : ℕ) < r → J i j = if i = j then 1 else 0)
    (hJcross : ∀ i j : Fin n, ¬(i : ℕ) < r → (j : ℕ) < r → J i j = 0) :
    matMul n (matSub_id n J) (bottomProjector n r) = matSub_id n J := by
  ext i j
  rw [matMul_bottomProjector_right]
  by_cases hj : (j : ℕ) < r
  · rw [if_neg (not_not_intro hj)]
    by_cases hi : (i : ℕ) < r
    · exact (matSub_id_J_top_row n r J hJtop hi j).symm
    · exact (matSub_id_J_cross n r J hJcross hi hj).symm
  · rw [if_pos hj]

/-- **Eq (17.24) at the printed data level** (Higham, Accuracy and Stability
    of Numerical Algorithms, 2nd ed., §17.4, eq (17.24)): the candidate
    `X·W·X⁻¹` built from the bottom-block inverse data satisfies the three
    index-one Drazin identities for `A := I − G`:
    `A·D = D·A`, `D·A·D = D`, and `A²·D = A`.  This certifies
    `drazinIG` as AN index-one Drazin inverse of `I − G` in the sense of
    the `IndexOneDrazinInverse` structure of `StationaryIteration.lean`,
    connecting the block-form route to the abstract Drazin wrappers there.

    Honest scope: uniqueness of the Drazin inverse (which makes the printed
    `(I−G)^D` well defined without reference to `P`) is not formalized;
    only the defining identities are proved from the block data. -/
theorem drazinIG_spec (n r : ℕ) (G J X X_inv W : Fin n → Fin n → ℝ)
    (hJtop : ∀ i j : Fin n, (i : ℕ) < r → J i j = if i = j then 1 else 0)
    (hJcross : ∀ i j : Fin n, ¬(i : ℕ) < r → (j : ℕ) < r → J i j = 0)
    (hWshape : ∀ i j : Fin n, (i : ℕ) < r ∨ (j : ℕ) < r → W i j = 0)
    (hW1 : matMul n (matSub_id n J) W = bottomProjector n r)
    (hW2 : matMul n W (matSub_id n J) = bottomProjector n r)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n G X) = J) :
    IndexOneDrazinInverse n (matSub_id n G) (drazinIG n X W X_inv) := by
  have hA : matSub_id n G = matMul n X (matMul n (matSub_id n J) X_inv) :=
    eq_17_23_block n G J X X_inv hXr hsim
  refine ⟨?_, ?_, ?_⟩
  · -- comm : (I−G)·D = D·(I−G)
    rw [hA]
    unfold drazinIG
    rw [conjugate_matMul n X X_inv (matSub_id n J) W hXl,
      conjugate_matMul n X X_inv W (matSub_id n J) hXl, hW1, hW2]
  · -- reflexive : D·((I−G)·D) = D
    rw [hA]
    unfold drazinIG
    rw [conjugate_matMul n X X_inv (matSub_id n J) W hXl, hW1,
      conjugate_matMul n X X_inv W (bottomProjector n r) hXl,
      W_mul_bottomProjector n r W hWshape]
  · -- index_one : ((I−G)·(I−G))·D = I−G
    rw [hA]
    unfold drazinIG
    rw [conjugate_matMul n X X_inv (matSub_id n J) (matSub_id n J) hXl,
      conjugate_matMul n X X_inv
        (matMul n (matSub_id n J) (matSub_id n J)) W hXl,
      matMul_assoc n (matSub_id n J) (matSub_id n J) W, hW1,
      matSub_id_J_mul_bottomProjector n r J hJtop hJcross]

-- ============================================================
-- §17.4  E. The projector E = (I−G)^D(I−G) is semiconvergentE
-- ============================================================

/-- The conjugated bottom projector is the accumulating projector `E` of
    the semiconvergent module: `X·diag(0, I_{n−r})·X⁻¹ = E`
    (Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
    §17.4, eqs (17.24)-(17.25) surroundings). -/
theorem conjugated_bottomProjector_eq_semiconvergentE (n r : ℕ)
    (X X_inv : Fin n → Fin n → ℝ) (hXr : IsRightInverse n X X_inv) :
    matMul n X (matMul n (bottomProjector n r) X_inv) =
      semiconvergentE n r X X_inv := by
  ext i j
  have hsplit : ∀ k : Fin n,
      matMul n (bottomProjector n r) X_inv k j =
        X_inv k j - matMul n (topProjector n r) X_inv k j := by
    intro k
    have hadd : matMul n (topProjector n r) X_inv k j +
        matMul n (bottomProjector n r) X_inv k j = X_inv k j := by
      calc matMul n (topProjector n r) X_inv k j +
            matMul n (bottomProjector n r) X_inv k j
          = (∑ l : Fin n, topProjector n r k l * X_inv l j) +
              ∑ l : Fin n, bottomProjector n r k l * X_inv l j := rfl
        _ = ∑ l : Fin n, (topProjector n r k l * X_inv l j +
              bottomProjector n r k l * X_inv l j) := by
            rw [← Finset.sum_add_distrib]
        _ = ∑ l : Fin n, idMatrix n k l * X_inv l j :=
            Finset.sum_congr rfl fun l _ => by
              rw [← add_mul, topProjector_add_bottomProjector]
        _ = X_inv k j := by
            have h := congrArg (fun T : Fin n → Fin n → ℝ => T k j)
              (matMul_id_left n X_inv)
            simpa [matMul] using h
    linarith
  calc matMul n X (matMul n (bottomProjector n r) X_inv) i j
      = ∑ k : Fin n, X i k * matMul n (bottomProjector n r) X_inv k j := rfl
    _ = ∑ k : Fin n, (X i k * X_inv k j -
          X i k * matMul n (topProjector n r) X_inv k j) :=
        Finset.sum_congr rfl fun k _ => by rw [hsplit k]; ring
    _ = (∑ k : Fin n, X i k * X_inv k j) -
          ∑ k : Fin n, X i k * matMul n (topProjector n r) X_inv k j := by
        rw [Finset.sum_sub_distrib]
    _ = idMatrix n i j - oneEigenProjector n r X X_inv i j := by
        rw [hXr i j]
        rfl
    _ = semiconvergentE n r X X_inv i j := rfl

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    p. 334 top: `(I−G)·(I−G)^D = E` — the range projector built from the
    Drazin inverse coincides with the semiconvergent module's accumulating
    projector `E = X·diag(0, I_{n−r})·X⁻¹`. -/
theorem matSub_id_G_mul_drazinIG_eq_semiconvergentE (n r : ℕ)
    (G J X X_inv W : Fin n → Fin n → ℝ)
    (hW1 : matMul n (matSub_id n J) W = bottomProjector n r)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n G X) = J) :
    matMul n (matSub_id n G) (drazinIG n X W X_inv) =
      semiconvergentE n r X X_inv := by
  rw [eq_17_23_block n G J X X_inv hXr hsim]
  unfold drazinIG
  rw [conjugate_matMul n X X_inv (matSub_id n J) W hXl, hW1,
    conjugated_bottomProjector_eq_semiconvergentE n r X X_inv hXr]

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    p. 334 top: `E = (I−G)^D(I−G)` — the book's definition of the range
    projector, equal to the semiconvergent module's `E`. -/
theorem drazinIG_mul_matSub_id_G_eq_semiconvergentE (n r : ℕ)
    (G J X X_inv W : Fin n → Fin n → ℝ)
    (hW2 : matMul n W (matSub_id n J) = bottomProjector n r)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n G X) = J) :
    matMul n (drazinIG n X W X_inv) (matSub_id n G) =
      semiconvergentE n r X X_inv := by
  rw [eq_17_23_block n G J X X_inv hXr hsim]
  unfold drazinIG
  rw [conjugate_matMul n X X_inv W (matSub_id n J) hXl, hW2,
    conjugated_bottomProjector_eq_semiconvergentE n r X X_inv hXr]

/-- Bridge between the two §17.4 routes in this repository: the abstract
    Drazin range projector of `StationaryIteration.lean`, instantiated at
    the block-form Drazin inverse `drazinIG`, IS the semiconvergent
    module's projector `E` (Higham, Accuracy and Stability of Numerical
    Algorithms, 2nd ed., §17.4, eqs (17.24)-(17.27)). -/
theorem stationaryDrazinRangeProjector_drazinIG_eq_semiconvergentE
    (n r : ℕ) (G J X X_inv W : Fin n → Fin n → ℝ)
    (hW1 : matMul n (matSub_id n J) W = bottomProjector n r)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n G X) = J) :
    stationaryDrazinRangeProjector n G (drazinIG n X W X_inv) =
      semiconvergentE n r X X_inv := by
  unfold stationaryDrazinRangeProjector
  exact matSub_id_G_mul_drazinIG_eq_semiconvergentE n r G J X X_inv W
    hW1 hXr hXl hsim

-- ============================================================
-- §17.4  F. Eq (17.25): lim Gᵐ = I − (I−G)^D(I−G)
-- ============================================================

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    eq (17.25), algebraic half: the printed limit expression
    `I − (I−G)^D(I−G)` is exactly the eigenvalue-1 projector
    `X·diag(I_r, 0)·X⁻¹` of the semiconvergent module. -/
theorem eq_17_25_limit (n r : ℕ) (G J X X_inv W : Fin n → Fin n → ℝ)
    (hW2 : matMul n W (matSub_id n J) = bottomProjector n r)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n G X) = J) :
    matSub_id n (matMul n (drazinIG n X W X_inv) (matSub_id n G)) =
      oneEigenProjector n r X X_inv := by
  rw [drazinIG_mul_matSub_id_G_eq_semiconvergentE n r G J X X_inv W
    hW2 hXr hXl hsim]
  exact matSub_id_semiconvergentE n r X X_inv

/-- **The literal eq (17.25)** (Higham, Accuracy and Stability of Numerical
    Algorithms, 2nd ed., §17.4, eq (17.25)): for an iteration matrix
    carrying the (17.22) block data with contraction certificate
    `‖Γ‖∞ ≤ q < 1` and the (17.24) bottom-block inverse data, the powers
    converge entrywise to the printed Drazin expression:
    `Gᵐ → I − (I−G)^D(I−G)`.  Composes `eq_17_25_limit` with the
    semiconvergence limit `matPow_G_tendsto_oneEigenProjector`. -/
theorem matPow_G_tendsto_limit_drazin (n r : ℕ)
    (G J X X_inv W : Fin n → Fin n → ℝ)
    (hJtop : ∀ i j : Fin n, (i : ℕ) < r → J i j = if i = j then 1 else 0)
    (hJcross : ∀ i j : Fin n, ¬(i : ℕ) < r → (j : ℕ) < r → J i j = 0)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hGamma : ∀ i : Fin n, ¬(i : ℕ) < r → ∑ j : Fin n, |J i j| ≤ q)
    (hW2 : matMul n W (matSub_id n J) = bottomProjector n r)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n G X) = J) :
    ∀ i j : Fin n,
      Filter.Tendsto (fun m => matPow n G m i j) Filter.atTop
        (nhds (matSub_id n
          (matMul n (drazinIG n X W X_inv) (matSub_id n G)) i j)) := by
  intro i j
  rw [eq_17_25_limit n r G J X X_inv W hW2 hXr hXl hsim]
  exact matPow_G_tendsto_oneEigenProjector n r G J X X_inv hJtop hJcross
    q hq0 hq1 hGamma hXr hXl hsim i j

-- ============================================================
-- §17.4  G. Eq (17.26): the stationary iteration limit
-- ============================================================

/-- **The literal eq (17.26)** (Higham, Accuracy and Stability of Numerical
    Algorithms, 2nd ed., §17.4, eq (17.26)): for a consistent singular
    system `Ax = b` and the exact stationary iteration
    `x_{m+1} = Gx_m + M⁻¹b` with semiconvergent `G` (the (17.22) block data
    with contraction certificate) and Drazin data (17.24), the iterates
    converge componentwise to the printed limit
    `lim x_m = (I − (I−G)^D(I−G))·x₀ + (I−G)^D M⁻¹ b`.

    Route: the (17.21) finite unrolling plus the p. 333 telescoping
    (`singular_stationary_iterate_consistent_split`) writes
    `x_{m+1} = G^{m+1}x₀ + (I − G^{m+1})x` for the consistency witness `x`;
    the limit `G^{m} → I − E` (eq (17.25)) and the identity
    `E·x = (I−G)^D(I−G)x = (I−G)^D M⁻¹ b` (consistency: `M⁻¹b = (I−G)x`,
    p. 333) produce exactly the printed right-hand side. -/
theorem eq_17_26_stationary_limit (n : ℕ)
    (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_seq : ℕ → Fin n → ℝ)
    (hIter : SourceComputedIteration n M N b x_seq (fun _ _ => 0))
    (r : ℕ) (J X X_inv W : Fin n → Fin n → ℝ)
    (hJtop : ∀ i j : Fin n, (i : ℕ) < r → J i j = if i = j then 1 else 0)
    (hJcross : ∀ i j : Fin n, ¬(i : ℕ) < r → (j : ℕ) < r → J i j = 0)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hGamma : ∀ i : Fin n, ¬(i : ℕ) < r → ∑ j : Fin n, |J i j| ≤ q)
    (hW2 : matMul n W (matSub_id n J) = bottomProjector n r)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n (iterMatrix n M_inv N) X) = J) :
    ∀ i : Fin n,
      Filter.Tendsto (fun m => x_seq m i) Filter.atTop
        (nhds (matMulVec n (matSub_id n (matMul n (drazinIG n X W X_inv)
            (matSub_id n (iterMatrix n M_inv N)))) (x_seq 0) i +
          matMulVec n (drazinIG n X W X_inv) (matMulVec n M_inv b) i)) := by
  intro i
  have hP := eq_17_25_limit n r (iterMatrix n M_inv N) J X X_inv W
    hW2 hXr hXl hsim
  -- powers applied to a fixed vector converge to the projector action
  have hvec : ∀ v : Fin n → ℝ,
      Filter.Tendsto
        (fun m => matMulVec n (matPow n (iterMatrix n M_inv N) (m + 1)) v i)
        Filter.atTop
        (nhds (matMulVec n (oneEigenProjector n r X X_inv) v i)) := by
    intro v
    have hentry := matPow_G_tendsto_oneEigenProjector n r
      (iterMatrix n M_inv N) J X X_inv hJtop hJcross q hq0 hq1 hGamma
      hXr hXl hsim
    have hshift : ∀ j : Fin n,
        Filter.Tendsto
          (fun m => matPow n (iterMatrix n M_inv N) (m + 1) i j)
          Filter.atTop
          (nhds (oneEigenProjector n r X X_inv i j)) := by
      intro j
      exact (Filter.tendsto_add_atTop_iff_nat 1).mpr (hentry i j)
    have hsum : Filter.Tendsto
        (fun m => ∑ j : Fin n,
          matPow n (iterMatrix n M_inv N) (m + 1) i j * v j)
        Filter.atTop
        (nhds (∑ j : Fin n, oneEigenProjector n r X X_inv i j * v j)) :=
      tendsto_finset_sum _ (fun j _ => (hshift j).mul_const (v j))
    exact hsum
  -- the consistent split of the exact iterates
  have hsplit := singular_stationary_iterate_consistent_split n A M N M_inv
    hS b x hAx x_seq hIter
  have hfun : (fun m => x_seq (m + 1) i) =
      (fun m => matMulVec n (matPow n (iterMatrix n M_inv N) (m + 1))
          (x_seq 0) i +
        (x i - matMulVec n (matPow n (iterMatrix n M_inv N) (m + 1)) x i)) :=
    funext fun m => hsplit m i
  have hlim : Filter.Tendsto (fun m => x_seq (m + 1) i) Filter.atTop
      (nhds (matMulVec n (oneEigenProjector n r X X_inv) (x_seq 0) i +
        (x i - matMulVec n (oneEigenProjector n r X X_inv) x i))) := by
    rw [hfun]
    exact (hvec (x_seq 0)).add (tendsto_const_nhds.sub (hvec x))
  -- identify the limit with the printed Drazin expression
  have hsecond : matMulVec n (drazinIG n X W X_inv)
      (matMulVec n M_inv b) i =
      x i - matMulVec n (oneEigenProjector n r X X_inv) x i := by
    have hsrc : matMulVec n M_inv b =
        matMulVec n (matSub_id n (iterMatrix n M_inv N)) x :=
      singular_consistent_source_term_eq_I_sub_G n A M N M_inv hS b x hAx
    calc matMulVec n (drazinIG n X W X_inv) (matMulVec n M_inv b) i
        = matMulVec n (drazinIG n X W X_inv)
            (matMulVec n (matSub_id n (iterMatrix n M_inv N)) x) i := by
          rw [hsrc]
      _ = matMulVec n (matMul n (drazinIG n X W X_inv)
            (matSub_id n (iterMatrix n M_inv N))) x i :=
          (matMulVec_matMul n (drazinIG n X W X_inv)
            (matSub_id n (iterMatrix n M_inv N)) x i).symm
      _ = matMulVec n (semiconvergentE n r X X_inv) x i := by
          rw [drazinIG_mul_matSub_id_G_eq_semiconvergentE n r
            (iterMatrix n M_inv N) J X X_inv W hW2 hXr hXl hsim]
      _ = x i - matMulVec n (oneEigenProjector n r X X_inv) x i := by
          show (∑ j : Fin n, semiconvergentE n r X X_inv i j * x j) =
            x i - ∑ j : Fin n, oneEigenProjector n r X X_inv i j * x j
          calc ∑ j : Fin n, semiconvergentE n r X X_inv i j * x j
              = ∑ j : Fin n, (idMatrix n i j * x j -
                  oneEigenProjector n r X X_inv i j * x j) :=
                Finset.sum_congr rfl fun j _ => by
                  show semiconvergentE n r X X_inv i j * x j = _
                  unfold semiconvergentE
                  ring
            _ = (∑ j : Fin n, idMatrix n i j * x j) -
                  ∑ j : Fin n, oneEigenProjector n r X X_inv i j * x j := by
                rw [Finset.sum_sub_distrib]
            _ = x i - ∑ j : Fin n,
                  oneEigenProjector n r X X_inv i j * x j := by
                have h := congrFun (matMulVec_id n x) i
                have h' : ∑ j : Fin n, idMatrix n i j * x j = x i := by
                  simpa [matMulVec] using h
                rw [h']
  have hL : matMulVec n (matSub_id n (matMul n (drazinIG n X W X_inv)
        (matSub_id n (iterMatrix n M_inv N)))) (x_seq 0) i +
      matMulVec n (drazinIG n X W X_inv) (matMulVec n M_inv b) i =
      matMulVec n (oneEigenProjector n r X X_inv) (x_seq 0) i +
        (x i - matMulVec n (oneEigenProjector n r X X_inv) x i) := by
    rw [hP, hsecond]
  rw [hL]
  exact (Filter.tendsto_add_atTop_iff_nat 1).mp hlim

-- ============================================================
-- §17.4  H. Eq (17.30): GⁱE = X·diag(0, Γⁱ)·X⁻¹ = (GE)ⁱ
-- ============================================================

/-- The bottom-left block of every power of the (17.22) block form
    vanishes. -/
theorem matPow_J_cross (n r : ℕ) (J : Fin n → Fin n → ℝ)
    (hJcross : ∀ i j : Fin n, ¬(i : ℕ) < r → (j : ℕ) < r → J i j = 0)
    (m : ℕ) :
    ∀ i j : Fin n, ¬(i : ℕ) < r → (j : ℕ) < r → matPow n J m i j = 0 := by
  induction m with
  | zero =>
      intro i j hi hj
      rw [matPow_zero]
      unfold idMatrix
      exact if_neg (fun h : i = j => hi (by rw [h]; exact hj))
  | succ m ih =>
      intro i j hi hj
      rw [matPow_succ]
      calc matMul n J (matPow n J m) i j
          = ∑ k : Fin n, J i k * matPow n J m k j := rfl
        _ = 0 := Finset.sum_eq_zero fun k _ => by
            by_cases hk : (k : ℕ) < r
            · rw [hJcross i k hi hk, zero_mul]
            · rw [ih k j hk hj, mul_zero]

/-- The bottom projector commutes with every power of the (17.22) block
    form: both products are `diag(0, Γᵐ)` (Higham, Accuracy and Stability
    of Numerical Algorithms, 2nd ed., §17.4, eq (17.30) surroundings). -/
theorem bottomProjector_matPow_J_comm (n r : ℕ) (J : Fin n → Fin n → ℝ)
    (hJtop : ∀ i j : Fin n, (i : ℕ) < r → J i j = if i = j then 1 else 0)
    (hJcross : ∀ i j : Fin n, ¬(i : ℕ) < r → (j : ℕ) < r → J i j = 0)
    (m : ℕ) :
    matMul n (bottomProjector n r) (matPow n J m) =
      matMul n (matPow n J m) (bottomProjector n r) := by
  ext i j
  rw [matMul_bottomProjector_left, matMul_bottomProjector_right]
  by_cases hi : (i : ℕ) < r
  · rw [if_neg (not_not_intro hi)]
    by_cases hj : (j : ℕ) < r
    · rw [if_neg (not_not_intro hj)]
    · rw [if_pos hj, matPow_J_top_entry n r J hJtop m i j hi,
        if_neg (fun h : i = j => hj (h ▸ hi))]
  · rw [if_pos hi]
    by_cases hj : (j : ℕ) < r
    · rw [if_neg (not_not_intro hj)]
      exact matPow_J_cross n r J hJcross m i j hi hj
    · rw [if_pos hj]

/-- **Eq (17.30), block form** (Higham, Accuracy and Stability of Numerical
    Algorithms, 2nd ed., §17.4, eq (17.30)): `GⁱE = X·diag(0, Γⁱ)·X⁻¹`,
    with `diag(0, Γⁱ)` realized as `Jⁱ·diag(0, I_{n−r})` from the block
    data.  Holds for every `i ≥ 0` in this form. -/
theorem eq_17_30_block (n r : ℕ) (G J X X_inv : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n G X) = J) (i : ℕ) :
    matMul n (matPow n G i) (semiconvergentE n r X X_inv) =
      matMul n X (matMul n
        (matMul n (matPow n J i) (bottomProjector n r)) X_inv) := by
  rw [matPow_similarity n G X X_inv J hXr hXl hsim i,
    ← conjugated_bottomProjector_eq_semiconvergentE n r X X_inv hXr]
  exact conjugate_matMul n X X_inv (matPow n J i) (bottomProjector n r) hXl

/-- **Eq (17.30), power form** (Higham, Accuracy and Stability of Numerical
    Algorithms, 2nd ed., §17.4, eq (17.30)): `GⁱE = (GE)ⁱ` for `i ≥ 1`
    (stated with `i + 1` so the positivity is structural).  The proof uses
    only that `E` commutes with `G` and is idempotent — both consequences
    of the (17.22) block data. -/
theorem eq_17_30_pow (n r : ℕ) (G J X X_inv : Fin n → Fin n → ℝ)
    (hJtop : ∀ i j : Fin n, (i : ℕ) < r → J i j = if i = j then 1 else 0)
    (hJcross : ∀ i j : Fin n, ¬(i : ℕ) < r → (j : ℕ) < r → J i j = 0)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n G X) = J) (i : ℕ) :
    matPow n (matMul n G (semiconvergentE n r X X_inv)) (i + 1) =
      matMul n (matPow n G (i + 1)) (semiconvergentE n r X X_inv) := by
  have hE : matMul n X (matMul n (bottomProjector n r) X_inv) =
      semiconvergentE n r X X_inv :=
    conjugated_bottomProjector_eq_semiconvergentE n r X X_inv hXr
  have hG : G = matMul n X (matMul n J X_inv) :=
    eq_conjugate_of_similarity n G X X_inv J hXr hsim
  have hJbP : matMul n J (bottomProjector n r) =
      matMul n (bottomProjector n r) J := by
    have h := bottomProjector_matPow_J_comm n r J hJtop hJcross 1
    rw [matPow_one] at h
    exact h.symm
  have hcomm : matMul n G (semiconvergentE n r X X_inv) =
      matMul n (semiconvergentE n r X X_inv) G := by
    rw [← hE, hG,
      conjugate_matMul n X X_inv J (bottomProjector n r) hXl,
      conjugate_matMul n X X_inv (bottomProjector n r) J hXl, hJbP]
  have hidem : matMul n (semiconvergentE n r X X_inv)
      (semiconvergentE n r X X_inv) = semiconvergentE n r X X_inv := by
    rw [← hE,
      conjugate_matMul n X X_inv (bottomProjector n r)
        (bottomProjector n r) hXl,
      bottomProjector_idempotent]
  induction i with
  | zero =>
      show matPow n (matMul n G (semiconvergentE n r X X_inv)) 1 =
        matMul n (matPow n G 1) (semiconvergentE n r X X_inv)
      rw [matPow_one, matPow_one]
  | succ i ih =>
      calc matPow n (matMul n G (semiconvergentE n r X X_inv)) (i + 1 + 1)
          = matMul n (matMul n G (semiconvergentE n r X X_inv))
              (matPow n (matMul n G (semiconvergentE n r X X_inv))
                (i + 1)) :=
            matPow_succ n _ (i + 1)
        _ = matMul n (matMul n G (semiconvergentE n r X X_inv))
              (matMul n (matPow n G (i + 1))
                (semiconvergentE n r X X_inv)) := by rw [ih]
        _ = matMul n G (matMul n (semiconvergentE n r X X_inv)
              (matMul n (matPow n G (i + 1))
                (semiconvergentE n r X X_inv))) :=
            matMul_assoc n G (semiconvergentE n r X X_inv) _
        _ = matMul n G (matMul n (matMul n (semiconvergentE n r X X_inv)
              (matPow n G (i + 1))) (semiconvergentE n r X X_inv)) := by
            rw [← matMul_assoc n (semiconvergentE n r X X_inv)
              (matPow n G (i + 1)) (semiconvergentE n r X X_inv)]
        _ = matMul n G (matMul n (matMul n (matPow n G (i + 1))
              (semiconvergentE n r X X_inv))
              (semiconvergentE n r X X_inv)) := by
            rw [← matPow_comm_of_matMul_comm n G
              (semiconvergentE n r X X_inv) hcomm (i + 1)]
        _ = matMul n G (matMul n (matPow n G (i + 1))
              (matMul n (semiconvergentE n r X X_inv)
                (semiconvergentE n r X X_inv))) := by
            rw [matMul_assoc n (matPow n G (i + 1))
              (semiconvergentE n r X X_inv) (semiconvergentE n r X X_inv)]
        _ = matMul n G (matMul n (matPow n G (i + 1))
              (semiconvergentE n r X X_inv)) := by rw [hidem]
        _ = matMul n (matMul n G (matPow n G (i + 1)))
              (semiconvergentE n r X X_inv) :=
            (matMul_assoc n G (matPow n G (i + 1))
              (semiconvergentE n r X X_inv)).symm
        _ = matMul n (matPow n G (i + 1 + 1))
              (semiconvergentE n r X X_inv) := by
            rw [← matPow_succ n G (i + 1)]

-- ============================================================
-- §17.4  I. Geometric decay and summability of ‖GⁱEM⁻¹‖∞
-- ============================================================

/-- The block factor `diag(0, Γⁱ) = Jⁱ·diag(0, I_{n−r})` of eq (17.30)
    decays geometrically in the ∞-norm under the row-sum contraction
    certificate: `‖Jⁱ·diag(0, I_{n−r})‖∞ ≤ qⁱ`. -/
theorem infNorm_matPow_J_bottomProjector_le (n r : ℕ)
    (J : Fin n → Fin n → ℝ)
    (hJtop : ∀ i j : Fin n, (i : ℕ) < r → J i j = if i = j then 1 else 0)
    (hJcross : ∀ i j : Fin n, ¬(i : ℕ) < r → (j : ℕ) < r → J i j = 0)
    (q : ℝ) (hq0 : 0 ≤ q)
    (hGamma : ∀ i : Fin n, ¬(i : ℕ) < r → ∑ j : Fin n, |J i j| ≤ q)
    (i : ℕ) :
    infNorm (matMul n (matPow n J i) (bottomProjector n r)) ≤ q ^ i := by
  apply infNorm_le_of_row_sum_le
  · intro k
    by_cases hk : (k : ℕ) < r
    · have hz : ∀ j : Fin n,
          matMul n (matPow n J i) (bottomProjector n r) k j = 0 := by
        intro j
        rw [matMul_bottomProjector_right]
        by_cases hj : (j : ℕ) < r
        · rw [if_neg (not_not_intro hj)]
        · rw [if_pos hj, matPow_J_top_entry n r J hJtop i k j hk]
          exact if_neg (fun h : k = j => hj (h ▸ hk))
      calc ∑ j : Fin n, |matMul n (matPow n J i) (bottomProjector n r) k j|
          = ∑ j : Fin n, (0 : ℝ) :=
            Finset.sum_congr rfl fun j _ => by rw [hz j, abs_zero]
        _ = 0 := Finset.sum_const_zero
        _ ≤ q ^ i := pow_nonneg hq0 i
    · calc ∑ j : Fin n, |matMul n (matPow n J i) (bottomProjector n r) k j|
          ≤ ∑ j : Fin n, |matPow n J i k j| := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [matMul_bottomProjector_right]
            by_cases hj : (j : ℕ) < r
            · rw [if_neg (not_not_intro hj), abs_zero]
              exact abs_nonneg _
            · rw [if_pos hj]
        _ ≤ q ^ i := matPow_J_bottom_row_sum n r J hJcross q hq0 hGamma i k hk
  · exact pow_nonneg hq0 i

/-- Geometric ∞-norm majorant for the terms of the infinite sum in
    eqs (17.31)-(17.32): `‖GⁱEM⁻¹‖∞ ≤ ‖X‖∞‖X⁻¹‖∞‖M⁻¹‖∞ · qⁱ`
    (Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
    §17.4, eq (17.30) and the convergence remark before (17.31)). -/
theorem infNorm_GiE_Minv_le (n r : ℕ) (hn : 0 < n)
    (G J X X_inv M_inv : Fin n → Fin n → ℝ)
    (hJtop : ∀ i j : Fin n, (i : ℕ) < r → J i j = if i = j then 1 else 0)
    (hJcross : ∀ i j : Fin n, ¬(i : ℕ) < r → (j : ℕ) < r → J i j = 0)
    (q : ℝ) (hq0 : 0 ≤ q)
    (hGamma : ∀ i : Fin n, ¬(i : ℕ) < r → ∑ j : Fin n, |J i j| ≤ q)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n G X) = J) (i : ℕ) :
    infNorm (matMul n (matMul n (matPow n G i)
        (semiconvergentE n r X X_inv)) M_inv) ≤
      infNorm X * infNorm X_inv * infNorm M_inv * q ^ i := by
  have hGE := eq_17_30_block n r G J X X_inv hXr hXl hsim i
  calc infNorm (matMul n (matMul n (matPow n G i)
        (semiconvergentE n r X X_inv)) M_inv)
      ≤ infNorm (matMul n (matPow n G i) (semiconvergentE n r X X_inv)) *
          infNorm M_inv := infNorm_matMul_le hn _ _
    _ = infNorm (matMul n X (matMul n
          (matMul n (matPow n J i) (bottomProjector n r)) X_inv)) *
          infNorm M_inv := by rw [hGE]
    _ ≤ (infNorm X * infNorm (matMul n
          (matMul n (matPow n J i) (bottomProjector n r)) X_inv)) *
          infNorm M_inv :=
        mul_le_mul_of_nonneg_right (infNorm_matMul_le hn _ _)
          (infNorm_nonneg _)
    _ ≤ (infNorm X * (infNorm (matMul n (matPow n J i)
          (bottomProjector n r)) * infNorm X_inv)) * infNorm M_inv := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (infNorm_matMul_le hn _ _)
            (infNorm_nonneg X)) (infNorm_nonneg _)
    _ ≤ (infNorm X * (q ^ i * infNorm X_inv)) * infNorm M_inv := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right
              (infNorm_matPow_J_bottomProjector_le n r J hJtop hJcross
                q hq0 hGamma i)
              (infNorm_nonneg X_inv))
            (infNorm_nonneg X)) (infNorm_nonneg _)
    _ = infNorm X * infNorm X_inv * infNorm M_inv * q ^ i := by ring

/-- **Summability of the (17.31) series** (Higham, Accuracy and Stability
    of Numerical Algorithms, 2nd ed., §17.4, remark after eq (17.29) and
    eq (17.30)): under the (17.22) block data with contraction certificate
    `‖Γ‖∞ ≤ q < 1`, the norms `‖GⁱEM⁻¹‖∞` are summable — the convergence
    of the infinite sum in eq (17.31), assured in the source by
    (17.22)-(17.24) via Problem 17.1. -/
theorem summable_infNorm_GiE_Minv (n r : ℕ) (hn : 0 < n)
    (G J X X_inv M_inv : Fin n → Fin n → ℝ)
    (hJtop : ∀ i j : Fin n, (i : ℕ) < r → J i j = if i = j then 1 else 0)
    (hJcross : ∀ i j : Fin n, ¬(i : ℕ) < r → (j : ℕ) < r → J i j = 0)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hGamma : ∀ i : Fin n, ¬(i : ℕ) < r → ∑ j : Fin n, |J i j| ≤ q)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n G X) = J) :
    Summable (fun i : ℕ => infNorm (matMul n (matMul n (matPow n G i)
      (semiconvergentE n r X X_inv)) M_inv)) :=
  Summable.of_nonneg_of_le (fun _ => infNorm_nonneg _)
    (fun i => infNorm_GiE_Minv_le n r hn G J X X_inv M_inv hJtop hJcross
      q hq0 hGamma hXr hXl hsim i)
    ((summable_geometric_of_lt_one hq0 hq1).mul_left
      (infNorm X * infNorm X_inv * infNorm M_inv))

/-- The infinite sum of eq (17.31) is bounded by the geometric value
    `‖X‖∞‖X⁻¹‖∞‖M⁻¹‖∞ (1 − q)⁻¹` — an ∞-norm certificate analogue of the
    printed diagonal-case remark
    `Σ' ‖GⁱEM⁻¹‖∞ ≤ κ∞(P)‖M⁻¹‖∞ / (1 − ρ(Γ))` after eq (17.31). -/
theorem tsum_infNorm_GiE_Minv_le (n r : ℕ) (hn : 0 < n)
    (G J X X_inv M_inv : Fin n → Fin n → ℝ)
    (hJtop : ∀ i j : Fin n, (i : ℕ) < r → J i j = if i = j then 1 else 0)
    (hJcross : ∀ i j : Fin n, ¬(i : ℕ) < r → (j : ℕ) < r → J i j = 0)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hGamma : ∀ i : Fin n, ¬(i : ℕ) < r → ∑ j : Fin n, |J i j| ≤ q)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n G X) = J) :
    (∑' i : ℕ, infNorm (matMul n (matMul n (matPow n G i)
        (semiconvergentE n r X X_inv)) M_inv)) ≤
      infNorm X * infNorm X_inv * infNorm M_inv * (1 - q)⁻¹ :=
  calc (∑' i : ℕ, infNorm (matMul n (matMul n (matPow n G i)
        (semiconvergentE n r X X_inv)) M_inv))
      ≤ ∑' i : ℕ, infNorm X * infNorm X_inv * infNorm M_inv * q ^ i :=
        Summable.tsum_le_tsum
          (fun i => infNorm_GiE_Minv_le n r hn G J X X_inv M_inv hJtop
            hJcross q hq0 hGamma hXr hXl hsim i)
          (summable_infNorm_GiE_Minv n r hn G J X X_inv M_inv hJtop
            hJcross q hq0 hq1 hGamma hXr hXl hsim)
          ((summable_geometric_of_lt_one hq0 hq1).mul_left
            (infNorm X * infNorm X_inv * infNorm M_inv))
    _ = infNorm X * infNorm X_inv * infNorm M_inv * (1 - q)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]

/-- Every finite (17.29) coefficient is dominated by the (17.31) infinite
    sum: `Σ_{k=0}^m ‖GᵏEM⁻¹‖∞ ≤ Σ'_{i=0}^∞ ‖GⁱEM⁻¹‖∞`. -/
theorem singularErrorSourceNormSum_le_tsum (n r : ℕ) (hn : 0 < n)
    (G J X X_inv M_inv : Fin n → Fin n → ℝ)
    (hJtop : ∀ i j : Fin n, (i : ℕ) < r → J i j = if i = j then 1 else 0)
    (hJcross : ∀ i j : Fin n, ¬(i : ℕ) < r → (j : ℕ) < r → J i j = 0)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hGamma : ∀ i : Fin n, ¬(i : ℕ) < r → ∑ j : Fin n, |J i j| ≤ q)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n G X) = J) (m : ℕ) :
    singularErrorSourceNormSum n G (semiconvergentE n r X X_inv) M_inv m ≤
      ∑' i : ℕ, infNorm (matMul n (matMul n (matPow n G i)
        (semiconvergentE n r X X_inv)) M_inv) := by
  unfold singularErrorSourceNormSum
  exact Summable.sum_le_tsum (Finset.range (m + 1))
    (fun _ _ => infNorm_nonneg _)
    (summable_infNorm_GiE_Minv n r hn G J X X_inv M_inv hJtop hJcross
      q hq0 hq1 hGamma hXr hXl hsim)

-- ============================================================
-- §17.4  J. Eq (17.31): the all-m normwise forward bound
-- ============================================================

/-- **The literal eq (17.31)** (Higham, Accuracy and Stability of Numerical
    Algorithms, 2nd ed., §17.4, eq (17.31)): for every horizon `m`
    simultaneously,
    `‖e_{m+1}‖∞ ≤ ‖G^{m+1}e₀‖∞ + c_n u(1+γ_x)(‖M‖∞+‖N‖∞)‖x‖∞ ·
       { Σ'_{i=0}^∞ ‖GⁱEM⁻¹‖∞ + (m+1)‖(I−E)M⁻¹‖∞ }`,
    with the infinite-sum constant of the printed statement (the finite
    (17.29) coefficient `Σ_{i=0}^m` is dominated by the `tsum` via
    `singularErrorSourceNormSum_le_tsum`).  In this repository's naming the
    book's `E` is `semiconvergentE` and the book's `I−E` is
    `oneEigenProjector`.

    Hypotheses: the (17.22) block data with row-sum contraction certificate
    for `G = M⁻¹N`, the local-error model (17.2) via `LocalErrorBound`, and
    the iterate-growth constant `γ_x` of (17.7) via
    `NormwiseIterateGrowthBound` — exactly the ingredients cited in the
    printed derivation ("Using inequality (17.2) and the definition of
    `γ_x` in (17.7)"). -/
theorem eq_17_31_normwise_bound (n : ℕ) (hn : 0 < n)
    (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ))
    (hIter : SourceComputedIteration n M N b x_hat ξ)
    (r : ℕ) (J X X_inv : Fin n → Fin n → ℝ)
    (hJtop : ∀ i j : Fin n, (i : ℕ) < r → J i j = if i = j then 1 else 0)
    (hJcross : ∀ i j : Fin n, ¬(i : ℕ) < r → (j : ℕ) < r → J i j = 0)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hGamma : ∀ i : Fin n, ¬(i : ℕ) < r → ∑ j : Fin n, |J i j| ≤ q)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n (iterMatrix n M_inv N) X) = J)
    (cn_u gamma_x : ℝ) (hcn : 0 ≤ cn_u) (hgamma : 0 ≤ gamma_x)
    (hx_bound : NormwiseIterateGrowthBound n x x_hat gamma_x)
    (hLocal : LocalErrorBound n M N b x_hat ξ cn_u)
    (m : ℕ) :
    infNormVec (fun i => x i - x_hat (m + 1) i) ≤
      infNormVec (matMulVec n (matPow n (iterMatrix n M_inv N) (m + 1))
        (fun j => x j - x_hat 0 j)) +
      cn_u * (1 + gamma_x) * (infNorm M + infNorm N) * infNormVec x *
        ((∑' i : ℕ, infNorm (matMul n (matMul n
            (matPow n (iterMatrix n M_inv N) i)
            (semiconvergentE n r X X_inv)) M_inv)) +
          ((m : ℝ) + 1) * infNorm (matMul n
            (oneEigenProjector n r X X_inv) M_inv)) := by
  have hAx' : ∀ i, ∑ j : Fin n, (M i j - N i j) * x j = b i := by
    intro i
    calc ∑ j : Fin n, (M i j - N i j) * x j
        = ∑ j : Fin n, A i j * x j :=
          Finset.sum_congr rfl fun j _ => by rw [hS.splitting i j]
      _ = b i := hAx i
  -- the uniform local-error norm bound μ of the printed derivation
  have hμ0 : 0 ≤ cn_u * (1 + gamma_x) * (infNorm M + infNorm N) *
      infNormVec x :=
    mul_nonneg
      (mul_nonneg (mul_nonneg hcn (by linarith))
        (add_nonneg (infNorm_nonneg M) (infNorm_nonneg N)))
      (infNormVec_nonneg x)
  have hξ : ∀ t : ℕ, infNormVec (ξ t) ≤
      cn_u * (1 + gamma_x) * (infNorm M + infNorm N) * infNormVec x :=
    local_error_normwise_simplified n M N b x hAx' x_hat ξ cn_u gamma_x
      hcn hgamma hx_bound hLocal
  -- finite (17.27) split with the semiconvergent projector
  have hsplit := singular_error_split_semiconvergent n A M N M_inv hS b x
    hAx x_hat ξ hIter r J X X_inv hJtop hJcross q hq0 hq1 hGamma
    hXr hXl hsim m
  -- S_m term: finite (17.29) bound composed with the tsum domination
  have hT2 : infNormVec (singularErrorSourceTerm n (iterMatrix n M_inv N)
      (semiconvergentE n r X X_inv) M_inv ξ m) ≤
      cn_u * (1 + gamma_x) * (infNorm M + infNorm N) * infNormVec x *
        singularErrorSourceNormSum n (iterMatrix n M_inv N)
          (semiconvergentE n r X X_inv) M_inv m :=
    singularErrorSourceTerm_norm_bound n hn (iterMatrix n M_inv N)
      (semiconvergentE n r X X_inv) M_inv ξ _ hμ0 hξ m
  have hT2' : infNormVec (singularErrorSourceTerm n (iterMatrix n M_inv N)
      (semiconvergentE n r X X_inv) M_inv ξ m) ≤
      cn_u * (1 + gamma_x) * (infNorm M + infNorm N) * infNormVec x *
        (∑' i : ℕ, infNorm (matMul n (matMul n
          (matPow n (iterMatrix n M_inv N) i)
          (semiconvergentE n r X X_inv)) M_inv)) :=
    hT2.trans (mul_le_mul_of_nonneg_left
      (singularErrorSourceNormSum_le_tsum n r hn (iterMatrix n M_inv N)
        J X X_inv M_inv hJtop hJcross q hq0 hq1 hGamma hXr hXl hsim m)
      hμ0)
  -- accumulated (I−E)M⁻¹ term
  have hs_bound : infNormVec
      (fun j => ∑ k ∈ Finset.range (m + 1), ξ (m - k) j) ≤
      ((m : ℝ) + 1) * (cn_u * (1 + gamma_x) * (infNorm M + infNorm N) *
        infNormVec x) := by
    apply infNormVec_le_of_abs_le
    · intro j
      calc |∑ k ∈ Finset.range (m + 1), ξ (m - k) j|
          ≤ ∑ k ∈ Finset.range (m + 1), |ξ (m - k) j| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k ∈ Finset.range (m + 1),
              cn_u * (1 + gamma_x) * (infNorm M + infNorm N) *
                infNormVec x :=
            Finset.sum_le_sum fun k _ =>
              (abs_le_infNormVec (ξ (m - k)) j).trans (hξ (m - k))
        _ = ((m : ℝ) + 1) * (cn_u * (1 + gamma_x) *
              (infNorm M + infNorm N) * infNormVec x) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
    · exact mul_nonneg (by positivity) hμ0
  have hT3 : infNormVec (matMulVec n (oneEigenProjector n r X X_inv)
      (matMulVec n M_inv
        (fun j => ∑ k ∈ Finset.range (m + 1), ξ (m - k) j))) ≤
      infNorm (matMul n (oneEigenProjector n r X X_inv) M_inv) *
        (((m : ℝ) + 1) * (cn_u * (1 + gamma_x) *
          (infNorm M + infNorm N) * infNormVec x)) := by
    have hfun : matMulVec n (oneEigenProjector n r X X_inv)
        (matMulVec n M_inv
          (fun j => ∑ k ∈ Finset.range (m + 1), ξ (m - k) j)) =
        matMulVec n (matMul n (oneEigenProjector n r X X_inv) M_inv)
          (fun j => ∑ k ∈ Finset.range (m + 1), ξ (m - k) j) :=
      funext fun i => (matMulVec_matMul n (oneEigenProjector n r X X_inv)
        M_inv (fun j => ∑ k ∈ Finset.range (m + 1), ξ (m - k) j) i).symm
    rw [hfun]
    calc infNormVec (matMulVec n
          (matMul n (oneEigenProjector n r X X_inv) M_inv)
          (fun j => ∑ k ∈ Finset.range (m + 1), ξ (m - k) j))
        ≤ infNorm (matMul n (oneEigenProjector n r X X_inv) M_inv) *
            infNormVec (fun j => ∑ k ∈ Finset.range (m + 1), ξ (m - k) j) :=
          infNormVec_matMulVec_le hn _ _
      _ ≤ infNorm (matMul n (oneEigenProjector n r X X_inv) M_inv) *
            (((m : ℝ) + 1) * (cn_u * (1 + gamma_x) *
              (infNorm M + infNorm N) * infNormVec x)) :=
          mul_le_mul_of_nonneg_left hs_bound (infNorm_nonneg _)
  -- assemble
  have htsum0 : 0 ≤ ∑' i : ℕ, infNorm (matMul n (matMul n
      (matPow n (iterMatrix n M_inv N) i)
      (semiconvergentE n r X X_inv)) M_inv) :=
    tsum_nonneg fun _ => infNorm_nonneg _
  apply infNormVec_le_of_abs_le
  · intro i
    show |x i - x_hat (m + 1) i| ≤ _
    have habs : |x i - x_hat (m + 1) i| ≤
        |matMulVec n (matPow n (iterMatrix n M_inv N) (m + 1))
          (fun j => x j - x_hat 0 j) i| +
        |singularErrorSourceTerm n (iterMatrix n M_inv N)
          (semiconvergentE n r X X_inv) M_inv ξ m i| +
        |matMulVec n (oneEigenProjector n r X X_inv)
          (matMulVec n M_inv
            (fun j => ∑ k ∈ Finset.range (m + 1), ξ (m - k) j)) i| := by
      rw [hsplit i]
      calc |matMulVec n (matPow n (iterMatrix n M_inv N) (m + 1))
            (fun j => x j - x_hat 0 j) i +
          singularErrorSourceTerm n (iterMatrix n M_inv N)
            (semiconvergentE n r X X_inv) M_inv ξ m i +
          matMulVec n (oneEigenProjector n r X X_inv)
            (matMulVec n M_inv
              (fun j => ∑ k ∈ Finset.range (m + 1), ξ (m - k) j)) i|
          ≤ |matMulVec n (matPow n (iterMatrix n M_inv N) (m + 1))
              (fun j => x j - x_hat 0 j) i +
            singularErrorSourceTerm n (iterMatrix n M_inv N)
              (semiconvergentE n r X X_inv) M_inv ξ m i| +
            |matMulVec n (oneEigenProjector n r X X_inv)
              (matMulVec n M_inv
                (fun j => ∑ k ∈ Finset.range (m + 1), ξ (m - k) j)) i| :=
            abs_add_le _ _
        _ ≤ _ := add_le_add (abs_add_le _ _) le_rfl
    have h1 : |matMulVec n (matPow n (iterMatrix n M_inv N) (m + 1))
        (fun j => x j - x_hat 0 j) i| ≤
        infNormVec (matMulVec n (matPow n (iterMatrix n M_inv N) (m + 1))
          (fun j => x j - x_hat 0 j)) :=
      abs_le_infNormVec _ i
    have h2 : |singularErrorSourceTerm n (iterMatrix n M_inv N)
        (semiconvergentE n r X X_inv) M_inv ξ m i| ≤
        cn_u * (1 + gamma_x) * (infNorm M + infNorm N) * infNormVec x *
          (∑' i : ℕ, infNorm (matMul n (matMul n
            (matPow n (iterMatrix n M_inv N) i)
            (semiconvergentE n r X X_inv)) M_inv)) :=
      (abs_le_infNormVec _ i).trans hT2'
    have h3 : |matMulVec n (oneEigenProjector n r X X_inv)
        (matMulVec n M_inv
          (fun j => ∑ k ∈ Finset.range (m + 1), ξ (m - k) j)) i| ≤
        infNorm (matMul n (oneEigenProjector n r X X_inv) M_inv) *
          (((m : ℝ) + 1) * (cn_u * (1 + gamma_x) *
            (infNorm M + infNorm N) * infNormVec x)) :=
      (abs_le_infNormVec _ i).trans hT3
    have hring : infNormVec (matMulVec n
          (matPow n (iterMatrix n M_inv N) (m + 1))
          (fun j => x j - x_hat 0 j)) +
        cn_u * (1 + gamma_x) * (infNorm M + infNorm N) * infNormVec x *
          (∑' i : ℕ, infNorm (matMul n (matMul n
            (matPow n (iterMatrix n M_inv N) i)
            (semiconvergentE n r X X_inv)) M_inv)) +
        infNorm (matMul n (oneEigenProjector n r X X_inv) M_inv) *
          (((m : ℝ) + 1) * (cn_u * (1 + gamma_x) *
            (infNorm M + infNorm N) * infNormVec x)) =
        infNormVec (matMulVec n (matPow n (iterMatrix n M_inv N) (m + 1))
          (fun j => x j - x_hat 0 j)) +
        cn_u * (1 + gamma_x) * (infNorm M + infNorm N) * infNormVec x *
          ((∑' i : ℕ, infNorm (matMul n (matMul n
              (matPow n (iterMatrix n M_inv N) i)
              (semiconvergentE n r X X_inv)) M_inv)) +
            ((m : ℝ) + 1) * infNorm (matMul n
              (oneEigenProjector n r X X_inv) M_inv)) := by ring
    calc |x i - x_hat (m + 1) i|
        ≤ |matMulVec n (matPow n (iterMatrix n M_inv N) (m + 1))
            (fun j => x j - x_hat 0 j) i| +
          |singularErrorSourceTerm n (iterMatrix n M_inv N)
            (semiconvergentE n r X X_inv) M_inv ξ m i| +
          |matMulVec n (oneEigenProjector n r X X_inv)
            (matMulVec n M_inv
              (fun j => ∑ k ∈ Finset.range (m + 1), ξ (m - k) j)) i| :=
          habs
      _ ≤ infNormVec (matMulVec n (matPow n (iterMatrix n M_inv N) (m + 1))
            (fun j => x j - x_hat 0 j)) +
          cn_u * (1 + gamma_x) * (infNorm M + infNorm N) * infNormVec x *
            (∑' i : ℕ, infNorm (matMul n (matMul n
              (matPow n (iterMatrix n M_inv N) i)
              (semiconvergentE n r X X_inv)) M_inv)) +
          infNorm (matMul n (oneEigenProjector n r X X_inv) M_inv) *
            (((m : ℝ) + 1) * (cn_u * (1 + gamma_x) *
              (infNorm M + infNorm N) * infNormVec x)) := by
          exact add_le_add (add_le_add h1 h2) h3
      _ = _ := hring
  · have hnn1 : 0 ≤ infNormVec (matMulVec n
        (matPow n (iterMatrix n M_inv N) (m + 1))
        (fun j => x j - x_hat 0 j)) := infNormVec_nonneg _
    have hnn2 : 0 ≤ (∑' i : ℕ, infNorm (matMul n (matMul n
        (matPow n (iterMatrix n M_inv N) i)
        (semiconvergentE n r X X_inv)) M_inv)) +
        ((m : ℝ) + 1) * infNorm (matMul n
          (oneEigenProjector n r X X_inv) M_inv) :=
      add_nonneg htsum0
        (mul_nonneg (by positivity) (infNorm_nonneg _))
    exact add_nonneg hnn1 (mul_nonneg hμ0 hnn2)

-- ============================================================
-- §17.4  K. p. 335 top: Σ'_{i=0}^∞ GⁱE = (I−G)^D
-- ============================================================

/-- Telescoped partial sums of the (17.30) block terms:
    `Σ_{k=0}^{N−1} Jᵏ·diag(0, I_{n−r}) = W − Jᴺ·W` entrywise, from the
    bottom-block inverse identity `(I−J)·W = diag(0, I_{n−r})`. -/
theorem sum_range_matPow_J_bottomProjector_entry (n r : ℕ)
    (J W : Fin n → Fin n → ℝ)
    (hW1 : matMul n (matSub_id n J) W = bottomProjector n r) :
    ∀ (N : ℕ) (c d : Fin n),
      (∑ k ∈ Finset.range N,
        matMul n (matPow n J k) (bottomProjector n r) c d) =
      W c d - matMul n (matPow n J N) W c d := by
  intro N
  induction N with
  | zero =>
      intro c d
      have hid : matMul n (matPow n J 0) W c d = W c d := by
        rw [matPow_zero, matMul_id_left]
      rw [Finset.sum_range_zero, hid]
      ring
  | succ N ih =>
      intro c d
      have hstep : matMul n (matPow n J N) (bottomProjector n r) c d =
          matMul n (matPow n J N) W c d -
            matMul n (matPow n J (N + 1)) W c d := by
        calc matMul n (matPow n J N) (bottomProjector n r) c d
            = matMul n (matPow n J N) (matMul n (matSub_id n J) W) c d := by
              rw [hW1]
          _ = matMul n (matMul n (matPow n J N) (matSub_id n J)) W c d := by
              rw [← matMul_assoc n (matPow n J N) (matSub_id n J) W]
          _ = ∑ e : Fin n,
                matMul n (matPow n J N) (matSub_id n J) c e * W e d := rfl
          _ = ∑ e : Fin n,
                (matPow n J N c e - matPow n J (N + 1) c e) * W e d :=
              Finset.sum_congr rfl fun e _ => by
                rw [matMul_matSub_id_apply n J (matPow n J N) c e,
                  ← matPow_succ_right n J N]
          _ = ∑ e : Fin n, (matPow n J N c e * W e d -
                matPow n J (N + 1) c e * W e d) :=
              Finset.sum_congr rfl fun e _ => by ring
          _ = (∑ e : Fin n, matPow n J N c e * W e d) -
                ∑ e : Fin n, matPow n J (N + 1) c e * W e d := by
              rw [Finset.sum_sub_distrib]
          _ = matMul n (matPow n J N) W c d -
                matMul n (matPow n J (N + 1)) W c d := rfl
      rw [Finset.sum_range_succ, ih c d, hstep]
      ring

/-- The tail `Jᴺ·W` of the telescoped (17.30) sum vanishes entrywise as
    `N → ∞` under the row-sum contraction certificate. -/
theorem matPow_J_mul_W_entry_tendsto_zero (n r : ℕ)
    (J W : Fin n → Fin n → ℝ)
    (hJtop : ∀ i j : Fin n, (i : ℕ) < r → J i j = if i = j then 1 else 0)
    (hJcross : ∀ i j : Fin n, ¬(i : ℕ) < r → (j : ℕ) < r → J i j = 0)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hGamma : ∀ i : Fin n, ¬(i : ℕ) < r → ∑ j : Fin n, |J i j| ≤ q)
    (hWshape : ∀ i j : Fin n, (i : ℕ) < r ∨ (j : ℕ) < r → W i j = 0)
    (c d : Fin n) :
    Filter.Tendsto (fun N => matMul n (matPow n J N) W c d)
      Filter.atTop (nhds 0) := by
  by_cases hc : (c : ℕ) < r
  · have hconst : ∀ N, matMul n (matPow n J N) W c d = 0 := by
      intro N
      rw [matMul_row_id n (matPow n J N) W c d
        (fun l => matPow_J_top_entry n r J hJtop N c l hc)]
      exact hWshape c d (Or.inl hc)
    have hfun : (fun N => matMul n (matPow n J N) W c d) =
        (fun _ : ℕ => (0 : ℝ)) := funext hconst
    rw [hfun]
    exact tendsto_const_nhds
  · have hC0 : 0 ≤ ∑ e : Fin n, |W e d| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hbound : ∀ N, |matMul n (matPow n J N) W c d| ≤
        q ^ N * ∑ e : Fin n, |W e d| := by
      intro N
      calc |matMul n (matPow n J N) W c d|
          = |∑ e : Fin n, matPow n J N c e * W e d| := rfl
        _ ≤ ∑ e : Fin n, |matPow n J N c e * W e d| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ e : Fin n, |matPow n J N c e| * |W e d| :=
            Finset.sum_congr rfl fun e _ => abs_mul _ _
        _ ≤ ∑ e : Fin n, |matPow n J N c e| * ∑ e' : Fin n, |W e' d| := by
            refine Finset.sum_le_sum fun e _ =>
              mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            exact Finset.single_le_sum
              (fun e' _ => abs_nonneg (W e' d)) (Finset.mem_univ e)
        _ = (∑ e : Fin n, |matPow n J N c e|) *
              ∑ e' : Fin n, |W e' d| := (Finset.sum_mul _ _ _).symm
        _ ≤ q ^ N * ∑ e : Fin n, |W e d| :=
            mul_le_mul_of_nonneg_right
              (matPow_J_bottom_row_sum n r J hJcross q hq0 hGamma N c hc)
              hC0
    have hgeo : Filter.Tendsto
        (fun N : ℕ => q ^ N * ∑ e : Fin n, |W e d|)
        Filter.atTop (nhds 0) := by
      simpa using
        (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const
          (∑ e : Fin n, |W e d|)
    exact squeeze_zero_norm
      (fun N => by simpa [Real.norm_eq_abs] using hbound N) hgeo

/-- **The p. 335 display** (Higham, Accuracy and Stability of Numerical
    Algorithms, 2nd ed., §17.4, p. 335, from (17.24) and (17.30)):
    `Σ_{i=0}^∞ GⁱE = (I−G)^D`, entrywise as a `HasSum`.  This is the
    identity that motivates the componentwise constant `c(A)` of
    eq (17.32). -/
theorem hasSum_GiE_entry_drazinIG (n r : ℕ)
    (G J X X_inv W : Fin n → Fin n → ℝ)
    (hJtop : ∀ i j : Fin n, (i : ℕ) < r → J i j = if i = j then 1 else 0)
    (hJcross : ∀ i j : Fin n, ¬(i : ℕ) < r → (j : ℕ) < r → J i j = 0)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hGamma : ∀ i : Fin n, ¬(i : ℕ) < r → ∑ j : Fin n, |J i j| ≤ q)
    (hWshape : ∀ i j : Fin n, (i : ℕ) < r ∨ (j : ℕ) < r → W i j = 0)
    (hW1 : matMul n (matSub_id n J) W = bottomProjector n r)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n G X) = J) :
    ∀ a b : Fin n,
      HasSum (fun k =>
          matMul n (matPow n G k) (semiconvergentE n r X X_inv) a b)
        (drazinIG n X W X_inv a b) := by
  -- entrywise J-level HasSum: Σ'_k (Jᵏ·bP)_{cd} = W_{cd}
  have hJlevel : ∀ c d : Fin n,
      HasSum (fun k => matMul n (matPow n J k) (bottomProjector n r) c d)
        (W c d) := by
    intro c d
    have habs : ∀ k, |matMul n (matPow n J k) (bottomProjector n r) c d| ≤
        q ^ k := by
      intro k
      rw [matMul_bottomProjector_right]
      by_cases hd : (d : ℕ) < r
      · rw [if_neg (not_not_intro hd), abs_zero]
        exact pow_nonneg hq0 k
      · rw [if_pos hd]
        by_cases hc : (c : ℕ) < r
        · rw [matPow_J_top_entry n r J hJtop k c d hc,
            if_neg (fun h : c = d => hd (h ▸ hc)), abs_zero]
          exact pow_nonneg hq0 k
        · calc |matPow n J k c d|
              ≤ ∑ e : Fin n, |matPow n J k c e| :=
                Finset.single_le_sum (f := fun e => |matPow n J k c e|)
                  (fun e _ => abs_nonneg _) (Finset.mem_univ d)
            _ ≤ q ^ k :=
                matPow_J_bottom_row_sum n r J hJcross q hq0 hGamma k c hc
    have hsummable : Summable
        (fun k => matMul n (matPow n J k) (bottomProjector n r) c d) := by
      refine Summable.of_norm ?_
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
        (fun k => ?_) (summable_geometric_of_lt_one hq0 hq1)
      simpa [Real.norm_eq_abs] using habs k
    refine (hsummable.hasSum_iff_tendsto_nat).mpr ?_
    have hfun : (fun N => ∑ k ∈ Finset.range N,
        matMul n (matPow n J k) (bottomProjector n r) c d) =
        (fun N => W c d - matMul n (matPow n J N) W c d) :=
      funext fun N =>
        sum_range_matPow_J_bottomProjector_entry n r J W hW1 N c d
    rw [hfun]
    have htail := matPow_J_mul_W_entry_tendsto_zero n r J W hJtop hJcross
      q hq0 hq1 hGamma hWshape c d
    simpa using tendsto_const_nhds.sub htail
  intro a b
  have hexp : (fun k =>
      matMul n (matPow n G k) (semiconvergentE n r X X_inv) a b) =
      (fun k => ∑ c : Fin n, X a c * ∑ d : Fin n,
        matMul n (matPow n J k) (bottomProjector n r) c d * X_inv d b) := by
    funext k
    rw [eq_17_30_block n r G J X X_inv hXr hXl hsim k]
    rfl
  have htarget : drazinIG n X W X_inv a b =
      ∑ c : Fin n, X a c * ∑ d : Fin n, W c d * X_inv d b := rfl
  rw [hexp, htarget]
  refine hasSum_sum fun c _ => ?_
  refine HasSum.mul_left (X a c) ?_
  exact hasSum_sum fun d _ => (hJlevel c d).mul_right (X_inv d b)

/-- `tsum` form of the p. 335 display: `Σ'_{i=0}^∞ (GⁱE)_{ab} = ((I−G)^D)_{ab}`
    (Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    p. 335). -/
theorem tsum_GiE_entry_eq_drazinIG (n r : ℕ)
    (G J X X_inv W : Fin n → Fin n → ℝ)
    (hJtop : ∀ i j : Fin n, (i : ℕ) < r → J i j = if i = j then 1 else 0)
    (hJcross : ∀ i j : Fin n, ¬(i : ℕ) < r → (j : ℕ) < r → J i j = 0)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hGamma : ∀ i : Fin n, ¬(i : ℕ) < r → ∑ j : Fin n, |J i j| ≤ q)
    (hWshape : ∀ i j : Fin n, (i : ℕ) < r ∨ (j : ℕ) < r → W i j = 0)
    (hW1 : matMul n (matSub_id n J) W = bottomProjector n r)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n G X) = J) (a b : Fin n) :
    (∑' k : ℕ, matMul n (matPow n G k)
        (semiconvergentE n r X X_inv) a b) =
      drazinIG n X W X_inv a b :=
  (hasSum_GiE_entry_drazinIG n r G J X X_inv W hJtop hJcross q hq0 hq1
    hGamma hWshape hW1 hXr hXl hsim a b).tsum_eq

-- ============================================================
-- §17.4  L. Eq (17.32): the all-m componentwise forward bound
-- ============================================================

/-- Entrywise summability of `|GⁱEM⁻¹|`, needed to dominate the finite
    (17.29) componentwise sums by their `tsum` (Higham, Accuracy and
    Stability of Numerical Algorithms, 2nd ed., §17.4, remark after
    eq (17.29)). -/
theorem summable_abs_GiE_Minv_entry (n r : ℕ) (hn : 0 < n)
    (G J X X_inv M_inv : Fin n → Fin n → ℝ)
    (hJtop : ∀ i j : Fin n, (i : ℕ) < r → J i j = if i = j then 1 else 0)
    (hJcross : ∀ i j : Fin n, ¬(i : ℕ) < r → (j : ℕ) < r → J i j = 0)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hGamma : ∀ i : Fin n, ¬(i : ℕ) < r → ∑ j : Fin n, |J i j| ≤ q)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n G X) = J) (i j : Fin n) :
    Summable (fun k : ℕ => |matMul n (matMul n (matPow n G k)
      (semiconvergentE n r X X_inv)) M_inv i j|) := by
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun k => ?_)
    ((summable_geometric_of_lt_one hq0 hq1).mul_left
      (infNorm X * infNorm X_inv * infNorm M_inv))
  calc |matMul n (matMul n (matPow n G k)
        (semiconvergentE n r X X_inv)) M_inv i j|
      ≤ ∑ l : Fin n, |matMul n (matMul n (matPow n G k)
          (semiconvergentE n r X X_inv)) M_inv i l| :=
        Finset.single_le_sum
          (f := fun l => |matMul n (matMul n (matPow n G k)
            (semiconvergentE n r X X_inv)) M_inv i l|)
          (fun l _ => abs_nonneg _) (Finset.mem_univ j)
    _ ≤ infNorm (matMul n (matMul n (matPow n G k)
          (semiconvergentE n r X X_inv)) M_inv) :=
        row_sum_le_infNorm _ i
    _ ≤ infNorm X * infNorm X_inv * infNorm M_inv * q ^ k :=
        infNorm_GiE_Minv_le n r hn G J X X_inv M_inv hJtop hJcross
          q hq0 hGamma hXr hXl hsim k

/-- **The literal eq (17.32)** (Higham, Accuracy and Stability of Numerical
    Algorithms, 2nd ed., §17.4, eq (17.32), p. 335): the componentwise
    all-m forward bound
    `|e_{m+1}| ≤ |G^{m+1}e₀| + c_n u(1+θ_x){ c(A)|(I−G)^D M⁻¹|
       + (m+1)|(I−E)M⁻¹| }(|M|+|N|)|x|`.

    The printed `c(A)` is `min{ ε : Σ'_{i=0}^∞ |GⁱEM⁻¹| ≤ ε|(I−G)^D M⁻¹| }`;
    here it enters as a certificate hypothesis `hcA` for the constant `cA`,
    following this repository's admissible-constant pattern for the (17.12)
    `c(A)` (the minimality/attainment of the printed min is not needed for
    the bound).  The entrywise identity `Σ' GⁱE = (I−G)^D` behind the
    printed definition is `tsum_GiE_entry_eq_drazinIG`.  In this
    repository's naming the book's `E` is `semiconvergentE` and the book's
    `I−E` is `oneEigenProjector`; `(|M|+|N|)|x|` is
    `stationaryLocalErrorSourceVector`.  The Drazin inverse-data hypotheses
    (`_hWshape`/`_hW1`/`_hW2`) pin `drazinIG` as the genuine `(I−G)^D` of
    (17.24); the bound itself consumes only the `hcA` certificate. -/
theorem eq_17_32_componentwise_bound (n : ℕ)
    (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ))
    (hIter : SourceComputedIteration n M N b x_hat ξ)
    (r : ℕ) (J X X_inv W : Fin n → Fin n → ℝ)
    (hJtop : ∀ i j : Fin n, (i : ℕ) < r → J i j = if i = j then 1 else 0)
    (hJcross : ∀ i j : Fin n, ¬(i : ℕ) < r → (j : ℕ) < r → J i j = 0)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hGamma : ∀ i : Fin n, ¬(i : ℕ) < r → ∑ j : Fin n, |J i j| ≤ q)
    (_hWshape : ∀ i j : Fin n, (i : ℕ) < r ∨ (j : ℕ) < r → W i j = 0)
    (_hW1 : matMul n (matSub_id n J) W = bottomProjector n r)
    (_hW2 : matMul n W (matSub_id n J) = bottomProjector n r)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n (iterMatrix n M_inv N) X) = J)
    (cn_u theta_x : ℝ) (hcn : 0 ≤ cn_u) (hθ : 0 ≤ theta_x)
    (hx_bound : ComponentwiseIterateGrowthBound n x x_hat theta_x)
    (hLocal : LocalErrorBound n M N b x_hat ξ cn_u)
    (cA : ℝ)
    (hcA : ∀ i j : Fin n,
      (∑' k : ℕ, |matMul n (matMul n (matPow n (iterMatrix n M_inv N) k)
          (semiconvergentE n r X X_inv)) M_inv i j|) ≤
        cA * |matMul n (drazinIG n X W X_inv) M_inv i j|)
    (m : ℕ) :
    ∀ i, |x i - x_hat (m + 1) i| ≤
      |matMulVec n (matPow n (iterMatrix n M_inv N) (m + 1))
          (fun j => x j - x_hat 0 j) i| +
      cn_u * (1 + theta_x) *
        (cA * matMulVec n
            (absMatrix n (matMul n (drazinIG n X W X_inv) M_inv))
            (stationaryLocalErrorSourceVector n M N x) i +
          ((m : ℝ) + 1) * matMulVec n
            (absMatrix n (matMul n (oneEigenProjector n r X X_inv) M_inv))
            (stationaryLocalErrorSourceVector n M N x) i) := by
  intro i
  have hn : 0 < n := i.pos
  have hAx' : ∀ i, ∑ j : Fin n, (M i j - N i j) * x j = b i := by
    intro i
    calc ∑ j : Fin n, (M i j - N i j) * x j
        = ∑ j : Fin n, A i j * x j :=
          Finset.sum_congr rfl fun j _ => by rw [hS.splitting i j]
      _ = b i := hAx i
  have hξ : ∀ (t : ℕ) (j : Fin n), |ξ t j| ≤ cn_u * (1 + theta_x) *
      stationaryLocalErrorSourceVector n M N x j := by
    intro t j
    simpa [stationaryLocalErrorSourceVector] using
      local_error_simplified n M N b x hAx' x_hat ξ cn_u theta_x
        hcn hθ hx_bound hLocal t j
  have hsrc0 : ∀ j, 0 ≤ stationaryLocalErrorSourceVector n M N x j :=
    fun j => Finset.sum_nonneg fun l _ =>
      mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)
  have hsplit := singular_error_split_semiconvergent n A M N M_inv hS b x
    hAx x_hat ξ hIter r J X X_inv hJtop hJcross q hq0 hq1 hGamma
    hXr hXl hsim m i
  -- S_m: the finite (17.29) componentwise bound
  have hT2 := singularErrorSourceTerm_componentwise_bound n
    (iterMatrix n M_inv N) (semiconvergentE n r X X_inv) M_inv M N x ξ
    cn_u theta_x hξ m i
  -- dominate the finite componentwise coefficient by the c(A) certificate
  have hT2' : singularErrorSourceComponentBound n (iterMatrix n M_inv N)
      (semiconvergentE n r X X_inv) M_inv M N x cn_u theta_x m i ≤
      cn_u * (1 + theta_x) *
        (cA * matMulVec n
          (absMatrix n (matMul n (drazinIG n X W X_inv) M_inv))
          (stationaryLocalErrorSourceVector n M N x) i) := by
    unfold singularErrorSourceComponentBound
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hcn (by linarith))
    calc ∑ k ∈ Finset.range (m + 1),
          matMulVec n (absMatrix n (matMul n (matMul n
            (matPow n (iterMatrix n M_inv N) k)
            (semiconvergentE n r X X_inv)) M_inv))
            (stationaryLocalErrorSourceVector n M N x) i
        = ∑ k ∈ Finset.range (m + 1), ∑ l : Fin n,
            |matMul n (matMul n (matPow n (iterMatrix n M_inv N) k)
              (semiconvergentE n r X X_inv)) M_inv i l| *
              stationaryLocalErrorSourceVector n M N x l := rfl
      _ = ∑ l : Fin n, ∑ k ∈ Finset.range (m + 1),
            |matMul n (matMul n (matPow n (iterMatrix n M_inv N) k)
              (semiconvergentE n r X X_inv)) M_inv i l| *
              stationaryLocalErrorSourceVector n M N x l :=
          Finset.sum_comm
      _ = ∑ l : Fin n, (∑ k ∈ Finset.range (m + 1),
            |matMul n (matMul n (matPow n (iterMatrix n M_inv N) k)
              (semiconvergentE n r X X_inv)) M_inv i l|) *
              stationaryLocalErrorSourceVector n M N x l :=
          Finset.sum_congr rfl fun l _ => (Finset.sum_mul _ _ _).symm
      _ ≤ ∑ l : Fin n, (cA *
            |matMul n (drazinIG n X W X_inv) M_inv i l|) *
              stationaryLocalErrorSourceVector n M N x l := by
          refine Finset.sum_le_sum fun l _ =>
            mul_le_mul_of_nonneg_right ?_ (hsrc0 l)
          have hpart : (∑ k ∈ Finset.range (m + 1),
              |matMul n (matMul n (matPow n (iterMatrix n M_inv N) k)
                (semiconvergentE n r X X_inv)) M_inv i l|) ≤
              ∑' k : ℕ, |matMul n (matMul n
                (matPow n (iterMatrix n M_inv N) k)
                (semiconvergentE n r X X_inv)) M_inv i l| :=
            Summable.sum_le_tsum (Finset.range (m + 1))
              (fun _ _ => abs_nonneg _)
              (summable_abs_GiE_Minv_entry n r hn (iterMatrix n M_inv N)
                J X X_inv M_inv hJtop hJcross q hq0 hq1 hGamma
                hXr hXl hsim i l)
          exact hpart.trans (hcA i l)
      _ = cA * ∑ l : Fin n,
            |matMul n (drazinIG n X W X_inv) M_inv i l| *
              stationaryLocalErrorSourceVector n M N x l := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun l _ => by ring
      _ = cA * matMulVec n
            (absMatrix n (matMul n (drazinIG n X W X_inv) M_inv))
            (stationaryLocalErrorSourceVector n M N x) i := rfl
  -- accumulated (I−E)M⁻¹ term, componentwise
  have hT3 : |matMulVec n (oneEigenProjector n r X X_inv)
      (matMulVec n M_inv
        (fun j => ∑ k ∈ Finset.range (m + 1), ξ (m - k) j)) i| ≤
      ((m : ℝ) + 1) * (cn_u * (1 + theta_x) * matMulVec n
        (absMatrix n (matMul n (oneEigenProjector n r X X_inv) M_inv))
        (stationaryLocalErrorSourceVector n M N x) i) := by
    have heq : matMulVec n (oneEigenProjector n r X X_inv)
        (matMulVec n M_inv
          (fun j => ∑ k ∈ Finset.range (m + 1), ξ (m - k) j)) i =
        matMulVec n (matMul n (oneEigenProjector n r X X_inv) M_inv)
          (fun j => ∑ k ∈ Finset.range (m + 1), ξ (m - k) j) i :=
      (matMulVec_matMul n (oneEigenProjector n r X X_inv) M_inv
        (fun j => ∑ k ∈ Finset.range (m + 1), ξ (m - k) j) i).symm
    rw [heq]
    calc |matMulVec n (matMul n (oneEigenProjector n r X X_inv) M_inv)
          (fun j => ∑ k ∈ Finset.range (m + 1), ξ (m - k) j) i|
        ≤ ∑ l : Fin n,
            |matMul n (oneEigenProjector n r X X_inv) M_inv i l| *
            |∑ k ∈ Finset.range (m + 1), ξ (m - k) l| :=
          abs_matMulVec_le n _ _ i
      _ ≤ ∑ l : Fin n,
            |matMul n (oneEigenProjector n r X X_inv) M_inv i l| *
            (((m : ℝ) + 1) * (cn_u * (1 + theta_x) *
              stationaryLocalErrorSourceVector n M N x l)) := by
          refine Finset.sum_le_sum fun l _ =>
            mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          calc |∑ k ∈ Finset.range (m + 1), ξ (m - k) l|
              ≤ ∑ k ∈ Finset.range (m + 1), |ξ (m - k) l| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _k ∈ Finset.range (m + 1), cn_u * (1 + theta_x) *
                  stationaryLocalErrorSourceVector n M N x l :=
                Finset.sum_le_sum fun k _ => hξ (m - k) l
            _ = ((m : ℝ) + 1) * (cn_u * (1 + theta_x) *
                  stationaryLocalErrorSourceVector n M N x l) := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
                push_cast
                ring
      _ = ∑ l : Fin n, ((m : ℝ) + 1) * (cn_u * (1 + theta_x) *
            (|matMul n (oneEigenProjector n r X X_inv) M_inv i l| *
              stationaryLocalErrorSourceVector n M N x l)) :=
          Finset.sum_congr rfl fun l _ => by ring
      _ = ((m : ℝ) + 1) * ∑ l : Fin n, cn_u * (1 + theta_x) *
            (|matMul n (oneEigenProjector n r X X_inv) M_inv i l| *
              stationaryLocalErrorSourceVector n M N x l) :=
          (Finset.mul_sum _ _ _).symm
      _ = ((m : ℝ) + 1) * (cn_u * (1 + theta_x) * ∑ l : Fin n,
            |matMul n (oneEigenProjector n r X X_inv) M_inv i l| *
              stationaryLocalErrorSourceVector n M N x l) := by
          rw [← Finset.mul_sum]
      _ = ((m : ℝ) + 1) * (cn_u * (1 + theta_x) * matMulVec n
            (absMatrix n (matMul n (oneEigenProjector n r X X_inv) M_inv))
            (stationaryLocalErrorSourceVector n M N x) i) := rfl
  -- assemble
  have habs : |x i - x_hat (m + 1) i| ≤
      |matMulVec n (matPow n (iterMatrix n M_inv N) (m + 1))
        (fun j => x j - x_hat 0 j) i| +
      |singularErrorSourceTerm n (iterMatrix n M_inv N)
        (semiconvergentE n r X X_inv) M_inv ξ m i| +
      |matMulVec n (oneEigenProjector n r X X_inv)
        (matMulVec n M_inv
          (fun j => ∑ k ∈ Finset.range (m + 1), ξ (m - k) j)) i| := by
    rw [hsplit]
    calc |matMulVec n (matPow n (iterMatrix n M_inv N) (m + 1))
          (fun j => x j - x_hat 0 j) i +
        singularErrorSourceTerm n (iterMatrix n M_inv N)
          (semiconvergentE n r X X_inv) M_inv ξ m i +
        matMulVec n (oneEigenProjector n r X X_inv)
          (matMulVec n M_inv
            (fun j => ∑ k ∈ Finset.range (m + 1), ξ (m - k) j)) i|
        ≤ |matMulVec n (matPow n (iterMatrix n M_inv N) (m + 1))
            (fun j => x j - x_hat 0 j) i +
          singularErrorSourceTerm n (iterMatrix n M_inv N)
            (semiconvergentE n r X X_inv) M_inv ξ m i| +
          |matMulVec n (oneEigenProjector n r X X_inv)
            (matMulVec n M_inv
              (fun j => ∑ k ∈ Finset.range (m + 1), ξ (m - k) j)) i| :=
          abs_add_le _ _
      _ ≤ _ := add_le_add (abs_add_le _ _) le_rfl
  have h2 : |singularErrorSourceTerm n (iterMatrix n M_inv N)
      (semiconvergentE n r X X_inv) M_inv ξ m i| ≤
      cn_u * (1 + theta_x) *
        (cA * matMulVec n
          (absMatrix n (matMul n (drazinIG n X W X_inv) M_inv))
          (stationaryLocalErrorSourceVector n M N x) i) :=
    hT2.trans hT2'
  have hring : |matMulVec n (matPow n (iterMatrix n M_inv N) (m + 1))
        (fun j => x j - x_hat 0 j) i| +
      cn_u * (1 + theta_x) *
        (cA * matMulVec n
          (absMatrix n (matMul n (drazinIG n X W X_inv) M_inv))
          (stationaryLocalErrorSourceVector n M N x) i) +
      ((m : ℝ) + 1) * (cn_u * (1 + theta_x) * matMulVec n
        (absMatrix n (matMul n (oneEigenProjector n r X X_inv) M_inv))
        (stationaryLocalErrorSourceVector n M N x) i) =
      |matMulVec n (matPow n (iterMatrix n M_inv N) (m + 1))
        (fun j => x j - x_hat 0 j) i| +
      cn_u * (1 + theta_x) *
        (cA * matMulVec n
            (absMatrix n (matMul n (drazinIG n X W X_inv) M_inv))
            (stationaryLocalErrorSourceVector n M N x) i +
          ((m : ℝ) + 1) * matMulVec n
            (absMatrix n (matMul n (oneEigenProjector n r X X_inv) M_inv))
            (stationaryLocalErrorSourceVector n M N x) i) := by ring
  calc |x i - x_hat (m + 1) i|
      ≤ |matMulVec n (matPow n (iterMatrix n M_inv N) (m + 1))
          (fun j => x j - x_hat 0 j) i| +
        |singularErrorSourceTerm n (iterMatrix n M_inv N)
          (semiconvergentE n r X X_inv) M_inv ξ m i| +
        |matMulVec n (oneEigenProjector n r X X_inv)
          (matMulVec n M_inv
            (fun j => ∑ k ∈ Finset.range (m + 1), ξ (m - k) j)) i| := habs
    _ ≤ |matMulVec n (matPow n (iterMatrix n M_inv N) (m + 1))
          (fun j => x j - x_hat 0 j) i| +
        cn_u * (1 + theta_x) *
          (cA * matMulVec n
            (absMatrix n (matMul n (drazinIG n X W X_inv) M_inv))
            (stationaryLocalErrorSourceVector n M N x) i) +
        ((m : ℝ) + 1) * (cn_u * (1 + theta_x) * matMulVec n
          (absMatrix n (matMul n (oneEigenProjector n r X X_inv) M_inv))
          (stationaryLocalErrorSourceVector n M N x) i) :=
        add_le_add (add_le_add le_rfl h2) hT3
    _ = _ := hring

-- ============================================================
-- §17.4  Uniqueness of the index-one Drazin (group) inverse
-- ============================================================

/-- **Uniqueness of the index-one Drazin inverse** (Higham, Accuracy and
    Stability of Numerical Algorithms, 2nd ed., §17.4, p. 331: the Drazin
    inverse is "the unique matrix `A^D` such that" the three identities
    hold).  Classical group-inverse argument: from the identities,
    `A·D₁ = A·D₂·A·D₁ = A·D₂`, and then
    `D₁ = D₁·A·D₁ = D₁·A·D₂ = D₂·A·D₂ = D₂`.  This upgrades
    `drazinIG_spec` to the printed uniqueness-inclusive definition. -/
theorem indexOneDrazinInverse_unique (n : ℕ)
    (A D₁ D₂ : Fin n → Fin n → ℝ)
    (h1 : IndexOneDrazinInverse n A D₁)
    (h2 : IndexOneDrazinInverse n A D₂) : D₁ = D₂ := by
  -- Step 1: A·D₁ = A·D₂ (both equal A·D₂·A·D₁).
  have hAD : matMul n A D₁ = matMul n A D₂ := by
    have hleft : matMul n (matMul n A D₂) (matMul n A D₁) =
        matMul n A D₁ := by
      -- A·D₂·A·D₁ = (A²·D₂)·D₁ = A·D₁ using comm on D₂ then index_one for D₂
      calc matMul n (matMul n A D₂) (matMul n A D₁)
          = matMul n (matMul n (matMul n A D₂) A) D₁ :=
            (matMul_assoc n (matMul n A D₂) A D₁).symm
        _ = matMul n (matMul n A (matMul n D₂ A)) D₁ := by
            rw [matMul_assoc n A D₂ A]
        _ = matMul n (matMul n A (matMul n A D₂)) D₁ := by
            rw [h2.comm]
        _ = matMul n (matMul n (matMul n A A) D₂) D₁ := by
            rw [matMul_assoc n A A D₂]
        _ = matMul n A D₁ := by rw [h2.index_one]
    have hright : matMul n (matMul n A D₂) (matMul n A D₁) =
        matMul n A D₂ := by
      -- A·D₂·A·D₁ = D₂·(A²·D₁) = D₂·A = A·D₂ using comm then index_one for D₁
      calc matMul n (matMul n A D₂) (matMul n A D₁)
          = matMul n (matMul n D₂ A) (matMul n A D₁) := by
            rw [h2.comm]
        _ = matMul n D₂ (matMul n A (matMul n A D₁)) :=
            matMul_assoc n D₂ A (matMul n A D₁)
        _ = matMul n D₂ (matMul n (matMul n A A) D₁) := by
            rw [← matMul_assoc n A A D₁]
        _ = matMul n D₂ A := by rw [h1.index_one]
        _ = matMul n A D₂ := by rw [← h2.comm]
    exact hleft.symm.trans hright
  -- Step 2: D₁ = D₁·A·D₁ = D₁·A·D₂ = D₂·A·D₂ = D₂.
  have hD1 : D₁ = matMul n D₁ (matMul n A D₂) := by
    rw [← hAD]
    exact h1.reflexive.symm
  have hswap : matMul n D₁ (matMul n A D₂) = matMul n D₂ (matMul n A D₂) := by
    calc matMul n D₁ (matMul n A D₂)
        = matMul n (matMul n D₁ A) D₂ := (matMul_assoc n D₁ A D₂).symm
      _ = matMul n (matMul n A D₁) D₂ := by rw [← h1.comm]
      _ = matMul n (matMul n A D₂) D₂ := by rw [hAD]
      _ = matMul n (matMul n D₂ A) D₂ := by rw [h2.comm]
      _ = matMul n D₂ (matMul n A D₂) := matMul_assoc n D₂ A D₂
  rw [hD1, hswap]
  exact h2.reflexive

/-- **The printed (17.24) with uniqueness**: any index-one Drazin inverse of
    `I − G` coincides with the block-data construction `drazinIG`.  Combined
    with `drazinIG_spec` this closes the p. 331 "unique matrix `A^D` such
    that" formulation for the index-one case the analysis uses. -/
theorem indexOneDrazinInverse_eq_drazinIG (n r : ℕ)
    (G J X X_inv W : Fin n → Fin n → ℝ)
    (hJtop : ∀ i j : Fin n, (i : ℕ) < r → J i j = if i = j then 1 else 0)
    (hJcross : ∀ i j : Fin n, ¬(i : ℕ) < r → (j : ℕ) < r → J i j = 0)
    (hWshape : ∀ i j : Fin n, (i : ℕ) < r ∨ (j : ℕ) < r → W i j = 0)
    (hW1 : matMul n (matSub_id n J) W = bottomProjector n r)
    (hW2 : matMul n W (matSub_id n J) = bottomProjector n r)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n G X) = J)
    (D : Fin n → Fin n → ℝ)
    (hD : IndexOneDrazinInverse n (matSub_id n G) D) :
    D = drazinIG n X W X_inv :=
  indexOneDrazinInverse_unique n (matSub_id n G) D
    (drazinIG n X W X_inv) hD
    (drazinIG_spec n r G J X X_inv W hJtop hJcross hWshape hW1 hW2
      hXr hXl hsim)

end NumStability
