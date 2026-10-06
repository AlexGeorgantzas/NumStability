import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Analysis.LinearOperators.Schur.Real.InvariantSubspace.TwoByTwo

W05 semantic leaf. Declaration commands are copied byte-identically from the frozen C0004 owners.
-/

/-
Analysis/RealInvariantSubspace.lean

The **ℂ→ℝ real invariant-subspace descent**.  Higham, *Accuracy and Stability
of Numerical Algorithms*, 2nd ed., §16.2 (real Schur decomposition (16.4)) and
§17.4 (Householder `[106, Lem 6.9]`, the ℂ→ℝ descent behind semiconvergent
existence).

This module supplies the single primitive that the obstruction blocks of
`Analysis/RealSchurTriangulation.lean` and `Analysis/SemiconvergentExistenceGaps.lean`
named as missing from Mathlib (v4.29.0): a **real invariant subspace of
dimension `1` or `2`** for an arbitrary real square matrix, obtained by
complexifying, taking a complex eigenvector `v`, and forming the real span of
`Re v` and `Im v`.

Concretely, for `A : Matrix (Fin n) (Fin n) ℝ` with `0 < n`:

  `∃ (W : Submodule ℝ (Fin n → ℝ)),
      0 < finrank ℝ W ∧ finrank ℝ W ≤ 2 ∧ ∀ w ∈ W, A.mulVecLin w ∈ W`.

The `2`-dimensional real span of `Re v, Im v` for a genuine complex-conjugate
eigenvalue pair is exactly the invariant subspace behind the `2×2` blocks of the
real quasi-triangular Schur form (16.4); when the eigenvalue is real, `Re v` is a
real eigenvector and the subspace is `1`-dimensional.  This is the "peel-1-or-2"
deflation primitive of the real Schur / real-Jordan reduction.

Mathlib (v4.29.0) has no real Schur form and no ready-made "invariant subspace of
dimension `≤ 2`" primitive; it does have `Module.End.exists_eigenvalue` over an
algebraically closed field and the entry-wise real/imaginary part maps of `ℂ`.
This file assembles the descent from those, honestly and unconditionally (no
extra hypothesis beyond the honest domain `0 < n`, which is genuinely necessary:
the empty matrix has no nonzero subspace at all).

Reference: N. J. Higham, *Accuracy and Stability of Numerical Algorithms*,
2nd ed., §16.2, equation (16.4) (real Schur decomposition); §17.4, Householder
`[106, Lem 6.9]`.  The real invariant-subspace fact is classical, see e.g.
Horn & Johnson, *Matrix Analysis*, §2.3 / Golub & Van Loan, *Matrix
Computations*, §7.4.

Main result:
* `NumStability.exists_real_invariant_subspace_dim_le_two` — every nonempty
  real matrix has a real invariant subspace of dimension `1` or `2`.
-/









open scoped BigOperators Matrix
open Module

namespace NumStability

namespace RealInvariantSubspaceAux

/-! ### Complexification and the real/imaginary parts of a complex eigenvector -/

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)



































































































































































end RealInvariantSubspaceAux

/-! ### The main theorem -/

/-- A real matrix has no nonzero real eigenline.  This source-side predicate is
    intentionally independent of the Sylvester development, so the real
    quasi-Schur construction can export irreducible `2 x 2` block data without
    creating an import cycle. -/
def MatrixNoRealEigenline {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ x : Fin n → ℝ, x ≠ 0 -> ¬ ∃ ν : ℝ, A *ᵥ x = ν • x

/-- The principal `2 x 2` block of a matrix on the ordered index pair `(p,q)`.
    This source-side definition is shared by future real quasi-Schur block
    exports and avoids depending on the Sylvester-specific block definitions. -/
def principalTwoBlock {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j =>
    if i = 0 then
      if j = 0 then A p p else A p q
    else
      if j = 0 then A q p else A q q

@[simp] theorem principalTwoBlock_zero_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) :
    principalTwoBlock A p q 0 0 = A p p := by
  simp [principalTwoBlock]

@[simp] theorem principalTwoBlock_zero_one {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) :
    principalTwoBlock A p q 0 1 = A p q := by
  simp [principalTwoBlock]

@[simp] theorem principalTwoBlock_one_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) :
    principalTwoBlock A p q 1 0 = A q p := by
  simp [principalTwoBlock]

@[simp] theorem principalTwoBlock_one_one {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) :
    principalTwoBlock A p q 1 1 = A q q := by
  simp [principalTwoBlock]

/-- The canonical real `2 x 2` rotation-scaling block
    `[[alpha,beta],[-beta,alpha]]` with `beta != 0` has no real eigenline. -/
theorem matrixNoRealEigenline_fin_two_of_rotation_scaling_entries
    (B : Matrix (Fin 2) (Fin 2) ℝ) (α β : ℝ)
    (h00 : B 0 0 = α)
    (h01 : B 0 1 = β)
    (h10 : B 1 0 = -β)
    (h11 : B 1 1 = α)
    (hβ : β ≠ 0) :
    MatrixNoRealEigenline B := by
  intro x hx hEig
  rcases hEig with ⟨ν, hν⟩
  have h0 := congrFun hν (0 : Fin 2)
  have h1 := congrFun hν (1 : Fin 2)
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h00, h01, h10, h11] at h0 h1
  have hsumsq : β * (x 0 ^ 2 + x 1 ^ 2) = 0 := by
    have h0mul : (α * x 0 + β * x 1) * x 1 = (ν * x 0) * x 1 := by
      rw [h0]
    have h1mul : (-(β * x 0) + α * x 1) * x 0 = (ν * x 1) * x 0 := by
      rw [h1]
    nlinarith [h0mul, h1mul]
  have hsq : x 0 ^ 2 + x 1 ^ 2 = 0 := (mul_eq_zero.mp hsumsq).resolve_left hβ
  have hx0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), hsq]
  have hx1 : x 1 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), hsq]
  apply hx
  funext k
  fin_cases k <;> simp [hx0, hx1]

/-- A principal `2 x 2` block with canonical rotation-scaling entries has no
    real eigenline. -/
theorem matrixNoRealEigenline_principalTwoBlock_of_rotation_scaling_entries
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) (α β : ℝ)
    (hpp : A p p = α)
    (hqq : A q q = α)
    (hpq : A p q = β)
    (hqp : A q p = -β)
    (hβ : β ≠ 0) :
    MatrixNoRealEigenline (principalTwoBlock A p q) :=
  matrixNoRealEigenline_fin_two_of_rotation_scaling_entries
    (principalTwoBlock A p q) α β
    (by simpa using hpp)
    (by simpa using hpq)
    (by simpa using hqp)
    (by simpa using hqq)
    hβ

/-- A real `2 x 2` matrix with no real eigenline has negative discriminant.
    This is the source-side spectral certificate needed before the Sylvester
    block-separation layer consumes such blocks. -/
theorem matrixNoRealEigenline_fin_two_disc_neg
    (B : Matrix (Fin 2) (Fin 2) ℝ)
    (hno : MatrixNoRealEigenline B) :
    (B 0 0 - B 1 1) ^ 2 + 4 * B 0 1 * B 1 0 < 0 := by
  by_contra hnot
  have hdisc : 0 ≤ (B 0 0 - B 1 1) ^ 2 + 4 * B 0 1 * B 1 0 := by
    linarith
  by_cases hsub : B 1 0 = 0
  · let x : Fin 2 → ℝ := fun k => if k = 0 then 1 else 0
    have hxne : x ≠ 0 := by
      intro hx
      have hcoord := congrFun hx (0 : Fin 2)
      norm_num [x] at hcoord
    have hEig : ∃ ν : ℝ, B *ᵥ x = ν • x := by
      refine ⟨B 0 0, ?_⟩
      funext k
      fin_cases k
      · simp [x, Matrix.mulVec, dotProduct]
      · simp [x, Matrix.mulVec, dotProduct, hsub]
    exact hno x hxne hEig
  · let disc : ℝ := (B 0 0 - B 1 1) ^ 2 + 4 * B 0 1 * B 1 0
    let ν : ℝ := (B 0 0 + B 1 1 + Real.sqrt disc) / 2
    let x : Fin 2 → ℝ := fun k => if k = 0 then ν - B 1 1 else B 1 0
    have hdisc_nonneg : 0 ≤ disc := by
      dsimp [disc]
      exact hdisc
    have hsqrt : (Real.sqrt disc) ^ 2 = disc := Real.sq_sqrt hdisc_nonneg
    have hroot : (B 0 0 - ν) * (B 1 1 - ν) - B 0 1 * B 1 0 = 0 := by
      dsimp [ν, disc] at hsqrt ⊢
      nlinarith [hsqrt]
    have hxne : x ≠ 0 := by
      intro hx
      have hcoord := congrFun hx (1 : Fin 2)
      exact hsub (by simpa [x] using hcoord)
    have hEig : ∃ μ : ℝ, B *ᵥ x = μ • x := by
      refine ⟨ν, ?_⟩
      funext k
      fin_cases k
      · have hcoord :
            B 0 0 * (ν - B 1 1) + B 0 1 * B 1 0 =
              ν * (ν - B 1 1) := by
          nlinarith [hroot]
        simpa [x, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hcoord
      · have hcoord :
            B 1 0 * (ν - B 1 1) + B 1 1 * B 1 0 =
              ν * B 1 0 := by
          ring
        simpa [x, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hcoord
    exact hno x hxne hEig

/-- A principal `2 x 2` block with no real eigenline has negative discriminant
    in the ambient matrix entries. -/
theorem principalTwoBlock_disc_neg_of_matrixNoRealEigenline
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n)
    (hno : MatrixNoRealEigenline (principalTwoBlock A p q)) :
    (A p p - A q q) ^ 2 + 4 * A p q * A q p < 0 := by
  simpa using
    matrixNoRealEigenline_fin_two_disc_neg (principalTwoBlock A p q) hno


















































































































































































































































































































































































-- ============================================================
-- §16.2 (16.4) / §17.4 [106].  STATUS after this module.
-- ============================================================
--
-- CLOSED (unconditionally, honest domain `0 < n` only):
--   • `exists_real_invariant_subspace_dim_le_two` — the exact primitive the
--     `RealSchurTriangulation.lean` obstruction named as missing from Mathlib
--     v4.29.0 ("no ready-made 'invariant subspace of dimension ≤ 2' primitive"):
--     a real `A`-invariant subspace with `0 < finrank ≤ 2`.
--   • `exists_real_invariant_subspace_dim_one_or_two` — the sharpened
--     `finrank = 1 ∨ finrank = 2` version (the `1×1`/`2×2` blocks of (16.4)).
--   • `exists_real_invariant_subspace_dim_one_or_two_no_real_eigenline` — the
--     same exact-dimension descent with the two-dimensional branch retaining the
--     no-real-eigenline irreducibility certificate.
--   • `real_peel_one_or_two` — the explicit, DEFLATION-READY dichotomy: either a
--     real eigenvalue with a real eigenvector (`1×1` block), or `α ± β i`,
--     `β ≠ 0`, with two `ℝ`-linearly independent real vectors on which `A` acts
--     by the real rotation-scaling block `[[α, β], [-β, α]]` (`2×2` block).  This
--     is precisely the "conjugate-pair recombination into a real invariant
--     subspace" that `SemiconvergentExistenceGaps.lean` GAP (3) recorded as
--     absent from Mathlib.
--
-- RESIDUAL OBSTRUCTION (the full general (16.4)).  Iterating this peel-1-or-2
-- primitive into the FULL real quasi-triangular ORTHOGONAL Schur form
-- `QᵀAQ = R` (block-upper-triangular, `Q` orthogonal) still needs the deflation
-- INDUCTION with a *variable* peel size `d ∈ {1, 2}`: an orthonormal basis of the
-- `d`-dimensional invariant subspace extended to the whole space
-- (`Orthonormal.exists_orthonormalBasis_extension_of_card_eq`), the resulting
-- orthogonal `Q` with leading `d` columns spanning `W`, the block-triangular
-- structure of `QᵀAQ`, and re-embedding a block-diagonal orthogonal matrix over a
-- `Fin (d + m)` reindexing.  Mathlib v4.29.0 has none of this assembled, and the
-- existing `RealSchurTriangulation.lean` deflation is hard-wired to peel size `1`
-- (`Fin (n+1)` via `Fin.cases`); a variable-`d` orthogonal deflation is the
-- single remaining bottleneck to (16.4) in full generality.  The invariant
-- subspace supplied here is exactly the primitive that induction consumes.

end NumStability
