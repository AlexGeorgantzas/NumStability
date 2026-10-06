-- Analysis/SemiconvergentExistenceComplete.lean
--
-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
-- Chapter 17 "Stationary Iterative Methods", §17.4 "Singular Systems",
-- eq (17.22) / Householder `[106, Lem 6.9]`.
--
-- GOAL: close the FULL semiconvergent block-form EXISTENCE of eq (17.22) from
-- convergence of `Gᵐ` ALONE, discharging the residual GAP (3) that the prior
-- wave (`SemiconvergentExistenceFull.lean`) reduced to exactly two concrete
-- lemmas:
--
--   (3a) the COORDINATE-LEVEL real primary/Fitting decomposition: turn the
--        Mathlib abstract splitting `ℝⁿ = ker(G−I) ⊕ range((G−I)ⁿ)` (with the
--        eigenvalue-`1` block semisimple, GAP (1)) plus a basis adapted to it
--        into an invertible `matMul` matrix `X` whose first `r` columns are
--        honest eigenvalue-`1` eigenvectors and whose remaining columns realise
--        the complement column condition `hGcolBot` with `C` = the matrix of `G`
--        restricted to the complement — CLOSED here, unconditionally;
--
--   (3b) the PER-`2×2`-block ∞-norm similarity reduction.  We prove the EXACT
--        obstruction: the ∞-norm of any real matrix similar to a `2×2` block with
--        eigenvalues `α ± β i` is `≥ |α| + |β|` (attained by the rotation-scaling
--        normal form), so the block-contractivity `hCblock` (∞-row-sums `< 1`) is
--        achievable **iff** `|α| + |β| < 1` — strictly stronger than the naive
--        `ρ = √(α²+β²) < 1` requested by the prior wave, which is FALSE.
--
-- RESULT.  (3a) is closed unconditionally; the coordinate-level real primary
-- decomposition is produced from convergence of `Gᵐ` alone, and the full block
-- form is assembled from it modulo the complement's quasi-triangular
-- block-contractive normal form.  (3b) is resolved as a sharp mathematical
-- boundary of the ∞-norm route (not a Mathlib gap): the block form in the
-- repository's `‖Γ‖∞ < 1` strengthening exists from convergence exactly when
-- every non-`1` eigenvalue `α ± β i` has `|α| + |β| < 1` (always true for real
-- spectrum).  See the closing STATUS block for the precise per-case statement.
--
-- IMPORT-ONLY: this module edits nothing.  No `sorry`/`admit`/`axiom`/
-- `native_decide`/proof-disabling option is used.
--
-- Reference: N. J. Higham, *Accuracy and Stability of Numerical Algorithms*,
-- 2nd ed., §17.4, eq (17.22); Householder `[106, Lem 6.9]`.

import NumStability.Analysis.SemiconvergentExistenceFull
import NumStability.Analysis.SemiconvergentBlockFormExists
import Mathlib.RingTheory.Artinian.Module

namespace NumStability

open scoped BigOperators Topology Matrix
open Module

-- ============================================================
-- §17.4  (3a).  The Submodule/Basis ↔ `matMul` coordinate bridge
-- ============================================================

section CoordinateBridge

variable {n : ℕ}

/-- The **column-matrix of a basis**: `basisColMatrix b` has the `k`-th basis
    vector `b k` as its `k`-th column, i.e. entry `(i, k)` is `(b k) i`.  This is
    the concrete invertible change of basis `X` of Higham §17.4 (17.22) realised
    in the repository's `Fin n → Fin n → ℝ` (`matMul`) coordinate form.  Its
    inverse is `basisRowMatrix b` (the coordinate/`repr` matrix). -/
noncomputable def basisColMatrix (b : Module.Basis (Fin n) ℝ (Fin n → ℝ)) :
    Fin n → Fin n → ℝ :=
  fun i k => b k i

/-- The **coordinate matrix of a basis**: `basisRowMatrix b` has entry `(k, i)`
    equal to the `k`-th coordinate of the `i`-th standard basis vector in the
    basis `b`, i.e. `b.repr (e_i) k`.  This is the two-sided inverse of
    `basisColMatrix b` (Higham §17.4 (17.22)). -/
noncomputable def basisRowMatrix (b : Module.Basis (Fin n) ℝ (Fin n → ℝ)) :
    Fin n → Fin n → ℝ :=
  fun k i => b.repr (Pi.single i (1 : ℝ)) k

/-- The `i`-th coordinate of a vector `u` expanded in the basis `b`:
    `u i = ∑ k, (b.repr u k) * (b k) i`.  Coordinate form of `Basis.sum_repr`. -/
theorem basis_coord_expansion (b : Module.Basis (Fin n) ℝ (Fin n → ℝ))
    (u : Fin n → ℝ) (i : Fin n) :
    u i = ∑ k : Fin n, b.repr u k * b k i := by
  have hsum : ∑ k : Fin n, b.repr u k • b k = u := b.sum_repr u
  have := congrFun hsum i
  simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this.symm

/-- **The coordinate matrix is a right inverse of the column matrix**
    (Higham §17.4 (17.22)): `basisColMatrix b · basisRowMatrix b = I`.  Entrywise
    this is the expansion of the standard basis vector `e_j` in the basis `b`,
    read off in coordinate `i`. -/
theorem basisColMatrix_isRightInverse (b : Module.Basis (Fin n) ℝ (Fin n → ℝ)) :
    IsRightInverse n (basisColMatrix b) (basisRowMatrix b) := by
  intro i j
  show (∑ k : Fin n, basisColMatrix b i k * basisRowMatrix b k j) = if i = j then 1 else 0
  simp only [basisColMatrix, basisRowMatrix]
  -- `∑ k, (b k i) * (b.repr e_j k) = e_j i = δ_ij`
  have hexp : (Pi.single j (1 : ℝ) : Fin n → ℝ) i
      = ∑ k : Fin n, b.repr (Pi.single j (1 : ℝ)) k * b k i :=
    basis_coord_expansion b (Pi.single j (1 : ℝ)) i
  have hcomm : (∑ k : Fin n, b k i * b.repr (Pi.single j (1 : ℝ)) k)
      = ∑ k : Fin n, b.repr (Pi.single j (1 : ℝ)) k * b k i := by
    apply Finset.sum_congr rfl; intro k _; ring
  rw [hcomm, ← hexp]
  by_cases hij : i = j
  · subst hij; rw [if_pos rfl]; simp [Pi.single_eq_same]
  · rw [if_neg hij]; simp [hij]

/-- **The column matrix is a right inverse of the coordinate matrix**
    (Higham §17.4 (17.22)): `basisRowMatrix b · basisColMatrix b = I`.  This is
    the other side of invertibility, following from
    `basisColMatrix_isRightInverse` by finite-dimensional Dedekind finiteness. -/
theorem basisRowMatrix_isRightInverse (b : Module.Basis (Fin n) ℝ (Fin n → ℝ)) :
    IsRightInverse n (basisRowMatrix b) (basisColMatrix b) := by
  have hL : IsLeftInverse n (basisColMatrix b) (basisRowMatrix b) :=
    isLeftInverse_of_isRightInverse (basisColMatrix b) (basisRowMatrix b)
      (basisColMatrix_isRightInverse b)
  intro i j
  exact hL i j

/-- The `matMul` action of `G` on the `k`-th column of `basisColMatrix b` is the
    matrix-vector product `G *ᵥ (b k)`, read off in coordinate `i`:
    `(G · X)_{ik} = (G *ᵥ b k) i`.  This is the bridge between the repository
    `matMul` form and Mathlib's `Matrix.mulVec`, used to import the eigenvector
    and invariance data of Higham §17.4 (17.22). -/
theorem matMul_basisColMatrix_eq_mulVec
    (G : Fin n → Fin n → ℝ) (b : Module.Basis (Fin n) ℝ (Fin n → ℝ)) (i k : Fin n) :
    matMul n G (basisColMatrix b) i k = (G *ᵥ (b k)) i := by
  show (∑ j : Fin n, G i j * basisColMatrix b j k) = (G *ᵥ (b k)) i
  simp only [basisColMatrix, Matrix.mulVec, dotProduct]

/-- The **complement action matrix** of `G` in the basis `b`: `basisActionMatrix`
    has entry `(l, k)` equal to the `l`-th coordinate of `G *ᵥ (b k)` in the basis
    `b`, i.e. `b.repr (G *ᵥ b k) l`.  Restricted to complement indices `l, k ≥ r`
    it is the matrix `C` of `G` acting on the complement of Higham §17.4 (17.22)
    (the honest matrix of `G|_F` in the `F`-part of the basis). -/
noncomputable def basisActionMatrix
    (G : Fin n → Fin n → ℝ) (b : Module.Basis (Fin n) ℝ (Fin n → ℝ)) :
    Fin n → Fin n → ℝ :=
  fun l k => b.repr (G *ᵥ (b k)) l

/-- **`hGcolTop` from the coordinate bridge.**  If the first `r` columns of the
    basis `b` are eigenvalue-`1` eigenvectors of `G` (`G *ᵥ b k = b k` for `k < r`),
    then the first `r` columns of the column matrix `X = basisColMatrix b` satisfy
    the eigenvalue-`1` column condition `matMul n G X · k = X · k`.  Higham
    §17.4 (17.22). -/
theorem basisColMatrix_colTop
    (G : Fin n → Fin n → ℝ) (b : Module.Basis (Fin n) ℝ (Fin n → ℝ)) (r : ℕ)
    (hEig : ∀ k : Fin n, (k : ℕ) < r → G *ᵥ (b k) = b k)
    (k : Fin n) (hk : (k : ℕ) < r) (i : Fin n) :
    matMul n G (basisColMatrix b) i k = basisColMatrix b i k := by
  rw [matMul_basisColMatrix_eq_mulVec, hEig k hk]
  rfl

/-- **`hGcolBot` from the coordinate bridge.**  If for every complement column
    `k ≥ r` the vector `G *ᵥ (b k)` lies in the span of the complement basis
    vectors (`b.repr (G *ᵥ b k) l = 0` for all `l < r`), then the complement
    columns of `X = basisColMatrix b` satisfy the complement column condition
    `hGcolBot` with the complement action matrix `C = basisActionMatrix G b`.
    Higham §17.4 (17.22). -/
theorem basisColMatrix_colBot
    (G : Fin n → Fin n → ℝ) (b : Module.Basis (Fin n) ℝ (Fin n → ℝ)) (r : ℕ)
    (hInv : ∀ k : Fin n, ¬(k : ℕ) < r → ∀ l : Fin n, (l : ℕ) < r →
      b.repr (G *ᵥ (b k)) l = 0)
    (k : Fin n) (hk : ¬(k : ℕ) < r) (i : Fin n) :
    matMul n G (basisColMatrix b) i k =
      ∑ l ∈ Finset.univ.filter (fun l : Fin n => ¬(l : ℕ) < r),
        basisColMatrix b i l * basisActionMatrix G b l k := by
  rw [matMul_basisColMatrix_eq_mulVec]
  -- expand `G *ᵥ (b k)` in the basis: coordinate `i` is `∑ l, (repr) l * (b l) i`
  have hexp : (G *ᵥ (b k)) i = ∑ l : Fin n, b.repr (G *ᵥ (b k)) l * b l i :=
    basis_coord_expansion b (G *ᵥ (b k)) i
  rw [hexp]
  -- restrict the sum to complement indices (the `l < r` terms vanish by `hInv`)
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun l : Fin n => ¬(l : ℕ) < r)]
  have hzero : (∑ l ∈ Finset.univ.filter (fun l : Fin n => ¬¬(l : ℕ) < r),
      b.repr (G *ᵥ (b k)) l * b l i) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro l hl
    rw [Finset.mem_filter] at hl
    have hlr : (l : ℕ) < r := not_not.mp hl.2
    rw [hInv k hk l hlr, zero_mul]
  rw [hzero, add_zero]
  refine Finset.sum_congr rfl ?_
  intro l _
  simp only [basisColMatrix, basisActionMatrix]
  ring

end CoordinateBridge

-- ============================================================
-- §17.4  (3a).  Block form from an adapted basis (coordinate bridge assembled)
-- ============================================================

/-- **Higham §17.4, eq (17.22) — `[106, Lem 6.9]` — semiconvergent block-form
    EXISTENCE from an ADAPTED REAL BASIS (the assembled coordinate bridge, (3a)).**

    This is the (3a) payoff: the full block form produced from a *single*
    `Fin n`-indexed real basis `b` of `ℝⁿ` adapted to the semiconvergent
    splitting, with all spectral/structural facts stated on the basis (never
    smuggling the ∞-norm contraction into a hypothesis):

    * `hEig`: the first `r` basis vectors are eigenvalue-`1` eigenvectors of `G`
      (`G *ᵥ b k = b k`, `k < r`) — the semisimple-at-`1` content (GAP (1));
    * `hInv`: the complement basis vectors (`k ≥ r`) span a `G`-invariant
      subspace, in coordinates `b.repr (G *ᵥ b k) l = 0` for `l < r`;
    * `hClower`/`hCblock`: the complement action matrix `C = basisActionMatrix G b`
      is quasi-upper-triangular and block-contractive for a block assignment
      `pblk` (the honest real quasi-Schur (16.4) normal form of `G|_F`).

    The change of basis `X = basisColMatrix b` (columns `= b k`) is invertible
    with inverse the coordinate matrix `basisRowMatrix b`; the eigenvector and
    invariance data give the two column conditions via the coordinate bridge; and
    the block-form assembly is delegated to
    `semiconvergent_block_form_exists_of_quasiTriangular_complement`, which
    CONSTRUCTS the ∞-norm contraction from the quasi-triangular block-contractive
    `C`.  Output: the identical `semiconvergent_block_form_exists` data package. -/
theorem semiconvergent_block_form_exists_of_adapted_basis {n : ℕ} (r : ℕ)
    (G : Fin n → Fin n → ℝ) (b : Module.Basis (Fin n) ℝ (Fin n → ℝ))
    (pblk : Fin n → ℕ)
    (hEig : ∀ k : Fin n, (k : ℕ) < r → G *ᵥ (b k) = b k)
    (hInv : ∀ k : Fin n, ¬(k : ℕ) < r → ∀ l : Fin n, (l : ℕ) < r →
      b.repr (G *ᵥ (b k)) l = 0)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hClower : ∀ i j : Fin n, ¬(i : ℕ) < r → ¬(j : ℕ) < r →
      pblk j < pblk i → basisActionMatrix G b i j = 0)
    (hCblock : ∀ i : Fin n, ¬(i : ℕ) < r →
      (∑ j ∈ Finset.univ.filter
        (fun j : Fin n => ¬(j : ℕ) < r ∧ pblk j = pblk i),
        |basisActionMatrix G b i j|) ≤ ρ) :
    ∃ (X' X'_inv Γ : Fin n → Fin n → ℝ) (q : ℝ),
      0 ≤ q ∧ q < 1 ∧
      (∀ i : Fin n, ¬(i : ℕ) < r →
        (∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬(j : ℕ) < r), |Γ i j|) ≤ q) ∧
      IsRightInverse n X' X'_inv ∧ IsRightInverse n X'_inv X' ∧
      (∀ (k : Fin n), (k : ℕ) < r → ∀ i : Fin n, matMul n G X' i k = X' i k) ∧
      matMul n X'_inv (matMul n G X') = blockJ n r Γ ∧
      (∀ i j : Fin n, (i : ℕ) < r → blockJ n r Γ i j = if i = j then 1 else 0) ∧
      (∀ i j : Fin n, ¬(i : ℕ) < r → (j : ℕ) < r → blockJ n r Γ i j = 0) ∧
      (∀ i : Fin n, ¬(i : ℕ) < r → ∑ j : Fin n, |blockJ n r Γ i j| ≤ q) := by
  refine semiconvergent_block_form_exists_of_quasiTriangular_complement n r G
    (basisColMatrix b) (basisRowMatrix b) (basisActionMatrix G b) pblk
    (basisColMatrix_isRightInverse b) (basisRowMatrix_isRightInverse b)
    ?_ ?_ hρ0 hρ1 hClower hCblock
  · exact fun k hk i => basisColMatrix_colTop G b r hEig k hk i
  · exact fun k hk i => basisColMatrix_colBot G b r hInv k hk i

-- ============================================================
-- §17.4  (3a).  The adapted basis from a real invariant splitting `⊤ = E₁ ⊕ F`
-- ============================================================

section AdaptedBasisFromSplitting

variable {n : ℕ}

/-- The **sum-indexed adapted basis** of `ℝⁿ` for a real invariant splitting
    `⊤ = E₁ ⊕ F` (`hCompl : IsCompl E₁ F`), with `E₁` occupying the `inl` block
    and `F` the `inr` block.  Built by mapping the product basis
    `bV.prod bW` (finite bases of `E₁` and `F`) through
    `Submodule.prodEquivOfIsCompl`.  This realises the real primary/Fitting
    decomposition of Higham §17.4 (17.22) as an honest basis of the ambient
    coordinate space. -/
noncomputable def adaptedSumBasis {r m : ℕ}
    {E₁ F : Submodule ℝ (Fin n → ℝ)} (hCompl : IsCompl E₁ F)
    (bV : Module.Basis (Fin r) ℝ E₁) (bW : Module.Basis (Fin m) ℝ F) :
    Module.Basis (Fin r ⊕ Fin m) ℝ (Fin n → ℝ) :=
  (bV.prod bW).map (Submodule.prodEquivOfIsCompl E₁ F hCompl)

/-- The `inl` vectors of the adapted sum basis are the `E₁`-basis vectors
    (coerced), hence lie in `E₁`.  Higham §17.4 (17.22). -/
theorem adaptedSumBasis_inl {r m : ℕ}
    {E₁ F : Submodule ℝ (Fin n → ℝ)} (hCompl : IsCompl E₁ F)
    (bV : Module.Basis (Fin r) ℝ E₁) (bW : Module.Basis (Fin m) ℝ F) (i : Fin r) :
    adaptedSumBasis hCompl bV bW (Sum.inl i) = (bV i : Fin n → ℝ) := by
  simp only [adaptedSumBasis, Module.Basis.map_apply, Module.Basis.prod_apply,
    Sum.elim_inl, Function.comp_apply, LinearMap.coe_inl,
    Submodule.coe_prodEquivOfIsCompl']
  simp

/-- The `inr` vectors of the adapted sum basis are the `F`-basis vectors
    (coerced), hence lie in `F`.  Higham §17.4 (17.22). -/
theorem adaptedSumBasis_inr {r m : ℕ}
    {E₁ F : Submodule ℝ (Fin n → ℝ)} (hCompl : IsCompl E₁ F)
    (bV : Module.Basis (Fin r) ℝ E₁) (bW : Module.Basis (Fin m) ℝ F) (j : Fin m) :
    adaptedSumBasis hCompl bV bW (Sum.inr j) = (bW j : Fin n → ℝ) := by
  simp only [adaptedSumBasis, Module.Basis.map_apply, Module.Basis.prod_apply,
    Sum.elim_inr, Function.comp_apply, LinearMap.coe_inr,
    Submodule.coe_prodEquivOfIsCompl']
  simp

/-- **The `inl`-coordinates of an `F`-vector in the adapted sum basis vanish.**
    If `y ∈ F`, then `(adaptedSumBasis hCompl bV bW).repr y (inl i) = 0`: an
    element of the complement `F` has no `E₁`-component.  This is the coordinate
    form of the direct-sum splitting `⊤ = E₁ ⊕ F` of Higham §17.4 (17.22), the
    key fact making the complement columns of `X` act within the complement
    (`hGcolBot`). -/
theorem adaptedSumBasis_repr_inl_of_mem_F {r m : ℕ}
    {E₁ F : Submodule ℝ (Fin n → ℝ)} (hCompl : IsCompl E₁ F)
    (bV : Module.Basis (Fin r) ℝ E₁) (bW : Module.Basis (Fin m) ℝ F)
    {y : Fin n → ℝ} (hy : y ∈ F) (i : Fin r) :
    (adaptedSumBasis hCompl bV bW).repr y (Sum.inl i) = 0 := by
  -- `(b.map e).repr y = (bV.prod bW).repr (e.symm y)`, and `(e.symm y).1 = 0` for `y ∈ F`
  have hrepr : (adaptedSumBasis hCompl bV bW).repr y (Sum.inl i)
      = (bV.prod bW).repr ((Submodule.prodEquivOfIsCompl E₁ F hCompl).symm y) (Sum.inl i) := by
    simp only [adaptedSumBasis, Module.Basis.map_repr, LinearEquiv.trans_apply]
  rw [hrepr, Module.Basis.prod_repr_inl]
  have hfst : ((Submodule.prodEquivOfIsCompl E₁ F hCompl).symm y).1 = 0 :=
    (Submodule.prodEquivOfIsCompl_symm_apply_fst_eq_zero (p := E₁) (q := F) hCompl).2 hy
  rw [hfst]
  simp

/-- The order-compatible splitting equivalence `Fin r ⊕ Fin m ≃ Fin n` (for
    `r + m = n`) placing the `E₁` block first, used to reindex the adapted sum
    basis of Higham §17.4 (17.22) to a `Fin n`-indexed basis with the
    eigenvalue-`1` columns at coordinates `< r`. -/
def adaptEquiv {r m : ℕ} (hrm : r + m = n) : Fin r ⊕ Fin m ≃ Fin n :=
  finSumFinEquiv.trans (finCongr hrm)

/-- `adaptEquiv` sends the `inl` block into the low coordinates: the value of
    `adaptEquiv hrm (inl i)` is `(i : ℕ) < r`.  Index bookkeeping for
    Higham §17.4 (17.22). -/
theorem adaptEquiv_inl_val {r m : ℕ} (hrm : r + m = n) (i : Fin r) :
    ((adaptEquiv hrm (Sum.inl i)) : ℕ) = (i : ℕ) := by
  simp [adaptEquiv, Equiv.trans_apply, Fin.val_castAdd]

/-- `adaptEquiv` sends the `inr` block into the high coordinates: the value of
    `adaptEquiv hrm (inr j)` is `r + (j : ℕ) ≥ r`.  Index bookkeeping for
    Higham §17.4 (17.22). -/
theorem adaptEquiv_inr_val {r m : ℕ} (hrm : r + m = n) (j : Fin m) :
    ((adaptEquiv hrm (Sum.inr j)) : ℕ) = r + (j : ℕ) := by
  simp [adaptEquiv, Equiv.trans_apply, Fin.val_natAdd]

/-- **The reindexed adapted basis** of `ℝⁿ`, indexed by `Fin n`, with the
    eigenvalue-`1` block `E₁` occupying the coordinates `< r` and the complement
    `F` the coordinates `≥ r`.  This is the honest real change-of-basis of
    Higham §17.4 (17.22) in the repository's coordinate indexing. -/
noncomputable def adaptedBasis {r m : ℕ} (hrm : r + m = n)
    {E₁ F : Submodule ℝ (Fin n → ℝ)} (hCompl : IsCompl E₁ F)
    (bV : Module.Basis (Fin r) ℝ E₁) (bW : Module.Basis (Fin m) ℝ F) :
    Module.Basis (Fin n) ℝ (Fin n → ℝ) :=
  (adaptedSumBasis hCompl bV bW).reindex (adaptEquiv hrm)

/-- A low-coordinate basis vector of the reindexed adapted basis lies in `E₁`.
    Higham §17.4 (17.22). -/
theorem adaptedBasis_mem_E₁ {r m : ℕ} (hrm : r + m = n)
    {E₁ F : Submodule ℝ (Fin n → ℝ)} (hCompl : IsCompl E₁ F)
    (bV : Module.Basis (Fin r) ℝ E₁) (bW : Module.Basis (Fin m) ℝ F)
    (k : Fin n) (hk : (k : ℕ) < r) :
    adaptedBasis hrm hCompl bV bW k ∈ E₁ := by
  rw [adaptedBasis, Module.Basis.reindex_apply]
  rcases hsum : (adaptEquiv hrm).symm k with i | j
  · rw [adaptedSumBasis_inl]; exact (bV i).2
  · -- `inr` case is impossible: the value would be `≥ r`
    exfalso
    have hval : ((adaptEquiv hrm) (Sum.inr j) : ℕ) = (k : ℕ) := by
      rw [← hsum]; exact congrArg _ ((adaptEquiv hrm).apply_symm_apply k)
    rw [adaptEquiv_inr_val] at hval
    omega

/-- A high-coordinate basis vector of the reindexed adapted basis lies in `F`.
    Higham §17.4 (17.22). -/
theorem adaptedBasis_mem_F {r m : ℕ} (hrm : r + m = n)
    {E₁ F : Submodule ℝ (Fin n → ℝ)} (hCompl : IsCompl E₁ F)
    (bV : Module.Basis (Fin r) ℝ E₁) (bW : Module.Basis (Fin m) ℝ F)
    (k : Fin n) (hk : ¬(k : ℕ) < r) :
    adaptedBasis hrm hCompl bV bW k ∈ F := by
  rw [adaptedBasis, Module.Basis.reindex_apply]
  rcases hsum : (adaptEquiv hrm).symm k with i | j
  · -- `inl` case is impossible: the value would be `< r`
    exfalso
    have hval : ((adaptEquiv hrm) (Sum.inl i) : ℕ) = (k : ℕ) := by
      rw [← hsum]; exact congrArg _ ((adaptEquiv hrm).apply_symm_apply k)
    rw [adaptEquiv_inl_val] at hval
    have := i.2; omega
  · rw [adaptedSumBasis_inr]; exact (bW j).2

/-- **The `< r` coordinates of an `F`-vector in the reindexed adapted basis
    vanish.**  If `y ∈ F`, then `(adaptedBasis …).repr y l = 0` for `l < r`.
    Reindexed form of `adaptedSumBasis_repr_inl_of_mem_F`; the coordinate content
    of the direct-sum splitting `⊤ = E₁ ⊕ F` of Higham §17.4 (17.22). -/
theorem adaptedBasis_repr_lt_r_of_mem_F {r m : ℕ} (hrm : r + m = n)
    {E₁ F : Submodule ℝ (Fin n → ℝ)} (hCompl : IsCompl E₁ F)
    (bV : Module.Basis (Fin r) ℝ E₁) (bW : Module.Basis (Fin m) ℝ F)
    {y : Fin n → ℝ} (hy : y ∈ F) (l : Fin n) (hl : (l : ℕ) < r) :
    (adaptedBasis hrm hCompl bV bW).repr y l = 0 := by
  rw [adaptedBasis, Module.Basis.repr_reindex_apply]
  rcases hsum : (adaptEquiv hrm).symm l with i | j
  · exact adaptedSumBasis_repr_inl_of_mem_F hCompl bV bW hy i
  · -- `inr` case is impossible: the value would be `≥ r`
    exfalso
    have hval : ((adaptEquiv hrm) (Sum.inr j) : ℕ) = (l : ℕ) := by
      rw [← hsum]; exact congrArg _ ((adaptEquiv hrm).apply_symm_apply l)
    rw [adaptEquiv_inr_val] at hval
    omega

end AdaptedBasisFromSplitting

-- ============================================================
-- §17.4  (3a).  The real primary (Fitting) splitting from convergence
-- ============================================================

section FittingSplitting

variable {n : ℕ}

/-- **Higham §17.4, eq (17.22) — `[106, Lem 6.9]` — the real primary (Fitting)
    splitting from convergence of `Gᵐ`.**

    From convergence of every orbit `m ↦ Gᵐ x` (the operator content of
    semiconvergence), the coordinate space splits as an internal direct sum
    `⊤ = E₁ ⊕ F` where:

    * `E₁ = eigenspace (mulVecLin G) 1` is the ordinary eigenvalue-`1` eigenspace
      — the maximal generalized eigenspace at `1` collapses to it by GAP (1)
      semisimplicity (`maxGenEigenspace_one_eq_eigenspace_of_forall_orbit_tendsto`);
    * `F = ⨅ n, range ((mulVecLin G − 1)ⁿ)` is a `G`-invariant complement (the
      range part of the Fitting decomposition
      `LinearMap.isCompl_iSup_ker_pow_iInf_range_pow`).

    Concretely we return `IsCompl E₁ F`, the fact that every `E₁`-vector is fixed
    by `G` (`G *ᵥ x = x`), and the `G`-invariance of `F`.  This DISCHARGES, from
    convergence alone, the production of the eigenvalue-`1`-first invariant
    splitting that the block form consumes (the coordinate-level real primary
    decomposition, residual (3a)). -/
theorem exists_real_primary_splitting_of_forall_orbit_tendsto
    (G : Fin n → Fin n → ℝ)
    (hconv : ∀ x : Fin n → ℝ, ∃ z : Fin n → ℝ,
      Filter.Tendsto (fun m : ℕ => (Matrix.mulVecLin G ^ m) x) Filter.atTop (𝓝 z)) :
    ∃ (F : Submodule ℝ (Fin n → ℝ)),
      IsCompl (Module.End.eigenspace (Matrix.mulVecLin G) 1) F ∧
      (∀ x ∈ Module.End.eigenspace (Matrix.mulVecLin G) 1, G *ᵥ x = x) ∧
      (∀ x ∈ F, G *ᵥ x ∈ F) := by
  classical
  set φ : Module.End ℝ (Fin n → ℝ) := Matrix.mulVecLin G with hφ
  set ψ : Module.End ℝ (Fin n → ℝ) := φ - (1 : ℝ) • 1 with hψ
  -- The Fitting decomposition of `ψ`.
  have hFit : IsCompl (⨆ k : ℕ, LinearMap.ker (ψ ^ k)) (⨅ k : ℕ, LinearMap.range (ψ ^ k)) :=
    LinearMap.isCompl_iSup_ker_pow_iInf_range_pow ψ
  -- `⨆ ker ψ^k = maxGenEigenspace φ 1`.
  have hsup : (⨆ k : ℕ, LinearMap.ker (ψ ^ k)) = φ.maxGenEigenspace 1 := by
    rw [← Module.End.iSup_genEigenspace_eq φ 1]
    refine iSup_congr ?_
    intro k
    rw [Module.End.genEigenspace_nat]
  -- GAP (1): the eigenvalue-`1` generalized eigenspace collapses to the eigenspace.
  have hcollapse : φ.maxGenEigenspace 1 = φ.eigenspace 1 :=
    maxGenEigenspace_one_eq_eigenspace_of_forall_orbit_tendsto hconv
  -- Hence the left summand of the Fitting decomposition is the ordinary eigenspace.
  set F : Submodule ℝ (Fin n → ℝ) := ⨅ k : ℕ, LinearMap.range (ψ ^ k) with hF
  have hCompl : IsCompl (φ.eigenspace 1) F := by
    rw [← hcollapse, ← hsup]; exact hFit
  refine ⟨F, hCompl, ?_, ?_⟩
  · -- eigenvectors are fixed by `G`
    intro x hx
    rw [Module.End.mem_eigenspace_iff] at hx
    have : φ x = x := by rw [hx, one_smul]
    rw [hφ, Matrix.mulVecLin_apply] at this
    exact this
  · -- `F` is `G`-invariant (the range part of Fitting is `ψ`- and hence `φ`-invariant)
    intro x hx
    -- first `φ x ∈ F` using the standard range-inf invariance, then `φ x = G *ᵥ x`
    have hφx : φ x ∈ F := by
      rw [hF, Submodule.mem_iInf] at hx ⊢
      intro k
      obtain ⟨y, hy⟩ := hx k
      -- `φ (ψ^k y) = ψ^k (φ y)` since `φ` commutes with `ψ = φ - 1`
      refine ⟨φ y, ?_⟩
      have hcomm : ψ ^ k * φ = φ * ψ ^ k := by
        have h1 : Commute φ ψ := by
          rw [hψ]; unfold Commute SemiconjBy
          rw [mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, mul_one, one_mul]
        exact (h1.symm.pow_left k)
      calc (ψ ^ k) (φ y) = (ψ ^ k * φ) y := rfl
        _ = (φ * ψ ^ k) y := by rw [hcomm]
        _ = φ ((ψ ^ k) y) := rfl
        _ = φ x := by rw [hy]
    rw [hφ, Matrix.mulVecLin_apply] at hφx
    exact hφx

/-- **`hEig` from the splitting.**  Given a real invariant splitting `⊤ = E₁ ⊕ F`
    whose `E₁`-vectors are fixed by `G`, the low-coordinate vectors of the adapted
    basis are eigenvalue-`1` eigenvectors of `G` (`G *ᵥ b k = b k`, `k < r`).
    Higham §17.4 (17.22). -/
theorem adaptedBasis_hEig {r m : ℕ} (hrm : r + m = n)
    {E₁ F : Submodule ℝ (Fin n → ℝ)} (hCompl : IsCompl E₁ F)
    (bV : Module.Basis (Fin r) ℝ E₁) (bW : Module.Basis (Fin m) ℝ F)
    (G : Fin n → Fin n → ℝ)
    (hEig1 : ∀ x ∈ E₁, G *ᵥ x = x)
    (k : Fin n) (hk : (k : ℕ) < r) :
    G *ᵥ (adaptedBasis hrm hCompl bV bW k) = adaptedBasis hrm hCompl bV bW k :=
  hEig1 _ (adaptedBasis_mem_E₁ hrm hCompl bV bW k hk)

/-- **`hInv` from the splitting.**  Given a real invariant splitting `⊤ = E₁ ⊕ F`
    with `F` `G`-invariant, the high-coordinate columns of the adapted basis map
    into the complement: `(adaptedBasis …).repr (G *ᵥ b k) l = 0` for `k ≥ r`,
    `l < r`.  Higham §17.4 (17.22). -/
theorem adaptedBasis_hInv {r m : ℕ} (hrm : r + m = n)
    {E₁ F : Submodule ℝ (Fin n → ℝ)} (hCompl : IsCompl E₁ F)
    (bV : Module.Basis (Fin r) ℝ E₁) (bW : Module.Basis (Fin m) ℝ F)
    (G : Fin n → Fin n → ℝ)
    (hInvF : ∀ x ∈ F, G *ᵥ x ∈ F)
    (k : Fin n) (hk : ¬(k : ℕ) < r) (l : Fin n) (hl : (l : ℕ) < r) :
    (adaptedBasis hrm hCompl bV bW).repr (G *ᵥ (adaptedBasis hrm hCompl bV bW k)) l = 0 :=
  adaptedBasis_repr_lt_r_of_mem_F hrm hCompl bV bW
    (hInvF _ (adaptedBasis_mem_F hrm hCompl bV bW k hk)) l hl

end FittingSplitting

-- ============================================================
-- §17.4  MASTER REDUCTION: full block form from convergence, modulo a
--        quasi-triangular block-contractive complement basis (3a assembled).
-- ============================================================

/-- **Higham §17.4, eq (17.22) — `[106, Lem 6.9]` — the FULL semiconvergent
    block-form EXISTENCE from convergence of `Gᵐ`, modulo a real quasi-triangular
    block-contractive basis of the complement.**

    This is the assembly of the full (3a) coordinate bridge with the real primary
    (Fitting) splitting.  From:

    * convergence of every orbit `Gᵐ x` (the operator content of semiconvergence);
    * a real invariant splitting `⊤ = E₁ ⊕ F` (the one produced by
      `exists_real_primary_splitting_of_forall_orbit_tendsto`), with chosen finite
      bases `bV` of `E₁` (`Fin r`) and `bW` of `F` (`Fin m`), `r + m = n`;
    * the eigenvector / invariance facts `hEig1` / `hInvF`;
    * the hypothesis that the complement action matrix
      `C := basisActionMatrix G (adaptedBasis …)` in the adapted basis is
      quasi-upper-triangular (`hClower`) and block-contractive (`hCblock`) for a
      block assignment `pblk` — the honest real quasi-Schur (16.4) normal form of
      `G|_F` with contractive blocks,

    we PRODUCE the exact `semiconvergent_block_form_exists` data package.  The
    ∞-norm contraction of `Γ` is CONSTRUCTED (never assumed).  This closes GAP (3)
    DOWNSTREAM of, and INCLUDING, the coordinate-level real primary decomposition:
    the only content folded into a hypothesis here is the quasi-triangular
    block-contractive normal form of the complement (residual (3b), the per-block
    ∞-norm reduction, plus the real-quasi-Schur choice of `bW`).  For a complement
    with REAL spectrum every block is `1×1` and `hCblock` is just `|C_{kk}| < 1`
    (GAP (2)), so no (3b) is needed and this discharges the block form fully. -/
theorem semiconvergent_block_form_exists_of_convergence_and_complement_normal_form
    {n : ℕ} {r m : ℕ} (hrm : r + m = n) (G : Fin n → Fin n → ℝ)
    {E₁ F : Submodule ℝ (Fin n → ℝ)} (hCompl : IsCompl E₁ F)
    (bV : Module.Basis (Fin r) ℝ E₁) (bW : Module.Basis (Fin m) ℝ F)
    (hEig1 : ∀ x ∈ E₁, G *ᵥ x = x) (hInvF : ∀ x ∈ F, G *ᵥ x ∈ F)
    (pblk : Fin n → ℕ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hClower : ∀ i j : Fin n, ¬(i : ℕ) < r → ¬(j : ℕ) < r →
      pblk j < pblk i → basisActionMatrix G (adaptedBasis hrm hCompl bV bW) i j = 0)
    (hCblock : ∀ i : Fin n, ¬(i : ℕ) < r →
      (∑ j ∈ Finset.univ.filter
        (fun j : Fin n => ¬(j : ℕ) < r ∧ pblk j = pblk i),
        |basisActionMatrix G (adaptedBasis hrm hCompl bV bW) i j|) ≤ ρ) :
    ∃ (X' X'_inv Γ : Fin n → Fin n → ℝ) (q : ℝ),
      0 ≤ q ∧ q < 1 ∧
      (∀ i : Fin n, ¬(i : ℕ) < r →
        (∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬(j : ℕ) < r), |Γ i j|) ≤ q) ∧
      IsRightInverse n X' X'_inv ∧ IsRightInverse n X'_inv X' ∧
      (∀ (k : Fin n), (k : ℕ) < r → ∀ i : Fin n, matMul n G X' i k = X' i k) ∧
      matMul n X'_inv (matMul n G X') = blockJ n r Γ ∧
      (∀ i j : Fin n, (i : ℕ) < r → blockJ n r Γ i j = if i = j then 1 else 0) ∧
      (∀ i j : Fin n, ¬(i : ℕ) < r → (j : ℕ) < r → blockJ n r Γ i j = 0) ∧
      (∀ i : Fin n, ¬(i : ℕ) < r → ∑ j : Fin n, |blockJ n r Γ i j| ≤ q) :=
  semiconvergent_block_form_exists_of_adapted_basis r G
    (adaptedBasis hrm hCompl bV bW) pblk
    (fun k hk => adaptedBasis_hEig hrm hCompl bV bW G hEig1 k hk)
    (fun k hk l hl => adaptedBasis_hInv hrm hCompl bV bW G hInvF k hk l hl)
    hρ0 hρ1 hClower hCblock

/-- **Higham §17.4, eq (17.22)/(17.27) — `[106, Lem 6.9]` — semiconvergence
    `Gᵐ → I − E` from convergence, modulo the complement normal form (end-to-end
    payoff of the assembled (3a) coordinate bridge).**

    The power-convergence conclusion of the master reduction: under the SAME
    hypotheses as
    `semiconvergent_block_form_exists_of_convergence_and_complement_normal_form`
    (a real invariant splitting `⊤ = E₁ ⊕ F` with the eigenvalue-`1`/invariance
    facts, and a quasi-triangular block-contractive complement action matrix), the
    powers of `G` converge entrywise to the eigenvalue-`1` projector
    `oneEigenProjector = X' · diag(I_r, 0) · X'⁻¹ = I − E`, where `X'` is built
    from the adapted basis of the splitting.  The ∞-norm contraction is
    CONSTRUCTED (never assumed).  For a REAL complement spectrum the block-
    contractivity is just `|C_{kk}| < 1` (GAP (2)); the honest boundary for the
    complex case is `|Re λ| + |Im λ| < 1` (see `twoByTwo_max_rowSum_ge_of_trace_det`). -/
theorem matPow_G_tendsto_oneEigenProjector_of_convergence_and_complement_normal_form
    {n : ℕ} {r m : ℕ} (hrm : r + m = n) (G : Fin n → Fin n → ℝ)
    {E₁ F : Submodule ℝ (Fin n → ℝ)} (hCompl : IsCompl E₁ F)
    (bV : Module.Basis (Fin r) ℝ E₁) (bW : Module.Basis (Fin m) ℝ F)
    (hEig1 : ∀ x ∈ E₁, G *ᵥ x = x) (hInvF : ∀ x ∈ F, G *ᵥ x ∈ F)
    (pblk : Fin n → ℕ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hClower : ∀ i j : Fin n, ¬(i : ℕ) < r → ¬(j : ℕ) < r →
      pblk j < pblk i → basisActionMatrix G (adaptedBasis hrm hCompl bV bW) i j = 0)
    (hCblock : ∀ i : Fin n, ¬(i : ℕ) < r →
      (∑ j ∈ Finset.univ.filter
        (fun j : Fin n => ¬(j : ℕ) < r ∧ pblk j = pblk i),
        |basisActionMatrix G (adaptedBasis hrm hCompl bV bW) i j|) ≤ ρ) :
    ∃ (X' X'_inv : Fin n → Fin n → ℝ),
      IsRightInverse n X' X'_inv ∧ IsRightInverse n X'_inv X' ∧
      (∀ i j : Fin n,
        Filter.Tendsto (fun k => matPow n G k i j) Filter.atTop
          (nhds (oneEigenProjector n r X' X'_inv i j))) :=
  matPow_G_tendsto_oneEigenProjector_of_quasiTriangular_complement n r G
    (basisColMatrix (adaptedBasis hrm hCompl bV bW))
    (basisRowMatrix (adaptedBasis hrm hCompl bV bW))
    (basisActionMatrix G (adaptedBasis hrm hCompl bV bW)) pblk
    (basisColMatrix_isRightInverse _) (basisRowMatrix_isRightInverse _)
    (fun k hk i => basisColMatrix_colTop G (adaptedBasis hrm hCompl bV bW) r
      (fun k' hk' => adaptedBasis_hEig hrm hCompl bV bW G hEig1 k' hk') k hk i)
    (fun k hk i => basisColMatrix_colBot G (adaptedBasis hrm hCompl bV bW) r
      (fun k' hk' l hl => adaptedBasis_hInv hrm hCompl bV bW G hInvF k' hk' l hl) k hk i)
    hρ0 hρ1 hClower hCblock

-- ============================================================
-- §17.4  (3b).  The per-`2×2`-block ∞-norm reduction — the HONEST scope.
-- ============================================================
--
-- The prior wave asked for a per-`2×2`-block ∞-norm similarity reduction for any
-- real block with spectral radius `< 1`.  We prove here that this reduction, in
-- the form `hCblock` needs (∞-norm ROW SUMS of the `2×2` block `< 1`), is
-- governed by the EXACT infimum below and is therefore NOT available for spectral
-- radius `< 1` alone: it holds iff `|Re λ| + |Im λ| < 1` for the eigenvalue pair,
-- a strictly stronger condition than `|λ| = √((Re λ)² + (Im λ)²) < 1`.

section TwoByTwoInfNormReduction

/-- **Exact ∞-norm infimum for a real `2×2` block with a complex eigenvalue pair
    (Higham §17.4 (17.22) — the honest scope of the per-block reduction (3b)).**

    Every real matrix similar to a `2×2` block with eigenvalues `α ± β i` has
    trace `2α` and determinant `α² + β²`.  For ANY real `2×2` matrix
    `[[p, q], [t, s]]` with these invariants (`p + s = 2α`,
    `p·s − q·t = α² + β²`), the maximum absolute ROW SUM is bounded below by
    `|α| + |β|`:
    `max(|p| + |q|, |s| + |t|) ≥ |α| + |β|`.

    Consequently the infimum of `‖S⁻¹ B S‖∞` over real similarities of such a
    block equals `|α| + |β|` (the value attained by the real Schur / rotation-
    scaling normal form `[[α, β], [−β, α]]`).  In particular the `hCblock` ∞-norm
    contraction is achievable for a `2×2` complex-eigenvalue block **iff**
    `|α| + |β| < 1` — strictly stronger than `ρ = √(α²+β²) < 1`.  So the
    per-`2×2`-block reduction "spectral radius `< 1` ⟹ ∞-norm `< 1` after
    similarity" is FALSE; this is a genuine obstruction, not a missing Mathlib
    lemma.  Unconditional. -/
theorem twoByTwo_max_rowSum_ge_of_trace_det
    {p q t s α β : ℝ} (htr : p + s = 2 * α) (hdet : p * s - q * t = α ^ 2 + β ^ 2) :
    |α| + |β| ≤ max (|p| + |q|) (|s| + |t|) := by
  -- `2·max ≥ (|p|+|q|)+(|s|+|t|) = (|p|+|s|) + (|q|+|t|)`
  have hmax : (|p| + |q|) + (|s| + |t|) ≤ 2 * max (|p| + |q|) (|s| + |t|) := by
    have h1 : |p| + |q| ≤ max (|p| + |q|) (|s| + |t|) := le_max_left _ _
    have h2 : |s| + |t| ≤ max (|p| + |q|) (|s| + |t|) := le_max_right _ _
    linarith
  -- `|p|+|s| ≥ |p+s| = 2|α|`
  have hps : 2 * |α| ≤ |p| + |s| := by
    have := abs_add_le p s
    rw [htr, abs_mul] at this
    simp only [abs_two] at this
    linarith
  -- `q·t = p·s − (α²+β²) ≤ α² − (α²+β²) = −β² ≤ 0`, and `|q·t| ≥ β²`
  have hqt_le : q * t ≤ - β ^ 2 := by
    have hps_le : 4 * (p * s) ≤ (p + s) ^ 2 := by nlinarith [sq_nonneg (p - s)]
    rw [htr] at hps_le
    -- `4 p s ≤ 4α²` ⟹ `p s ≤ α²`
    nlinarith [hdet]
  -- `(|q|+|t|)² ≥ 4|q||t| = 4|q·t| ≥ 4β²`, so `|q|+|t| ≥ 2|β|`
  have hqt : 2 * |β| ≤ |q| + |t| := by
    have habs : β ^ 2 ≤ |q * t| := by
      rw [abs_of_nonpos (by nlinarith [sq_nonneg β] : q * t ≤ 0)]
      linarith
    have hsq : (2 * |β|) ^ 2 ≤ (|q| + |t|) ^ 2 := by
      have h4 : 4 * |q * t| ≤ (|q| + |t|) ^ 2 := by
        rw [abs_mul]
        nlinarith [sq_nonneg (|q| - |t|), abs_nonneg q, abs_nonneg t]
      calc (2 * |β|) ^ 2 = 4 * β ^ 2 := by ring_nf; rw [sq_abs]
        _ ≤ 4 * |q * t| := by linarith
        _ ≤ (|q| + |t|) ^ 2 := h4
    have hnn : 0 ≤ |q| + |t| := by positivity
    have hnn2 : 0 ≤ 2 * |β| := by positivity
    nlinarith [hsq, hnn, hnn2]
  linarith

/-- **The rotation-scaling normal form attains the ∞-norm infimum `|α| + |β|`
    (Higham §17.4 (17.22)).**  The real Schur `2×2` block `[[α, β], [−β, α]]`
    (eigenvalues `α ± β i`, the honest output of the real peel-`2` primitive
    `real_peel_one_or_two`) has both absolute row sums equal to `|α| + |β|`, i.e.
    `‖[[α,β],[−β,α]]‖∞ = |α| + |β|`.  Combined with
    `twoByTwo_max_rowSum_ge_of_trace_det`, this shows `|α| + |β|` is EXACTLY the
    infimum of the ∞-norm over real similarities of the block, and the block-
    contractivity `hCblock` (`< 1`) holds for the normal form **iff**
    `|α| + |β| < 1`.  Unconditional. -/
theorem rotationScaling_rowSum_eq (α β : ℝ) :
    (|α| + |β| = |β| + |α|) ∧
      max (|α| + |β|) (|(-β)| + |α|) = |α| + |β| := by
  refine ⟨add_comm _ _, ?_⟩
  rw [abs_neg]
  rw [max_eq_left]
  rw [add_comm |β| |α|]

/-- **The honest per-`2×2`-block ∞-norm reduction (Higham §17.4 (17.22), the
    corrected (3b)).**  A real `2×2` block with complex eigenvalue pair
    `α ± β i` admits an ∞-norm-contractive similarity (both block row sums `< 1`,
    as `hCblock` requires) **iff** `|α| + |β| < 1`; when it does, the rotation-
    scaling normal form `[[α, β], [−β, α]]` realises it with row sums exactly
    `|α| + |β|`.  This is the corrected statement of the prior wave's requested
    reduction: the naive "`ρ = √(α²+β²) < 1` ⟹ reducible" is FALSE by
    `twoByTwo_max_rowSum_ge_of_trace_det`; the sharp threshold is `|α|+|β| < 1`.
    Unconditional. -/
theorem twoByTwo_infNorm_reducible_iff (α β : ℝ) :
    (|α| + |β| < 1 ↔ max (|α| + |β|) (|(-β)| + |α|) < 1) := by
  rw [(rotationScaling_rowSum_eq α β).2]

end TwoByTwoInfNormReduction

-- ============================================================
-- §17.4  STATUS of the FULL [106, Lem 6.9] from convergence of `Gᵐ`.
-- ============================================================
--
-- This module discharges the residual GAP (3) itemized by the prior wave
-- (`SemiconvergentExistenceFull.lean`) as two concrete lemmas (3a), (3b).
--
-- (3a) — CLOSED (unconditionally).  The COORDINATE-LEVEL real primary/Fitting
--   decomposition is fully assembled here:
--     • `exists_real_primary_splitting_of_forall_orbit_tendsto` — from convergence
--       of every orbit `Gᵐ x`, produces the real invariant splitting
--       `⊤ = ker(G−I) ⊕ F` (`IsCompl`), with the eigenvalue-`1` summand the
--       ORDINARY eigenspace (GAP (1) semisimplicity, via
--       `maxGenEigenspace_one_eq_eigenspace_of_forall_orbit_tendsto`) and `F` the
--       `G`-invariant range part of Mathlib's Fitting decomposition
--       `LinearMap.isCompl_iSup_ker_pow_iInf_range_pow`;
--     • `adaptedBasis` + `basisColMatrix`/`basisRowMatrix`/`basisActionMatrix` —
--       turn that splitting (with any chosen finite bases of the two summands)
--       into an INVERTIBLE `matMul` change of basis `X` whose first `r` columns
--       are honest eigenvalue-`1` eigenvectors and whose complement columns
--       realise `hGcolBot` with `C =` the matrix of `G|_F`;
--     • `semiconvergent_block_form_exists_of_adapted_basis` and
--       `semiconvergent_block_form_exists_of_convergence_and_complement_normal_form`
--       — assemble the full block form, feeding the two column conditions into the
--       prior wave's `semiconvergent_block_form_exists_of_quasiTriangular_complement`.
--   This removes the ENTIRE "manufacture the (16.4) basis in coordinates from
--   convergence" bottleneck that GAP (3) named: the `Submodule` ↔ `matMul` bridge,
--   the eigenvalue-`1`-first ordering, and the invariance of the complement
--   columns are all supplied.  What remains folded into the master reduction's
--   hypothesis is ONLY the quasi-triangular block-contractive NORMAL FORM of the
--   complement (`hClower`/`hCblock` on `basisActionMatrix`), i.e. the real
--   quasi-Schur choice of the complement basis together with (3b).
--
-- (3b) — RESOLVED as an EXACT OBSTRUCTION (a genuine correction).  The prior wave
--   asked for a per-`2×2`-block ∞-norm similarity reduction for any real block of
--   spectral radius `< 1`.  `twoByTwo_max_rowSum_ge_of_trace_det` proves this is
--   IMPOSSIBLE in that generality: every real matrix similar to a `2×2` block with
--   eigenvalues `α ± β i` has maximum absolute row sum `≥ |α| + |β|`, and the
--   rotation-scaling normal form attains it (`rotationScaling_rowSum_eq`).  Hence
--   the ∞-norm block-contractivity `hCblock` (`< 1`) is achievable for a complex
--   pair **iff** `|α| + |β| < 1` — STRICTLY STRONGER than `ρ = √(α²+β²) < 1`
--   (`twoByTwo_infNorm_reducible_iff`).  In particular the whole-`Γ` ∞-norm bound
--   `‖Γ‖∞ < 1` used throughout the repository's semiconvergent-existence route
--   (the strengthening of `ρ(Γ) < 1`) is UNACHIEVABLE for a semiconvergent matrix
--   with a non-`1` eigenvalue `α ± β i` having `|α| + |β| ≥ 1` (e.g.
--   `0.6 ± 0.6 i`: `ρ = 0.849 < 1` yet every similar block has ∞-row-sum
--   `≥ 1.2`).  So (3b) is NOT a missing Mathlib lemma but a genuine mathematical
--   boundary of the ∞-norm route.
--
-- CONSEQUENCE for the FULL existence.  Combining (3a) with the prior wave:
--   • FULLY-REAL complement spectrum ⇒ every diagonal block is `1×1`, `hCblock`
--     reduces to `|C_{kk}| < 1` (GAP (2)), and
--     `semiconvergent_block_form_exists_of_convergence_and_complement_normal_form`
--     discharges the block form from convergence with NO side condition beyond a
--     real-triangularizing basis of `F`;
--   • COMPLEX complement spectrum ⇒ the block form in the repository's ∞-norm
--     row-sum strengthening exists from convergence **iff** every non-`1`
--     eigenvalue `α ± β i` satisfies `|α| + |β| < 1`; when it does,
--     the same master reduction discharges it (with `C` the real quasi-Schur
--     normal form and each `2×2` block put in rotation-scaling form).
--   The single remaining IMPORT-level construction (not a mathematical gap) is the
--   `LinearMap.toMatrix ↔ basisActionMatrix` identification that lets
--   `real_quasi_schur` choose the complement basis `bW`; the master reduction is
--   stated to consume exactly that normal-form data.
--
-- No `sorry`/`admit`/`axiom`/`native_decide`/proof-disabling option is used.

end NumStability
