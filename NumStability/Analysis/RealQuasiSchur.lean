/-
Analysis/RealQuasiSchur.lean

The **full real quasi-triangular (quasi-)Schur decomposition**.  Higham,
*Accuracy and Stability of Numerical Algorithms*, 2nd ed., §16.2, equation
(16.4): every real square matrix `A` is orthogonally similar to a real
*block*-upper-triangular matrix `R` whose diagonal blocks have size `1` (real
eigenvalues) or `2` (complex-conjugate eigenvalue pairs):

  `∃ Q ∈ orthogonalGroup, Qᵀ A Q = R`, with `R` block-upper-triangular
  (zeros strictly below the `≤ 2` diagonal-block structure).

This closes the residual obstruction recorded at the end of
`Analysis/RealInvariantSubspace.lean`: iterating the real "peel-1-or-2" primitive
into the FULL orthogonal quasi-triangular form via the *variable-`d`*
(`d ∈ {1, 2}`) orthogonal deflation induction.

Reference: N. J. Higham, *Accuracy and Stability of Numerical Algorithms*,
2nd ed., §16.2, equation (16.4) (real Schur decomposition); the classical
statement is Golub & Van Loan, *Matrix Computations*, Theorem 7.4.1.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Matrix.Block
import NumStability.Analysis.RealInvariantSubspace

open scoped BigOperators Matrix
open Module

namespace NumStability

/-- Spectral certificates for adjacent `2 x 2` blocks in a constructed real
    quasi-Schur block map.  For every adjacent pair in the same block, the
    ordered principal block has no real eigenline, hence its discriminant is
    negative.  This is the certificate layer needed before exporting
    source-facing real `2 x 2` Schur block data from the recursive construction. -/
def HasRealQuasiSchurTwoBlockSpectral {n : ℕ}
    (R : Matrix (Fin n) (Fin n) ℝ) (pmap : Fin n → ℕ) : Prop :=
  ∀ p q : Fin n,
    (q : ℕ) = (p : ℕ) + 1 →
    pmap p = pmap q →
      MatrixNoRealEigenline (principalTwoBlock R p q) ∧
        (R p p - R q q) ^ 2 + 4 * R p q * R q p < 0

namespace RealQuasiSchurAux

/-! ### The quasi-upper-triangular predicate (Higham (16.4))

A matrix `R : Matrix (Fin n) (Fin n) ℝ` is *quasi-upper-triangular* when there is
a block-assignment `p : Fin n → ℕ` such that:
* `p` is monotone — so each block `p⁻¹(c)` is a contiguous interval;
* every block has at most `2` elements — the diagonal blocks are `1×1` or `2×2`;
* `R i j = 0` whenever row `i` lies in a strictly later block than column `j`
  (`p j < p i`) — i.e. everything strictly below the block diagonal vanishes.

This is precisely the real quasi-triangular Schur form of Higham §16.2 (16.4):
block-upper-triangular with `1×1`/`2×2` diagonal blocks.  In the degenerate case
`p = id` (all blocks of size `1`) it reduces to ordinary upper-triangularity
`R i j = 0` for `j < i`. -/
def IsQuasiUpperTriangular {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ p : Fin n → ℕ, Monotone p ∧
    (∀ c : ℕ, (Finset.univ.filter (fun i => p i = c)).card ≤ 2) ∧
    (∀ i j : Fin n, p j < p i → R i j = 0)

/-! ### Block-diagonal orthogonal re-embedding over a sum index

Re-embedding an `m×m` orthogonal matrix `U` as the trailing block of a
`(Fin d ⊕ Fin m)`-indexed matrix with an identity `d×d` leading block, used to
lift the trailing-block reduction of Higham §16.2 (16.4) to the full space. -/

variable {d m : ℕ}

/-- The block-diagonal embedding `U ↦ [[1, 0], [0, U]]` over the sum index
    `Fin d ⊕ Fin m`.  Companion to the `embed` of `RealSchurTriangulation.lean`,
    generalised to a `d`-dimensional leading identity block for the variable-`d`
    deflation of Higham §16.2 (16.4). -/
def embedBlock (U : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ :=
  Matrix.fromBlocks 1 0 0 U

/-- Transpose commutes with the block-diagonal embedding of Higham §16.2 (16.4). -/
@[simp] lemma embedBlock_transpose (U : Matrix (Fin m) (Fin m) ℝ) :
    (embedBlock (d := d) U)ᵀ = embedBlock (Uᵀ) := by
  unfold embedBlock
  rw [Matrix.fromBlocks_transpose]
  simp

/-- The block-diagonal embedding of Higham §16.2 (16.4) sends the identity to the
    identity. -/
lemma embedBlock_one : embedBlock (d := d) (1 : Matrix (Fin m) (Fin m) ℝ) = 1 := by
  unfold embedBlock; rw [Matrix.fromBlocks_one]

/-- The block-diagonal embedding of Higham §16.2 (16.4) is multiplicative. -/
lemma embedBlock_mul (U V : Matrix (Fin m) (Fin m) ℝ) :
    embedBlock (d := d) U * embedBlock (d := d) V = embedBlock (d := d) (U * V) := by
  unfold embedBlock
  rw [Matrix.fromBlocks_multiply]
  simp

/-- The block-diagonal embedding of an orthogonal matrix is orthogonal. -/
lemma embedBlock_mem_orthogonal {U : Matrix (Fin m) (Fin m) ℝ}
    (hU : U ∈ Matrix.orthogonalGroup (Fin m) ℝ) :
    embedBlock (d := d) U ∈ Matrix.orthogonalGroup (Fin d ⊕ Fin m) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff']
  rw [embedBlock_transpose, embedBlock_mul]
  rw [Matrix.mem_orthogonalGroup_iff'] at hU
  rw [hU, embedBlock_one]

/-! ### Deflation: an invariant leading block zeros the lower-left block

If the first `d` columns of an orthogonal `Q` span an `A`-invariant subspace,
then conjugating `A` by `Q` zeros the block strictly below those columns. -/

variable {n : ℕ}

/-- The `(i,j)` entry of `Qᵀ * A * Q` is the euclidean dot product of column `i`
    of `Q` with `A` applied to column `j` of `Q`.  Matrix-level restatement used
    for the deflation of Higham §16.2 (16.4). -/
lemma conj_entry_eq_dotProduct (A Q : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (Qᵀ * A * Q) i j
      = (fun k => Q k i) ⬝ᵥ (A *ᵥ (fun k => Q k j)) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct]
  -- LHS: ∑ x, (∑ x_1, Q x_1 i * A x_1 x) * Q x j ;  RHS: ∑ x, Q x i * ∑ x_1, A x x_1 * Q x_1 j
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- Orthonormality of the columns of an orthogonal matrix: the dot product of
    column `i` with column `j` is `1` if `i = j` and `0` otherwise.  Used for the
    deflation of Higham §16.2 (16.4). -/
lemma orthogonal_col_dotProduct {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin n) ℝ) (i j : Fin n) :
    (fun k => Q k i) ⬝ᵥ (fun k => Q k j) = if i = j then 1 else 0 := by
  rw [Matrix.mem_orthogonalGroup_iff'] at hQ
  have := congrFun (congrFun hQ i) j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at this
  rw [dotProduct]
  simpa using this

/-- **Variable-`d` deflation zero block.**  If the first `d` columns of an
    orthogonal `Q` span a subspace `W`, and `A *ᵥ (column j of Q) ∈ W` for every
    `j < d` (i.e. `W` is `A`-invariant), then `(Qᵀ A Q) i j = 0` whenever `i ≥ d`
    and `j < d`: the block strictly below the leading `d` columns is zero.  This
    is the deflation step behind the `2×2` (or `1×1`) blocks of Higham
    §16.2 (16.4). -/
lemma deflation_lower_left_zero (A Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin n) ℝ) (d : ℕ)
    (hinv : ∀ j : Fin n, (j : ℕ) < d →
      (A *ᵥ (fun k => Q k j)) ∈
        Submodule.span ℝ (Set.range (fun c : {c : Fin n // (c : ℕ) < d} => (fun k => Q k c.1))))
    (i j : Fin n) (hi : d ≤ (i : ℕ)) (hj : (j : ℕ) < d) :
    (Qᵀ * A * Q) i j = 0 := by
  rw [conj_entry_eq_dotProduct]
  -- The linear functional `u ↦ (col i) ⬝ᵥ u` vanishes on `W`, and `A (col j) ∈ W`.
  -- `col i` is orthogonal to every generator `col c` (`c < d`) since `i ≥ d > c ≥ 0` so `i ≠ c`.
  set coli : Fin n → ℝ := fun k => Q k i with hcoli
  -- the functional as a linear map
  have hfun : ∀ u ∈ Submodule.span ℝ
      (Set.range (fun c : {c : Fin n // (c : ℕ) < d} => (fun k => Q k c.1))),
      coli ⬝ᵥ u = 0 := by
    intro u hu
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨c, rfl⟩
      rw [hcoli, orthogonal_col_dotProduct hQ]
      have hne : i ≠ c.1 := by
        intro h; rw [h] at hi; exact absurd c.2 (not_lt.mpr hi)
      simp [hne]
    · simp
    · intro x y _ _ hx hy; rw [dotProduct_add, hx, hy, add_zero]
    · intro a x _ hx; rw [dotProduct_smul, hx, smul_zero]
  exact hfun _ (hinv j hj)

/-! ### Orthogonal frame whose leading `d` columns span the invariant subspace

From a `d`-dimensional real invariant subspace `W` we build an orthogonal `Q`
whose first `d` columns form an orthonormal basis of `W`; this is the orthonormal
extension `Orthonormal.exists_orthonormalBasis_extension_of_card_eq` that the
variable-`d` deflation of Higham §16.2 (16.4) consumes. -/

/-- The `EuclideanSpace ↔ (Fin n → ℝ)` linear equiv (the identity on the
    underlying module), used to move a real invariant subspace of Higham
    §16.2 (16.4) between the coordinate space and its `ℓ²` (euclidean) copy. -/
noncomputable def euclEquiv (n : ℕ) : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] (Fin n → ℝ) :=
  WithLp.linearEquiv 2 ℝ (Fin n → ℝ)

/-- The equiv `euclEquiv` of Higham §16.2 (16.4) acts as the identity on entries. -/
@[simp] lemma euclEquiv_apply (n : ℕ) (w : EuclideanSpace ℝ (Fin n)) (k : Fin n) :
    euclEquiv n w k = w k := rfl

/-- The inverse of `euclEquiv` (Higham §16.2 (16.4)) acts as the identity on
    entries. -/
lemma euclEquiv_symm_apply (n : ℕ) (w : Fin n → ℝ) (k : Fin n) :
    (euclEquiv n).symm w k = w k := rfl

/-- **Orthogonal frame extension.**  Given a real invariant subspace `W` of the
    coordinate space of finrank `d ≤ n`, there is an orthogonal matrix `Q` whose
    first `d` columns (indexed by `{c : Fin n // c < d}`) form an orthonormal
    basis of `W`: they all lie in `W` and their span is `W`.  This packages the
    orthonormal-basis extension behind the variable-`d` deflation of Higham
    §16.2 (16.4). -/
lemma exists_orthogonal_frame (W : Submodule ℝ (Fin n → ℝ)) (d : ℕ)
    (hd : finrank ℝ W = d) :
    ∃ Q : Matrix (Fin n) (Fin n) ℝ, Q ∈ Matrix.orthogonalGroup (Fin n) ℝ ∧
      (∀ c : {c : Fin n // (c : ℕ) < d}, (fun k => Q k c.1) ∈ W) ∧
      Submodule.span ℝ
        (Set.range (fun c : {c : Fin n // (c : ℕ) < d} => (fun k => Q k c.1))) = W := by
  classical
  -- `W` as a submodule of the euclidean space
  set WE : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
    W.comap (euclEquiv n).toLinearMap with hWE
  have hdE : finrank ℝ WE = d := by
    rw [hWE, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq, hd]
  have hdn : d ≤ n := by
    have hle : finrank ℝ WE ≤ finrank ℝ (EuclideanSpace ℝ (Fin n)) := Submodule.finrank_le WE
    rw [hdE] at hle; simpa using hle
  -- orthonormal basis of `WE`, indexed by `Fin d`
  set bW : OrthonormalBasis (Fin d) ℝ WE :=
    (stdOrthonormalBasis ℝ WE).reindex (finCongr hdE) with hbW
  -- the family to extend: `v i = ↑(bW ⟨i,·⟩)` on `s`, else `0`
  set s : Set (Fin n) := {i : Fin n | (i : ℕ) < d} with hs
  set v : Fin n → EuclideanSpace ℝ (Fin n) :=
    fun i => if h : (i : ℕ) < d then ((bW ⟨(i : ℕ), h⟩ : WE) : EuclideanSpace ℝ (Fin n)) else 0
    with hv
  have hcard : finrank ℝ (EuclideanSpace ℝ (Fin n)) = Fintype.card (Fin n) := by simp
  -- `s.restrict v` is orthonormal
  have horth : Orthonormal ℝ (s.restrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi_mem⟩ ⟨j, hj_mem⟩
    have hi : (i : ℕ) < d := hi_mem
    have hj : (j : ℕ) < d := hj_mem
    simp only [Set.restrict_apply, hv, dif_pos hi, dif_pos hj]
    rw [← Submodule.coe_inner, orthonormal_iff_ite.mp bW.orthonormal]
    have hiff : ((⟨(i : ℕ), hi⟩ : Fin d) = ⟨(j : ℕ), hj⟩)
        ↔ ((⟨i, hi_mem⟩ : ↥s) = ⟨j, hj_mem⟩) := by
      rw [Fin.mk.injEq, Subtype.mk.injEq, Fin.val_eq_val]
    by_cases hcase : (⟨i, hi_mem⟩ : ↥s) = ⟨j, hj_mem⟩
    · rw [if_pos hcase, if_pos (hiff.mpr hcase)]
    · rw [if_neg hcase, if_neg (fun h => hcase (hiff.mp h))]
  -- extend to an orthonormal basis of the whole space
  obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq hcard
  -- the matrix
  set Q : Matrix (Fin n) (Fin n) ℝ :=
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.toMatrix b.toBasis with hQdef
  refine ⟨Q,
    (EuclideanSpace.basisFun (Fin n) ℝ).toMatrix_orthonormalBasis_mem_orthogonal b, ?_, ?_⟩
  · -- membership: column `c` is in `W`
    rintro ⟨c, hc⟩
    have hcol : (fun k => Q k c)
        = fun k => (b c : EuclideanSpace ℝ (Fin n)) k := by
      funext k
      rw [hQdef, Module.Basis.toMatrix_apply]
      simp [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_repr]
    rw [hcol]
    have hbc : b c = v c := hb c (by simp [hs, hc])
    rw [hbc]
    simp only [hv, dif_pos hc]
    -- `↑(bW ⟨c,·⟩) ∈ WE`, so `euclEquiv (↑(bW⟨c,·⟩)) ∈ W`
    have hmemWE : ((bW ⟨(c : ℕ), hc⟩ : WE) : EuclideanSpace ℝ (Fin n)) ∈ WE :=
      (bW ⟨(c : ℕ), hc⟩).2
    have : ((bW ⟨(c : ℕ), hc⟩ : WE) : EuclideanSpace ℝ (Fin n)) ∈
        W.comap (euclEquiv n).toLinearMap := hmemWE
    rw [Submodule.mem_comap] at this
    exact this
  · -- span: the first `d` columns span `W`
    -- Each generator equals `euclEquiv n (↑(bW ⟨c,·⟩))`.
    have hgen : ∀ c : {c : Fin n // (c : ℕ) < d},
        (fun k => Q k c.1)
          = (euclEquiv n) ((bW ⟨(c.1 : ℕ), c.2⟩ : WE) : EuclideanSpace ℝ (Fin n)) := by
      rintro ⟨c, hc⟩
      funext k
      rw [hQdef, Module.Basis.toMatrix_apply]
      have hbc : b c = v c := hb c (by simp [hs, hc])
      simp only [OrthonormalBasis.coe_toBasis, hbc, hv, dif_pos hc]
      rfl
    -- rewrite the range of generators as an image
    have hrange : (Set.range (fun c : {c : Fin n // (c : ℕ) < d} => (fun k => Q k c.1)))
        = ⇑(euclEquiv n) ''
          (Set.range (fun c' : Fin d => (bW c' : EuclideanSpace ℝ (Fin n)))) := by
      ext z
      simp only [Set.mem_range, Set.mem_image]
      constructor
      · rintro ⟨⟨c, hc⟩, rfl⟩
        exact ⟨(bW ⟨(c : ℕ), hc⟩ : EuclideanSpace ℝ (Fin n)), ⟨⟨(c : ℕ), hc⟩, rfl⟩,
          (hgen ⟨c, hc⟩).symm⟩
      · rintro ⟨w, ⟨c', rfl⟩, rfl⟩
        refine ⟨⟨Fin.castLE hdn c', by simp [c'.2]⟩, ?_⟩
        rw [hgen ⟨Fin.castLE hdn c', by simp [c'.2]⟩]
        congr 2
    rw [hrange, Submodule.span_image_linearEquiv]
    -- `span (range (↑ ∘ bW)) = WE`, then `map euclEquiv WE = W`
    have hbWspan : Submodule.span ℝ
        (Set.range (fun c' : Fin d => (bW c' : EuclideanSpace ℝ (Fin n)))) = WE := by
      have h1 : (Set.range (fun c' : Fin d => (bW c' : EuclideanSpace ℝ (Fin n))))
          = WE.subtype '' (Set.range (fun c' : Fin d => bW c')) := by
        rw [← Set.range_comp]; rfl
      rw [h1, Submodule.span_image]
      have h2 : Submodule.span ℝ (Set.range (fun c' : Fin d => bW c')) = ⊤ := by
        have := bW.toBasis.span_eq
        rwa [OrthonormalBasis.coe_toBasis] at this
      rw [h2, Submodule.map_subtype_top]
    rw [hbWspan, hWE, Submodule.map_comap_eq_self]
    rw [LinearMap.range_eq_top_of_surjective _ (euclEquiv n).surjective]
    exact le_top

lemma eq_zero_of_mem_span_pair_orthogonal_cols_dot_eq_zero
    {Q : Matrix (Fin n) (Fin n) ℝ} {p q : Fin n}
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin n) ℝ) (hpq : p ≠ q)
    {v : Fin n → ℝ}
    (hv : v ∈
      Submodule.span ℝ
        ({(fun k : Fin n => Q k p), (fun k : Fin n => Q k q)}
          : Set (Fin n → ℝ)))
    (hp : (fun k : Fin n => Q k p) ⬝ᵥ v = 0)
    (hq : (fun k : Fin n => Q k q) ⬝ᵥ v = 0) :
    v = 0 := by
  rcases (Submodule.mem_span_pair.mp hv) with ⟨a, b, hrepr⟩
  have ha : a = 0 := by
    have hdot :=
      congrArg (fun z : Fin n → ℝ => (fun k : Fin n => Q k p) ⬝ᵥ z) hrepr
    change (fun k : Fin n => Q k p) ⬝ᵥ
        ((a • fun k : Fin n => Q k p) + b • fun k : Fin n => Q k q) =
      (fun k : Fin n => Q k p) ⬝ᵥ v at hdot
    rw [hp] at hdot
    simpa [dotProduct_add, dotProduct_smul, orthogonal_col_dotProduct hQ, hpq,
      Ne.symm hpq] using hdot
  have hb : b = 0 := by
    have hdot :=
      congrArg (fun z : Fin n → ℝ => (fun k : Fin n => Q k q) ⬝ᵥ z) hrepr
    change (fun k : Fin n => Q k q) ⬝ᵥ
        ((a • fun k : Fin n => Q k p) + b • fun k : Fin n => Q k q) =
      (fun k : Fin n => Q k q) ⬝ᵥ v at hdot
    rw [hq] at hdot
    simpa [dotProduct_add, dotProduct_smul, orthogonal_col_dotProduct hQ, hpq,
      Ne.symm hpq] using hdot
  rw [← hrepr, ha, hb]
  simp

/-- If two orthogonal columns span an invariant plane with no real eigenline for
    `A`, then the corresponding principal `2 x 2` block of `Qᵀ * A * Q` has no
    real eigenline. This is the source-side bridge that lets the quasi-Schur
    deflation carry irreducibility data from an invariant plane to the explicit
    diagonal block seen by Higham (16.4). -/
lemma matrixNoRealEigenline_principalTwoBlock_of_invariant_noRealEigenline_columnSpan
    (A Q : Matrix (Fin n) (Fin n) ℝ) {p q : Fin n}
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin n) ℝ) (hpq : p ≠ q)
    (W : Submodule ℝ (Fin n → ℝ))
    (hWspan :
      Submodule.span ℝ
        ({(fun k : Fin n => Q k p), (fun k : Fin n => Q k q)}
          : Set (Fin n → ℝ)) = W)
    (hWinv : ∀ w ∈ W, A.mulVecLin w ∈ W)
    (hWno :
      ∀ w ∈ W, w ≠ 0 →
        ¬ ∃ nu : ℝ, A *ᵥ w = nu • w) :
    NumStability.MatrixNoRealEigenline
      (NumStability.principalTwoBlock (Qᵀ * A * Q) p q) := by
  intro x hx hEig
  rcases hEig with ⟨nu, hnu⟩
  let cp : Fin n → ℝ := fun k => Q k p
  let cq : Fin n → ℝ := fun k => Q k q
  let w : Fin n → ℝ := x 0 • cp + x 1 • cq
  have hWspan' : Submodule.span ℝ ({cp, cq} : Set (Fin n → ℝ)) = W := by
    simpa [cp, cq] using hWspan
  have hw_span : w ∈ Submodule.span ℝ ({cp, cq} : Set (Fin n → ℝ)) := by
    rw [Submodule.mem_span_pair]
    exact ⟨x 0, x 1, rfl⟩
  have hwW : w ∈ W := by
    rw [← hWspan']
    exact hw_span
  have hdotp_w : cp ⬝ᵥ w = x 0 := by
    simp [w, cp, cq, dotProduct_add, dotProduct_smul, orthogonal_col_dotProduct hQ, hpq]
  have hdotq_w : cq ⬝ᵥ w = x 1 := by
    simp [w, cp, cq, dotProduct_add, dotProduct_smul, orthogonal_col_dotProduct hQ,
      Ne.symm hpq]
  have hwne : w ≠ 0 := by
    intro hzero
    have hx0 : x 0 = 0 := by
      have hdot := hdotp_w
      rw [hzero, dotProduct_zero] at hdot
      exact hdot.symm
    have hx1 : x 1 = 0 := by
      have hdot := hdotq_w
      rw [hzero, dotProduct_zero] at hdot
      exact hdot.symm
    apply hx
    funext k
    fin_cases k <;> simp [hx0, hx1]
  have hrow0 :
      (Qᵀ * A * Q) p p * x 0 + (Qᵀ * A * Q) p q * x 1 = nu * x 0 := by
    have hcoord := congrFun hnu (0 : Fin 2)
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, principalTwoBlock] using hcoord
  have hrow1 :
      (Qᵀ * A * Q) q p * x 0 + (Qᵀ * A * Q) q q * x 1 = nu * x 1 := by
    have hcoord := congrFun hnu (1 : Fin 2)
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, principalTwoBlock] using hcoord
  have hAw_dotp : cp ⬝ᵥ (A *ᵥ w) = nu * x 0 := by
    calc
      cp ⬝ᵥ (A *ᵥ w)
          = x 0 * (cp ⬝ᵥ (A *ᵥ cp)) + x 1 * (cp ⬝ᵥ (A *ᵥ cq)) := by
            simp [w, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
              dotProduct_smul]
      _ = (Qᵀ * A * Q) p p * x 0 + (Qᵀ * A * Q) p q * x 1 := by
            rw [← conj_entry_eq_dotProduct A Q p p, ← conj_entry_eq_dotProduct A Q p q]
            ring
      _ = nu * x 0 := hrow0
  have hAw_dotq : cq ⬝ᵥ (A *ᵥ w) = nu * x 1 := by
    calc
      cq ⬝ᵥ (A *ᵥ w)
          = x 0 * (cq ⬝ᵥ (A *ᵥ cp)) + x 1 * (cq ⬝ᵥ (A *ᵥ cq)) := by
            simp [w, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
              dotProduct_smul]
      _ = (Qᵀ * A * Q) q p * x 0 + (Qᵀ * A * Q) q q * x 1 := by
            rw [← conj_entry_eq_dotProduct A Q q p, ← conj_entry_eq_dotProduct A Q q q]
            ring
      _ = nu * x 1 := hrow1
  have hresW : A *ᵥ w - nu • w ∈ W := by
    have hAwW : A *ᵥ w ∈ W := by
      simpa [Matrix.mulVecLin_apply] using hWinv w hwW
    exact W.sub_mem hAwW (W.smul_mem nu hwW)
  have hres_span :
      A *ᵥ w - nu • w ∈ Submodule.span ℝ ({cp, cq} : Set (Fin n → ℝ)) := by
    rw [hWspan']
    exact hresW
  have hres_dotp : cp ⬝ᵥ (A *ᵥ w - nu • w) = 0 := by
    rw [dotProduct_sub, dotProduct_smul, hAw_dotp, hdotp_w]
    rw [smul_eq_mul]
    ring
  have hres_dotq : cq ⬝ᵥ (A *ᵥ w - nu • w) = 0 := by
    rw [dotProduct_sub, dotProduct_smul, hAw_dotq, hdotq_w]
    rw [smul_eq_mul]
    ring
  have hres_zero : A *ᵥ w - nu • w = 0 :=
    eq_zero_of_mem_span_pair_orthogonal_cols_dot_eq_zero
      hQ hpq (by simpa [cp, cq] using hres_span)
      (by simpa [cp] using hres_dotp)
      (by simpa [cq] using hres_dotq)
  exact hWno w hwW hwne ⟨nu, sub_eq_zero.mp hres_zero⟩

/-- A framed invariant plane with no real eigenline gives the negative
    discriminant certificate for the corresponding principal `2 x 2` block of
    `Qᵀ * A * Q`. -/
lemma principalTwoBlock_disc_neg_of_invariant_noRealEigenline_columnSpan
    (A Q : Matrix (Fin n) (Fin n) ℝ) {p q : Fin n}
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin n) ℝ) (hpq : p ≠ q)
    (W : Submodule ℝ (Fin n → ℝ))
    (hWspan :
      Submodule.span ℝ
        ({(fun k : Fin n => Q k p), (fun k : Fin n => Q k q)}
          : Set (Fin n → ℝ)) = W)
    (hWinv : ∀ w ∈ W, A.mulVecLin w ∈ W)
    (hWno :
      ∀ w ∈ W, w ≠ 0 →
        ¬ ∃ nu : ℝ, A *ᵥ w = nu • w) :
    ((Qᵀ * A * Q) p p - (Qᵀ * A * Q) q q) ^ 2 +
      4 * (Qᵀ * A * Q) p q * (Qᵀ * A * Q) q p < 0 := by
  exact
    NumStability.principalTwoBlock_disc_neg_of_matrixNoRealEigenline
      (Qᵀ * A * Q) p q
      (matrixNoRealEigenline_principalTwoBlock_of_invariant_noRealEigenline_columnSpan
        A Q hQ hpq W hWspan hWinv hWno)

/-- The span of the first two columns of an orthogonal frame, represented by the
    `{c // c < 2}` index set used by `exists_orthogonal_frame`, is the ordinary
    pair-span of the columns whose values are `0` and `1`. -/
lemma span_frame_lt_two_eq_span_pair_of_val_zero_one
    (Q : Matrix (Fin n) (Fin n) ℝ) {p q : Fin n}
    (hp : (p : ℕ) = 0) (hq : (q : ℕ) = 1) :
    Submodule.span ℝ
        (Set.range
          (fun c : {c : Fin n // (c : ℕ) < 2} => (fun k => Q k c.1))) =
      Submodule.span ℝ
        ({(fun k : Fin n => Q k p), (fun k : Fin n => Q k q)}
          : Set (Fin n → ℝ)) := by
  have hrange :
      Set.range
          (fun c : {c : Fin n // (c : ℕ) < 2} => (fun k => Q k c.1)) =
        ({(fun k : Fin n => Q k p), (fun k : Fin n => Q k q)}
          : Set (Fin n → ℝ)) := by
    ext v
    constructor
    · rintro ⟨c, rfl⟩
      have hc : (c.1 : ℕ) = 0 ∨ (c.1 : ℕ) = 1 := by omega
      rcases hc with h0 | h1
      · left
        have hcp : c.1 = p := Fin.ext (by rw [h0, hp])
        funext k
        change Q k c.1 = Q k p
        rw [hcp]
      · right
        have hcq : c.1 = q := Fin.ext (by rw [h1, hq])
        funext k
        change Q k c.1 = Q k q
        rw [hcq]
    · rintro (rfl | rfl)
      · exact ⟨⟨p, by omega⟩, rfl⟩
      · exact ⟨⟨q, by omega⟩, rfl⟩
  rw [hrange]

/-- The `d = 2` frame-span form of the invariant-plane bridge: if the first two
    frame columns span a no-real-eigenline invariant plane, then the corresponding
    principal block of `Qᵀ * A * Q` has no real eigenline. -/
lemma matrixNoRealEigenline_principalTwoBlock_of_frameSpan_two
    (A Q : Matrix (Fin n) (Fin n) ℝ) {p q : Fin n}
    (hp : (p : ℕ) = 0) (hq : (q : ℕ) = 1)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    (W : Submodule ℝ (Fin n → ℝ))
    (hQspan :
      Submodule.span ℝ
        (Set.range
          (fun c : {c : Fin n // (c : ℕ) < 2} => (fun k => Q k c.1))) = W)
    (hWinv : ∀ w ∈ W, A.mulVecLin w ∈ W)
    (hWno :
      ∀ w ∈ W, w ≠ 0 →
        ¬ ∃ nu : ℝ, A *ᵥ w = nu • w) :
    NumStability.MatrixNoRealEigenline
      (NumStability.principalTwoBlock (Qᵀ * A * Q) p q) := by
  have hpq : p ≠ q := by
    intro h
    have hval := congrArg (fun r : Fin n => (r : ℕ)) h
    omega
  have hpair_span :
      Submodule.span ℝ
          ({(fun k : Fin n => Q k p), (fun k : Fin n => Q k q)}
            : Set (Fin n → ℝ)) = W := by
    rw [← span_frame_lt_two_eq_span_pair_of_val_zero_one Q hp hq]
    exact hQspan
  exact
    matrixNoRealEigenline_principalTwoBlock_of_invariant_noRealEigenline_columnSpan
      A Q hQ hpq W hpair_span hWinv hWno

/-- The `d = 2` frame-span form of the discriminant bridge for a no-real-eigenline
    invariant plane. -/
lemma principalTwoBlock_disc_neg_of_frameSpan_two
    (A Q : Matrix (Fin n) (Fin n) ℝ) {p q : Fin n}
    (hp : (p : ℕ) = 0) (hq : (q : ℕ) = 1)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    (W : Submodule ℝ (Fin n → ℝ))
    (hQspan :
      Submodule.span ℝ
        (Set.range
          (fun c : {c : Fin n // (c : ℕ) < 2} => (fun k => Q k c.1))) = W)
    (hWinv : ∀ w ∈ W, A.mulVecLin w ∈ W)
    (hWno :
      ∀ w ∈ W, w ≠ 0 →
        ¬ ∃ nu : ℝ, A *ᵥ w = nu • w) :
    ((Qᵀ * A * Q) p p - (Qᵀ * A * Q) q q) ^ 2 +
      4 * (Qᵀ * A * Q) p q * (Qᵀ * A * Q) q p < 0 := by
  exact
    NumStability.principalTwoBlock_disc_neg_of_matrixNoRealEigenline
      (Qᵀ * A * Q) p q
      (matrixNoRealEigenline_principalTwoBlock_of_frameSpan_two
        A Q hp hq hQ W hQspan hWinv hWno)

/-- A two-dimensional invariant subspace with no real eigenline can be framed by
    the first two columns of an orthogonal matrix so that the leading principal
    `2 x 2` block has both the no-real-eigenline and negative-discriminant
    certificates. This packages the `d = 2` branch data before recursive
    split/reindex threading. -/
lemma exists_orthogonal_frame_two_principalBlock_noRealEigenline_disc_neg
    (A : Matrix (Fin n) (Fin n) ℝ)
    (W : Submodule ℝ (Fin n → ℝ))
    (hd : finrank ℝ W = 2)
    (hWinv : ∀ w ∈ W, A.mulVecLin w ∈ W)
    (hWno :
      ∀ w ∈ W, w ≠ 0 →
        ¬ ∃ nu : ℝ, A *ᵥ w = nu • w) :
    ∃ (Q : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n),
      Q ∈ Matrix.orthogonalGroup (Fin n) ℝ ∧
        (p : ℕ) = 0 ∧
        (q : ℕ) = 1 ∧
        Submodule.span ℝ
          (Set.range
            (fun c : {c : Fin n // (c : ℕ) < 2} => (fun k => Q k c.1))) = W ∧
        NumStability.MatrixNoRealEigenline
          (NumStability.principalTwoBlock (Qᵀ * A * Q) p q) ∧
        ((Qᵀ * A * Q) p p - (Qᵀ * A * Q) q q) ^ 2 +
          4 * (Qᵀ * A * Q) p q * (Qᵀ * A * Q) q p < 0 := by
  have hdn : 2 ≤ n := by
    have hle : finrank ℝ W ≤ finrank ℝ (Fin n → ℝ) := Submodule.finrank_le W
    rw [hd] at hle
    simpa using hle
  obtain ⟨Q, hQ, _hQmem, hQspan⟩ := exists_orthogonal_frame W 2 hd
  let p : Fin n := ⟨0, by omega⟩
  let q : Fin n := ⟨1, by omega⟩
  have hp : (p : ℕ) = 0 := rfl
  have hq : (q : ℕ) = 1 := rfl
  have hno :
      NumStability.MatrixNoRealEigenline
        (NumStability.principalTwoBlock (Qᵀ * A * Q) p q) :=
    matrixNoRealEigenline_principalTwoBlock_of_frameSpan_two
      A Q hp hq hQ W hQspan hWinv hWno
  have hdisc :
      ((Qᵀ * A * Q) p p - (Qᵀ * A * Q) q q) ^ 2 +
        4 * (Qᵀ * A * Q) p q * (Qᵀ * A * Q) q p < 0 :=
    principalTwoBlock_disc_neg_of_frameSpan_two
      A Q hp hq hQ W hQspan hWinv hWno
  exact ⟨Q, p, q, hQ, hp, hq, hQspan, hno, hdisc⟩

/-- Source-side peel data with the two-dimensional branch already framed as a
    leading `2 x 2` block carrying no-real-eigenline and negative-discriminant
    certificates. This is the nonrecursive input surface needed before the full
    quasi-Schur recursion can export spectral data for its `2 x 2` blocks. -/
lemma exists_invariant_subspace_dim_one_or_two_frame_twoBlock_spectral
    {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ W : Submodule ℝ (Fin n → ℝ),
      (finrank ℝ W = 1 ∨
        ∃ (Q : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n),
          finrank ℝ W = 2 ∧
            Q ∈ Matrix.orthogonalGroup (Fin n) ℝ ∧
            (p : ℕ) = 0 ∧
            (q : ℕ) = 1 ∧
            Submodule.span ℝ
              (Set.range
                (fun c : {c : Fin n // (c : ℕ) < 2} => (fun k => Q k c.1))) = W ∧
            NumStability.MatrixNoRealEigenline
              (NumStability.principalTwoBlock (Qᵀ * A * Q) p q) ∧
            ((Qᵀ * A * Q) p p - (Qᵀ * A * Q) q q) ^ 2 +
              4 * (Qᵀ * A * Q) p q * (Qᵀ * A * Q) q p < 0) ∧
      ∀ w ∈ W, A.mulVecLin w ∈ W := by
  obtain ⟨W, hbranch, hWinv⟩ :=
    NumStability.exists_real_invariant_subspace_dim_one_or_two_no_real_eigenline hn A
  rcases hbranch with h1 | ⟨h2, hWno⟩
  · exact ⟨W, Or.inl h1, hWinv⟩
  · obtain ⟨Q, p, q, hQ, hp, hq, hQspan, hno, hdisc⟩ :=
      exists_orthogonal_frame_two_principalBlock_noRealEigenline_disc_neg
        A W h2 hWinv hWno
    exact ⟨W, Or.inr ⟨Q, p, q, h2, hQ, hp, hq, hQspan, hno, hdisc⟩, hWinv⟩

/-! ### Reindexing helpers: conjugation and orthogonality transport

Transporting an orthogonal conjugation `Xᵀ A X` along an index equivalence
`e : Fin n ≃ ι`.  `Matrix.reindex e e` is an algebra isomorphism, so it commutes
with products, transposes and units, hence carries orthogonal conjugations to
orthogonal conjugations. -/

/-- `Matrix.reindex e e` carries an orthogonal conjugation to an orthogonal
    conjugation: `reindex e e (Xᵀ * A * X) = (reindex e e X)ᵀ * reindex e e A *
    reindex e e X`.  Deflation transport for Higham §16.2 (16.4). -/
lemma reindex_conj {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (A X : Matrix α α ℝ) :
    Matrix.reindex e e (Xᵀ * A * X)
      = (Matrix.reindex e e X)ᵀ * Matrix.reindex e e A * Matrix.reindex e e X := by
  have hmul : ∀ Y Z : Matrix α α ℝ,
      Matrix.reindex e e (Y * Z) = Matrix.reindex e e Y * Matrix.reindex e e Z := by
    intro Y Z
    simp only [Matrix.reindex_apply]
    exact (Matrix.submatrix_mul_equiv Y Z e.symm e.symm e.symm).symm
  rw [hmul, hmul, Matrix.transpose_reindex]

/-- Reindexing and then reindexing back is the identity (transport inverse for
    Higham §16.2 (16.4)). -/
lemma reindex_symm_reindex {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (A : Matrix α α ℝ) :
    Matrix.reindex e.symm e.symm (Matrix.reindex e e A) = A := by
  simp [Matrix.reindex_apply, Matrix.submatrix_submatrix]

/-- `Matrix.reindex e e` preserves the orthogonal group (Higham §16.2 (16.4)). -/
lemma reindex_mem_orthogonal {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) {X : Matrix α α ℝ} (hX : X ∈ Matrix.orthogonalGroup α ℝ) :
    Matrix.reindex e e X ∈ Matrix.orthogonalGroup β ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff'] at hX ⊢
  rw [Matrix.transpose_reindex]
  have hmul : Matrix.reindex e e Xᵀ * Matrix.reindex e e X = Matrix.reindex e e (Xᵀ * X) := by
    simp only [Matrix.reindex_apply]
    exact Matrix.submatrix_mul_equiv Xᵀ X e.symm e.symm e.symm
  rw [hmul, hX]
  simp only [Matrix.reindex_apply]
  exact Matrix.submatrix_one_equiv e.symm

/-! ### The order-compatible splitting equivalence `Fin n ≃ Fin d ⊕ Fin m`

For `d + m = n`, the equivalence `splitEquiv` sends the first `d` indices to the
`Fin d` summand and the rest to the `Fin m` summand, order-preservingly. -/

/-- The order-compatible splitting equivalence `Fin n ≃ Fin d ⊕ Fin m` for
    `d + m = n`, underlying the variable-`d` deflation of Higham §16.2 (16.4). -/
def splitEquiv {d m n : ℕ} (hnm : d + m = n) : Fin n ≃ Fin d ⊕ Fin m :=
  (finCongr hnm.symm).trans finSumFinEquiv.symm

/-- The forward `finSumFinEquiv` recovers the original index value; index
    bookkeeping for the deflation of Higham §16.2 (16.4). -/
lemma finSumFinEquiv_splitEquiv_val {d m n : ℕ} (hnm : d + m = n) (i : Fin n) :
    (finSumFinEquiv (splitEquiv hnm i) : ℕ) = (i : ℕ) := by
  simp [splitEquiv, Equiv.trans_apply]

/-- If `splitEquiv` sends `i` to the left summand `a`, then `(a : ℕ) = (i : ℕ)`
    (Higham §16.2 (16.4) index bookkeeping). -/
lemma splitEquiv_inl_val {d m n : ℕ} (hnm : d + m = n) {i : Fin n} {a : Fin d}
    (h : splitEquiv hnm i = Sum.inl a) : (a : ℕ) = (i : ℕ) := by
  have := finSumFinEquiv_splitEquiv_val hnm i
  rw [h] at this
  rwa [finSumFinEquiv_apply_left, Fin.val_castAdd] at this

/-- If `splitEquiv` sends `i` to the right summand `b`, then `d + (b : ℕ) = (i : ℕ)`
    (Higham §16.2 (16.4) index bookkeeping). -/
lemma splitEquiv_inr_val {d m n : ℕ} (hnm : d + m = n) {i : Fin n} {b : Fin m}
    (h : splitEquiv hnm i = Sum.inr b) : d + (b : ℕ) = (i : ℕ) := by
  have := finSumFinEquiv_splitEquiv_val hnm i
  rw [h] at this
  rwa [finSumFinEquiv_apply_right, Fin.val_natAdd] at this

/-- `splitEquiv` sends `i` to the left summand exactly when `(i : ℕ) < d`
    (Higham §16.2 (16.4) index bookkeeping). -/
lemma splitEquiv_isLeft_iff {d m n : ℕ} (hnm : d + m = n) (i : Fin n) :
    (splitEquiv hnm i).isLeft = true ↔ (i : ℕ) < d := by
  rcases hsum : splitEquiv hnm i with a | b
  · simp only [Sum.isLeft, true_iff]
    have hval := splitEquiv_inl_val hnm hsum
    have := a.2; omega
  · simp only [Sum.isLeft, Bool.false_eq_true, false_iff, not_lt]
    have hval : d + (b : ℕ) = (i : ℕ) := splitEquiv_inr_val hnm hsum
    omega

/-- `splitEquiv` sends an index whose value is `< d` to the corresponding left
    summand.  This is the pointwise form of the leading-block side of the
    variable-`d` deflation split. -/
lemma splitEquiv_eq_inl_of_lt {d m n : ℕ} (hnm : d + m = n)
    (i : Fin n) (hi : (i : ℕ) < d) :
    splitEquiv hnm i = Sum.inl ⟨(i : ℕ), hi⟩ := by
  rcases hsum : splitEquiv hnm i with a | b
  · have hval := splitEquiv_inl_val hnm hsum
    have ha : a = ⟨(i : ℕ), hi⟩ := Fin.ext (by simpa using hval)
    rw [ha]
  · have hval : d + (b : ℕ) = (i : ℕ) := splitEquiv_inr_val hnm hsum
    omega

/-- `splitEquiv` sends an index whose value is `d + a` to the corresponding
    right summand.  This is the pointwise form of the trailing-block side of the
    variable-`d` deflation split. -/
lemma splitEquiv_eq_inr_of_eq_add {d m n : ℕ} (hnm : d + m = n)
    (i : Fin n) (a : Fin m) (hi : (i : ℕ) = d + (a : ℕ)) :
    splitEquiv hnm i = Sum.inr a := by
  rcases hsum : splitEquiv hnm i with b | b
  · have hval := splitEquiv_inl_val hnm hsum
    have hb := b.2
    omega
  · have hval : d + (b : ℕ) = (i : ℕ) := splitEquiv_inr_val hnm hsum
    have hba : b = a := Fin.ext (by omega)
    rw [hba]

/-! ### Block conjugation by the re-embedded trailing orthogonal matrix -/

/-- Conjugating a block matrix `[[P, Bu], [0, D]]` (zero lower-left) by the block
    embedding `[[1,0],[0,U]]` yields `[[P, Bu·U], [0, Uᵀ·D·U]]`; in particular the
    lower-left stays zero and the trailing block becomes `Uᵀ D U`.  The block-form
    deflation re-embedding for the variable-`d` step of Higham §16.2 (16.4). -/
lemma conj_embedBlock_eq {d m : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (Bu : Matrix (Fin d) (Fin m) ℝ) (D : Matrix (Fin m) (Fin m) ℝ)
    (U : Matrix (Fin m) (Fin m) ℝ) :
    (embedBlock (d := d) U)ᵀ * Matrix.fromBlocks P Bu 0 D * embedBlock (d := d) U
      = Matrix.fromBlocks P (Bu * U) 0 (Uᵀ * D * U) := by
  unfold embedBlock
  rw [Matrix.fromBlocks_transpose]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp

/-- Re-embedding a trailing orthogonal factor does not change entries whose row
    and column are both in the leading block. -/
lemma embedBlock_conj_apply_inl_inl {d m : ℕ}
    (M : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ)
    (U : Matrix (Fin m) (Fin m) ℝ) (a b : Fin d) :
    ((embedBlock (d := d) U)ᵀ * M * embedBlock (d := d) U) (Sum.inl a) (Sum.inl b) =
      M (Sum.inl a) (Sum.inl b) := by
  simp [embedBlock, Matrix.fromBlocks, Matrix.mul_apply, Matrix.one_apply]

/-- Re-embedding a trailing orthogonal factor turns the trailing block into the
    conjugated trailing block. -/
lemma embedBlock_conj_apply_inr_inr {d m : ℕ}
    (M : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ)
    (U : Matrix (Fin m) (Fin m) ℝ) (a b : Fin m) :
    ((embedBlock (d := d) U)ᵀ * M * embedBlock (d := d) U) (Sum.inr a) (Sum.inr b) =
      (Uᵀ * M.toBlocks₂₂ * U) a b := by
  simp [embedBlock, Matrix.fromBlocks, Matrix.toBlocks₂₂, Matrix.mul_apply]

/-- Trailing recursive conjugation leaves entries in the leading `d = 2` block
    unchanged after transporting back from the split index. -/
lemma trailing_conj_preserves_leading_entry
    {m n : ℕ} (hnm : 2 + m = n)
    (A Q : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix (Fin m) (Fin m) ℝ)
    {i j : Fin n} (hi : (i : ℕ) < 2) (hj : (j : ℕ) < 2) :
    let e : Fin n ≃ Fin 2 ⊕ Fin m := splitEquiv hnm
    let Qfull : Matrix (Fin n) (Fin n) ℝ :=
      Matrix.reindex e.symm e.symm
        (Matrix.reindex e e Q * embedBlock (d := 2) U)
    (Qfullᵀ * A * Qfull) i j = (Qᵀ * A * Q) i j := by
  let e : Fin n ≃ Fin 2 ⊕ Fin m := splitEquiv hnm
  let Q' : Matrix (Fin 2 ⊕ Fin m) (Fin 2 ⊕ Fin m) ℝ := Matrix.reindex e e Q
  let A' : Matrix (Fin 2 ⊕ Fin m) (Fin 2 ⊕ Fin m) ℝ := Matrix.reindex e e A
  let E : Matrix (Fin 2 ⊕ Fin m) (Fin 2 ⊕ Fin m) ℝ := embedBlock (d := 2) U
  let V : Matrix (Fin 2 ⊕ Fin m) (Fin 2 ⊕ Fin m) ℝ := Q' * E
  have hQfull :
      (Matrix.reindex e.symm e.symm V)ᵀ * A * Matrix.reindex e.symm e.symm V =
        Matrix.reindex e.symm e.symm (Vᵀ * A' * V) := by
    have h := reindex_conj e.symm A' V
    rw [show Matrix.reindex e.symm e.symm A' = A by
      simp [A']] at h
    exact h.symm
  have hV :
      Vᵀ * A' * V = Eᵀ * (Q'ᵀ * A' * Q') * E := by
    dsimp [V]
    rw [Matrix.transpose_mul]
    simp only [mul_assoc]
  have hQ' : Q'ᵀ * A' * Q' = Matrix.reindex e e (Qᵀ * A * Q) := by
    exact (reindex_conj e A Q).symm
  have hei : e i = Sum.inl ⟨(i : ℕ), hi⟩ := splitEquiv_eq_inl_of_lt hnm i hi
  have hej : e j = Sum.inl ⟨(j : ℕ), hj⟩ := splitEquiv_eq_inl_of_lt hnm j hj
  have hsym_i : e.symm (Sum.inl ⟨(i : ℕ), hi⟩) = i := by
    rw [← hei]
    exact e.symm_apply_apply i
  have hsym_j : e.symm (Sum.inl ⟨(j : ℕ), hj⟩) = j := by
    rw [← hej]
    exact e.symm_apply_apply j
  change (((Matrix.reindex e.symm e.symm V)ᵀ * A *
      Matrix.reindex e.symm e.symm V) i j = (Qᵀ * A * Q) i j)
  rw [hQfull]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  change (Vᵀ * A' * V) (e i) (e j) = (Qᵀ * A * Q) i j
  rw [hei, hej, hV, embedBlock_conj_apply_inl_inl, hQ']
  simp [Matrix.reindex_apply, hsym_i, hsym_j]

/-- Trailing recursive conjugation transports entries in the trailing block to
    the conjugated recursive block after splitting by an arbitrary leading
    dimension `d`.  This is the entrywise algebra needed before recursive
    spectral certificates can be threaded through the Schur construction. -/
lemma trailing_conj_preserves_trailing_entry
    {d m n : ℕ} (hnm : d + m = n)
    (A Q : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix (Fin m) (Fin m) ℝ)
    {i j : Fin n} {a b : Fin m}
    (hi : (i : ℕ) = d + (a : ℕ)) (hj : (j : ℕ) = d + (b : ℕ)) :
    let e : Fin n ≃ Fin d ⊕ Fin m := splitEquiv hnm
    let Qfull : Matrix (Fin n) (Fin n) ℝ :=
      Matrix.reindex e.symm e.symm
        (Matrix.reindex e e Q * embedBlock (d := d) U)
    (Qfullᵀ * A * Qfull) i j =
      (Uᵀ * (Matrix.reindex e e (Qᵀ * A * Q)).toBlocks₂₂ * U) a b := by
  let e : Fin n ≃ Fin d ⊕ Fin m := splitEquiv hnm
  let Q' : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ := Matrix.reindex e e Q
  let A' : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ := Matrix.reindex e e A
  let E : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ := embedBlock (d := d) U
  let V : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ := Q' * E
  have hQfull :
      (Matrix.reindex e.symm e.symm V)ᵀ * A * Matrix.reindex e.symm e.symm V =
        Matrix.reindex e.symm e.symm (Vᵀ * A' * V) := by
    have h := reindex_conj e.symm A' V
    rw [show Matrix.reindex e.symm e.symm A' = A by
      simp [A']] at h
    exact h.symm
  have hV :
      Vᵀ * A' * V = Eᵀ * (Q'ᵀ * A' * Q') * E := by
    dsimp [V]
    rw [Matrix.transpose_mul]
    simp only [mul_assoc]
  have hQ' : Q'ᵀ * A' * Q' = Matrix.reindex e e (Qᵀ * A * Q) := by
    exact (reindex_conj e A Q).symm
  have hei : e i = Sum.inr a := splitEquiv_eq_inr_of_eq_add hnm i a hi
  have hej : e j = Sum.inr b := splitEquiv_eq_inr_of_eq_add hnm j b hj
  change (((Matrix.reindex e.symm e.symm V)ᵀ * A *
      Matrix.reindex e.symm e.symm V) i j =
        (Uᵀ * (Matrix.reindex e e (Qᵀ * A * Q)).toBlocks₂₂ * U) a b)
  rw [hQfull]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  change (Vᵀ * A' * V) (e i) (e j) =
    (Uᵀ * (Matrix.reindex e e (Qᵀ * A * Q)).toBlocks₂₂ * U) a b
  rw [hei, hej, hV, embedBlock_conj_apply_inr_inr, hQ']

/-- The ordered `2 x 2` block on a trailing pair is exactly the corresponding
    principal block of the recursively conjugated trailing Schur factor. -/
lemma principalTwoBlock_trailing_conj_transports_trailing_two
    {d m n : ℕ} (hnm : d + m = n)
    (A Q : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix (Fin m) (Fin m) ℝ)
    {p q : Fin n} {a b : Fin m}
    (hp : (p : ℕ) = d + (a : ℕ))
    (hq : (q : ℕ) = d + (b : ℕ)) :
    let e : Fin n ≃ Fin d ⊕ Fin m := splitEquiv hnm
    let Qfull : Matrix (Fin n) (Fin n) ℝ :=
      Matrix.reindex e.symm e.symm
        (Matrix.reindex e e Q * embedBlock (d := d) U)
    NumStability.principalTwoBlock (Qfullᵀ * A * Qfull) p q =
      NumStability.principalTwoBlock
        (Uᵀ * (Matrix.reindex e e (Qᵀ * A * Q)).toBlocks₂₂ * U) a b := by
  funext i j
  fin_cases i <;> fin_cases j
  · exact trailing_conj_preserves_trailing_entry hnm A Q U hp hp
  · exact trailing_conj_preserves_trailing_entry hnm A Q U hp hq
  · exact trailing_conj_preserves_trailing_entry hnm A Q U hq hp
  · exact trailing_conj_preserves_trailing_entry hnm A Q U hq hq

/-- No-real-eigenline and negative-discriminant certificates for a trailing
    recursive `2 x 2` block transport back through the full re-embedded Schur
    factor. -/
lemma trailing_twoBlock_spectral_preserved_after_trailing_conj
    {d m n : ℕ} (hnm : d + m = n)
    (A Q : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix (Fin m) (Fin m) ℝ)
    {p q : Fin n} {a b : Fin m}
    (hp : (p : ℕ) = d + (a : ℕ))
    (hq : (q : ℕ) = d + (b : ℕ))
    (hno :
      let e : Fin n ≃ Fin d ⊕ Fin m := splitEquiv hnm
      NumStability.MatrixNoRealEigenline
        (NumStability.principalTwoBlock
          (Uᵀ * (Matrix.reindex e e (Qᵀ * A * Q)).toBlocks₂₂ * U) a b)) :
    let e : Fin n ≃ Fin d ⊕ Fin m := splitEquiv hnm
    let Qfull : Matrix (Fin n) (Fin n) ℝ :=
      Matrix.reindex e.symm e.symm
        (Matrix.reindex e e Q * embedBlock (d := d) U)
    NumStability.MatrixNoRealEigenline
        (NumStability.principalTwoBlock (Qfullᵀ * A * Qfull) p q) ∧
      ((Qfullᵀ * A * Qfull) p p - (Qfullᵀ * A * Qfull) q q) ^ 2 +
        4 * (Qfullᵀ * A * Qfull) p q * (Qfullᵀ * A * Qfull) q p < 0 := by
  let e : Fin n ≃ Fin d ⊕ Fin m := splitEquiv hnm
  let Qfull : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.reindex e.symm e.symm
      (Matrix.reindex e e Q * embedBlock (d := d) U)
  have hblock :
      NumStability.principalTwoBlock (Qfullᵀ * A * Qfull) p q =
        NumStability.principalTwoBlock
          (Uᵀ * (Matrix.reindex e e (Qᵀ * A * Q)).toBlocks₂₂ * U) a b :=
    principalTwoBlock_trailing_conj_transports_trailing_two hnm A Q U hp hq
  have hno' :
      NumStability.MatrixNoRealEigenline
        (NumStability.principalTwoBlock (Qfullᵀ * A * Qfull) p q) := by
    rw [hblock]
    simpa [e] using hno
  exact ⟨hno',
    NumStability.principalTwoBlock_disc_neg_of_matrixNoRealEigenline
      (Qfullᵀ * A * Qfull) p q hno'⟩

/-- A recursive trailing adjacent same-block spectral certificate lifts to the
    parent block map after re-embedding the trailing Schur factor. -/
lemma trailing_twoBlock_spectral_with_parentBlockMap_after_trailing_conj
    {d m n : ℕ} (hnm : d + m = n)
    (A Q : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix (Fin m) (Fin m) ℝ)
    (p' : Fin m → ℕ) {a b : Fin m}
    (hab : (b : ℕ) = (a : ℕ) + 1)
    (hsame : p' a = p' b)
    (hspectral :
      let e : Fin n ≃ Fin d ⊕ Fin m := splitEquiv hnm
      HasRealQuasiSchurTwoBlockSpectral
        (Uᵀ * (Matrix.reindex e e (Qᵀ * A * Q)).toBlocks₂₂ * U) p') :
    let e : Fin n ≃ Fin d ⊕ Fin m := splitEquiv hnm
    let Qfull : Matrix (Fin n) (Fin n) ℝ :=
      Matrix.reindex e.symm e.symm
        (Matrix.reindex e e Q * embedBlock (d := d) U)
    let pmap : Fin n → ℕ :=
      fun i => Sum.elim (fun _ : Fin d => 0) (fun c : Fin m => p' c + 1) (e i)
    let p : Fin n := e.symm (Sum.inr a)
    let q : Fin n := e.symm (Sum.inr b)
    (q : ℕ) = (p : ℕ) + 1 ∧
      pmap p = pmap q ∧
      NumStability.MatrixNoRealEigenline
        (NumStability.principalTwoBlock (Qfullᵀ * A * Qfull) p q) ∧
      ((Qfullᵀ * A * Qfull) p p - (Qfullᵀ * A * Qfull) q q) ^ 2 +
        4 * (Qfullᵀ * A * Qfull) p q * (Qfullᵀ * A * Qfull) q p < 0 := by
  let e : Fin n ≃ Fin d ⊕ Fin m := splitEquiv hnm
  let Qfull : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.reindex e.symm e.symm
      (Matrix.reindex e e Q * embedBlock (d := d) U)
  let pmap : Fin n → ℕ :=
    fun i => Sum.elim (fun _ : Fin d => 0) (fun c : Fin m => p' c + 1) (e i)
  let p : Fin n := e.symm (Sum.inr a)
  let q : Fin n := e.symm (Sum.inr b)
  have hpval : (p : ℕ) = d + (a : ℕ) := by
    have hsum : splitEquiv hnm p = Sum.inr a := by
      dsimp [p, e]
      exact (splitEquiv hnm).apply_symm_apply (Sum.inr a)
    exact (splitEquiv_inr_val hnm hsum).symm
  have hqval : (q : ℕ) = d + (b : ℕ) := by
    have hsum : splitEquiv hnm q = Sum.inr b := by
      dsimp [q, e]
      exact (splitEquiv hnm).apply_symm_apply (Sum.inr b)
    exact (splitEquiv_inr_val hnm hsum).symm
  have hadj : (q : ℕ) = (p : ℕ) + 1 := by
    omega
  have hsame_parent : pmap p = pmap q := by
    dsimp [pmap, p, q, e]
    simp [hsame]
  have htrail :
      NumStability.MatrixNoRealEigenline
        (NumStability.principalTwoBlock
          (Uᵀ * (Matrix.reindex e e (Qᵀ * A * Q)).toBlocks₂₂ * U) a b) ∧
        ((Uᵀ * (Matrix.reindex e e (Qᵀ * A * Q)).toBlocks₂₂ * U) a a -
            (Uᵀ * (Matrix.reindex e e (Qᵀ * A * Q)).toBlocks₂₂ * U) b b) ^ 2 +
          4 * (Uᵀ * (Matrix.reindex e e (Qᵀ * A * Q)).toBlocks₂₂ * U) a b *
            (Uᵀ * (Matrix.reindex e e (Qᵀ * A * Q)).toBlocks₂₂ * U) b a < 0 := by
    simpa [e] using hspectral a b hab hsame
  have hfull :
      NumStability.MatrixNoRealEigenline
          (NumStability.principalTwoBlock (Qfullᵀ * A * Qfull) p q) ∧
        ((Qfullᵀ * A * Qfull) p p - (Qfullᵀ * A * Qfull) q q) ^ 2 +
          4 * (Qfullᵀ * A * Qfull) p q * (Qfullᵀ * A * Qfull) q p < 0 := by
    simpa [e, Qfull, p, q] using
      trailing_twoBlock_spectral_preserved_after_trailing_conj
        hnm A Q U hpval hqval htrail.1
  exact ⟨hadj, hsame_parent, hfull.1, hfull.2⟩

/-- The principal leading `2 x 2` block is unchanged when the trailing recursive
    conjugation is re-embedded. -/
lemma principalTwoBlock_trailing_conj_preserves_leading_two
    {m n : ℕ} (hnm : 2 + m = n)
    (A Q : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix (Fin m) (Fin m) ℝ)
    {p q : Fin n}
    (hp : (p : ℕ) = 0) (hq : (q : ℕ) = 1) :
    let e : Fin n ≃ Fin 2 ⊕ Fin m := splitEquiv hnm
    let Qfull : Matrix (Fin n) (Fin n) ℝ :=
      Matrix.reindex e.symm e.symm
        (Matrix.reindex e e Q * embedBlock (d := 2) U)
    NumStability.principalTwoBlock (Qfullᵀ * A * Qfull) p q =
      NumStability.principalTwoBlock (Qᵀ * A * Q) p q := by
  funext i j
  fin_cases i <;> fin_cases j
  · exact trailing_conj_preserves_leading_entry hnm A Q U (by omega) (by omega)
  · exact trailing_conj_preserves_leading_entry hnm A Q U (by omega) (by omega)
  · exact trailing_conj_preserves_leading_entry hnm A Q U (by omega) (by omega)
  · exact trailing_conj_preserves_leading_entry hnm A Q U (by omega) (by omega)

/-- No-real-eigenline and negative-discriminant certificates for the leading
    `2 x 2` block survive the trailing recursive conjugation. -/
lemma leading_twoBlock_spectral_preserved_after_trailing_conj
    {m n : ℕ} (hnm : 2 + m = n)
    (A Q : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix (Fin m) (Fin m) ℝ)
    {p q : Fin n}
    (hp : (p : ℕ) = 0) (hq : (q : ℕ) = 1)
    (hno :
      NumStability.MatrixNoRealEigenline
        (NumStability.principalTwoBlock (Qᵀ * A * Q) p q)) :
    let e : Fin n ≃ Fin 2 ⊕ Fin m := splitEquiv hnm
    let Qfull : Matrix (Fin n) (Fin n) ℝ :=
      Matrix.reindex e.symm e.symm
        (Matrix.reindex e e Q * embedBlock (d := 2) U)
    NumStability.MatrixNoRealEigenline
        (NumStability.principalTwoBlock (Qfullᵀ * A * Qfull) p q) ∧
      ((Qfullᵀ * A * Qfull) p p - (Qfullᵀ * A * Qfull) q q) ^ 2 +
        4 * (Qfullᵀ * A * Qfull) p q * (Qfullᵀ * A * Qfull) q p < 0 := by
  let e : Fin n ≃ Fin 2 ⊕ Fin m := splitEquiv hnm
  let Qfull : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.reindex e.symm e.symm
      (Matrix.reindex e e Q * embedBlock (d := 2) U)
  have hblock :
      NumStability.principalTwoBlock (Qfullᵀ * A * Qfull) p q =
        NumStability.principalTwoBlock (Qᵀ * A * Q) p q :=
    principalTwoBlock_trailing_conj_preserves_leading_two hnm A Q U hp hq
  have hno' :
      NumStability.MatrixNoRealEigenline
        (NumStability.principalTwoBlock (Qfullᵀ * A * Qfull) p q) := by
    rw [hblock]
    exact hno
  exact ⟨hno',
    NumStability.principalTwoBlock_disc_neg_of_matrixNoRealEigenline
      (Qfullᵀ * A * Qfull) p q hno'⟩

/-- A two-dimensional no-real-eigenline peel branch can be framed, recursively
    re-embedded through an orthogonal trailing factor, and still expose the
    leading `2 x 2` no-real-eigenline/negative-discriminant certificate. -/
lemma exists_orthogonal_frame_two_principalBlock_spectral_after_trailing_conj
    {m n : ℕ} (hnm : 2 + m = n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (W : Submodule ℝ (Fin n → ℝ))
    (hd : finrank ℝ W = 2)
    (hWinv : ∀ w ∈ W, A.mulVecLin w ∈ W)
    (hWno :
      ∀ w ∈ W, w ≠ 0 →
        ¬ ∃ nu : ℝ, A *ᵥ w = nu • w)
    (U : Matrix (Fin m) (Fin m) ℝ)
    (hUorth : U ∈ Matrix.orthogonalGroup (Fin m) ℝ) :
    ∃ (Q Qfull : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n),
      Q ∈ Matrix.orthogonalGroup (Fin n) ℝ ∧
        Qfull ∈ Matrix.orthogonalGroup (Fin n) ℝ ∧
        (p : ℕ) = 0 ∧
        (q : ℕ) = 1 ∧
        Submodule.span ℝ
          (Set.range
            (fun c : {c : Fin n // (c : ℕ) < 2} => (fun k => Q k c.1))) = W ∧
        (let e : Fin n ≃ Fin 2 ⊕ Fin m := splitEquiv hnm
         Qfull =
          Matrix.reindex e.symm e.symm
            (Matrix.reindex e e Q * embedBlock (d := 2) U)) ∧
        NumStability.MatrixNoRealEigenline
          (NumStability.principalTwoBlock (Qfullᵀ * A * Qfull) p q) ∧
        ((Qfullᵀ * A * Qfull) p p - (Qfullᵀ * A * Qfull) q q) ^ 2 +
          4 * (Qfullᵀ * A * Qfull) p q * (Qfullᵀ * A * Qfull) q p < 0 := by
  obtain ⟨Q, p, q, hQ, hp, hq, hQspan, hno, _hdisc⟩ :=
    exists_orthogonal_frame_two_principalBlock_noRealEigenline_disc_neg
      A W hd hWinv hWno
  let e : Fin n ≃ Fin 2 ⊕ Fin m := splitEquiv hnm
  let Qfull : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.reindex e.symm e.symm
      (Matrix.reindex e e Q * embedBlock (d := 2) U)
  have hQfullorth : Qfull ∈ Matrix.orthogonalGroup (Fin n) ℝ := by
    change Matrix.reindex e.symm e.symm
      (Matrix.reindex e e Q * embedBlock (d := 2) U) ∈ Matrix.orthogonalGroup (Fin n) ℝ
    exact reindex_mem_orthogonal e.symm
      (Submonoid.mul_mem _
        (reindex_mem_orthogonal e hQ)
        (embedBlock_mem_orthogonal (d := 2) hUorth))
  have hspectral :
      NumStability.MatrixNoRealEigenline
          (NumStability.principalTwoBlock (Qfullᵀ * A * Qfull) p q) ∧
        ((Qfullᵀ * A * Qfull) p p - (Qfullᵀ * A * Qfull) q q) ^ 2 +
          4 * (Qfullᵀ * A * Qfull) p q * (Qfullᵀ * A * Qfull) q p < 0 :=
    leading_twoBlock_spectral_preserved_after_trailing_conj
      hnm A Q U hp hq hno
  exact ⟨Q, Qfull, p, q, hQ, hQfullorth, hp, hq, hQspan, rfl,
    hspectral.1, hspectral.2⟩

/-! ### The variable-`d` orthogonal deflation induction (Higham (16.4)) -/

open RealInvariantSubspaceAux in
/-- **Existence of the real quasi-triangular orthogonal Schur form (Higham
    §16.2 (16.4)).**  Every real square matrix `A` is orthogonally similar to a
    quasi-upper-triangular matrix.  Proved by strong induction on the dimension
    with a *variable* peel size `d ∈ {1, 2}`: peel off a real invariant subspace
    of dimension `d` (`exists_real_invariant_subspace_dim_one_or_two`), extend an
    orthonormal basis of it to the whole space (`exists_orthogonal_frame`),
    conjugate to zero the block strictly below the leading `d` columns
    (`deflation_lower_left_zero`), reindex to expose the block structure, recurse
    on the `(n-d)×(n-d)` trailing block, and re-embed via a block-diagonal
    orthogonal matrix. -/
theorem exists_orthogonal_conj_quasiUpperTriangular :
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
      ∃ Q : Matrix (Fin n) (Fin n) ℝ, Q ∈ Matrix.orthogonalGroup (Fin n) ℝ ∧
        IsQuasiUpperTriangular (Qᵀ * A * Q) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · -- empty matrix: trivially quasi-triangular
      subst hn0
      refine ⟨1, Submonoid.one_mem _, fun _ => 0, ?_, ?_, ?_⟩
      · exact monotone_const
      · intro c; simp
      · intro i; exact absurd i.2 (Nat.not_lt_zero _)
    · -- peel a `d ∈ {1,2}`-dimensional invariant subspace
      obtain ⟨W, hWdim, hWinv⟩ := exists_real_invariant_subspace_dim_one_or_two hnpos A
      -- the dimension `d`
      obtain ⟨d, hd, hdle⟩ : ∃ d, finrank ℝ W = d ∧ (d = 1 ∨ d = 2) := by
        rcases hWdim with h1 | h2
        · exact ⟨1, h1, Or.inl rfl⟩
        · exact ⟨2, h2, Or.inr rfl⟩
      have hdpos : 0 < d := by rcases hdle with h | h <;> omega
      have hdcard : d ≤ 2 := by rcases hdle with h | h <;> omega
      -- the trailing size `m`
      set m : ℕ := n - d with hm
      have hdn : d ≤ n := by
        have hle : finrank ℝ W ≤ finrank ℝ (Fin n → ℝ) := Submodule.finrank_le W
        rw [hd] at hle; simpa using hle
      have hnm : d + m = n := by omega
      have hmlt : m < n := by omega
      -- the orthogonal frame
      obtain ⟨Q, hQorth, hQmem, hQspan⟩ := exists_orthogonal_frame W d hd
      -- invariance in the form needed by the deflation lemma
      have hinv : ∀ j : Fin n, (j : ℕ) < d →
          (A *ᵥ (fun k => Q k j)) ∈
            Submodule.span ℝ
              (Set.range (fun c : {c : Fin n // (c : ℕ) < d} => (fun k => Q k c.1))) := by
        intro j hj
        rw [hQspan]
        have hcolmem : (fun k => Q k j) ∈ W := hQmem ⟨j, hj⟩
        have := hWinv (fun k => Q k j) hcolmem
        rwa [Matrix.mulVecLin_apply] at this
      -- zero lower-left block in `Fin n`
      have hMzero : ∀ i j : Fin n, d ≤ (i : ℕ) → (j : ℕ) < d → (Qᵀ * A * Q) i j = 0 :=
        fun i j hi hj => deflation_lower_left_zero A Q hQorth d hinv i j hi hj
      -- reindex to the sum index
      set e : Fin n ≃ Fin d ⊕ Fin m := splitEquiv hnm with he
      set M : Matrix (Fin n) (Fin n) ℝ := Qᵀ * A * Q with hMdef
      set M' : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ := Matrix.reindex e e M with hM'
      -- zero lower-left block of `M'`
      have hM'zero : M'.toBlocks₂₁ = 0 := by
        ext a b
        simp only [Matrix.toBlocks₂₁, hM', Matrix.reindex_apply, Matrix.submatrix_apply,
          Matrix.of_apply, Matrix.zero_apply]
        apply hMzero
        · -- `d ≤ (e.symm (inr a) : ℕ)`
          have hsum : splitEquiv hnm (e.symm (Sum.inr a)) = Sum.inr a := by
            rw [← he]; exact e.apply_symm_apply _
          have hval := splitEquiv_inr_val hnm hsum
          omega
        · -- `(e.symm (inl b) : ℕ) < d`
          have hsum : splitEquiv hnm (e.symm (Sum.inl b)) = Sum.inl b := by
            rw [← he]; exact e.apply_symm_apply _
          have hval := splitEquiv_inl_val hnm hsum
          have hb := b.2; omega
      -- block form of `M'`
      have hM'block : M' = Matrix.fromBlocks M'.toBlocks₁₁ M'.toBlocks₁₂ 0 M'.toBlocks₂₂ := by
        conv_lhs => rw [← Matrix.fromBlocks_toBlocks M']
        rw [hM'zero]
      -- recurse on the trailing block
      obtain ⟨U', hU'orth, hU'qt⟩ := ih m hmlt M'.toBlocks₂₂
      -- the conjugated block matrix over the sum index
      set Q' : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ := Matrix.reindex e e Q with hQ'
      set A' : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ := Matrix.reindex e e A with hA'
      set V : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ := Q' * embedBlock U' with hV
      set Qfull : Matrix (Fin n) (Fin n) ℝ := Matrix.reindex e.symm e.symm V with hQfull
      -- `Qfull` is orthogonal
      have hQfullorth : Qfull ∈ Matrix.orthogonalGroup (Fin n) ℝ := by
        rw [hQfull]
        apply reindex_mem_orthogonal
        rw [hV]
        exact Submonoid.mul_mem _ (reindex_mem_orthogonal e hQorth) (embedBlock_mem_orthogonal hU'orth)
      refine ⟨Qfull, hQfullorth, ?_⟩
      -- identify `Qfullᵀ * A * Qfull` with the transported conjugated block matrix
      set X : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ :=
        (embedBlock U')ᵀ * M' * embedBlock U' with hX
      have hconj : Qfullᵀ * A * Qfull = Matrix.reindex e.symm e.symm X := by
        -- `M' = Q'ᵀ * A' * Q'`
        have hM'conj : M' = Q'ᵀ * A' * Q' := by
          rw [hM', hMdef, hQ', hA', reindex_conj]
        have hXeq : X = Vᵀ * A' * V := by
          rw [hX, hM'conj, hV]
          rw [Matrix.transpose_mul]
          simp only [mul_assoc]
        rw [hXeq, reindex_conj, ← hQfull, hA', reindex_symm_reindex]
      rw [hconj]
      -- Now prove `reindex e.symm e.symm X` is quasi-upper-triangular.
      -- First: `X = fromBlocks P (Bu·U') 0 (U'ᵀ·D·U')`.
      have hXblock : X = Matrix.fromBlocks M'.toBlocks₁₁ (M'.toBlocks₁₂ * U') 0
          (U'ᵀ * M'.toBlocks₂₂ * U') := by
        rw [hX]
        conv_lhs => rw [hM'block]
        rw [conj_embedBlock_eq]
      -- the trailing block's quasi-tri assignment
      obtain ⟨p', hp'mono, hp'card, hp'zero⟩ := hU'qt
      -- entry formula of the transported matrix
      have hRentry : ∀ i j : Fin n, (Matrix.reindex e.symm e.symm X) i j = X (e i) (e j) := by
        intro i j
        simp [Matrix.reindex_apply, Matrix.submatrix_apply]
      -- block assignment on the sum index
      set q : Fin d ⊕ Fin m → ℕ := Sum.elim (fun _ => 0) (fun a => p' a + 1) with hq
      -- the assignment `p` on `Fin n`
      refine ⟨fun i => q (e i), ?_, ?_, ?_⟩
      · -- Monotone
        intro i i' hii'
        rcases hei : e i with a | a
        · simp [hq, hei]
        · -- e i = inr a, so i ≥ d, hence i' ≥ d, so e i' = inr a'
          have heisp : splitEquiv hnm i = Sum.inr a := by rw [← he]; exact hei
          have hia : d + (a : ℕ) = (i : ℕ) := splitEquiv_inr_val hnm heisp
          rcases hei' : e i' with a' | a'
          · -- e i' = inl a' ⇒ i' < d, contradiction with i ≤ i' and i ≥ d
            have hei'sp : splitEquiv hnm i' = Sum.inl a' := by rw [← he]; exact hei'
            have hia' : (a' : ℕ) = (i' : ℕ) := splitEquiv_inl_val hnm hei'sp
            have ha'2 := a'.2
            have hii'val : (i : ℕ) ≤ (i' : ℕ) := hii'
            omega
          · -- e i' = inr a', both ≥ d, and p' a ≤ p' a'
            have hei'sp : splitEquiv hnm i' = Sum.inr a' := by rw [← he]; exact hei'
            have hia' : d + (a' : ℕ) = (i' : ℕ) := splitEquiv_inr_val hnm hei'sp
            have haa' : (a : ℕ) ≤ (a' : ℕ) := by
              have hii'val : (i : ℕ) ≤ (i' : ℕ) := hii'; omega
            simp only [hq, hei, hei', Sum.elim_inr]
            have := hp'mono (show a ≤ a' from haa')
            omega
      · -- card ≤ 2
        intro c
        -- transport the fiber card along `e`
        have hcardeq : (Finset.univ.filter (fun i : Fin n => q (e i) = c)).card
            = (Finset.univ.filter (fun x : Fin d ⊕ Fin m => q x = c)).card := by
          rw [← Fintype.card_subtype, ← Fintype.card_subtype]
          exact Fintype.card_congr (Equiv.subtypeEquiv e (fun a => Iff.rfl))
        rw [hcardeq, ← Fintype.card_subtype]
        -- split the sum-subtype
        rw [Fintype.card_congr (Equiv.subtypeSum (p := fun x : Fin d ⊕ Fin m => q x = c))]
        rw [Fintype.card_sum]
        -- for each `c`, at most one summand is nonzero
        by_cases hc0 : c = 0
        · -- c = 0: left = d ≤ 2, right = 0
          subst hc0
          have hleft : Fintype.card {a : Fin d // q (Sum.inl a) = 0} = d := by
            simp only [hq, Sum.elim_inl]
            simp [Fintype.card_subtype]
          have hright : Fintype.card {b : Fin m // q (Sum.inr b) = 0} = 0 := by
            simp only [hq, Sum.elim_inr]
            rw [Fintype.card_subtype]
            simp only [Nat.succ_ne_zero, Finset.filter_false, Finset.card_empty]
          rw [hleft, hright]; omega
        · -- c ≥ 1: left = 0, right ≤ 2
          have hleft : Fintype.card {a : Fin d // q (Sum.inl a) = c} = 0 := by
            simp only [hq, Sum.elim_inl]
            rw [Fintype.card_subtype]
            simp only [Finset.card_eq_zero]
            rw [Finset.filter_eq_empty_iff]
            intro a _; exact fun h => hc0 h.symm
          have hright : Fintype.card {b : Fin m // q (Sum.inr b) = c} ≤ 2 := by
            simp only [hq, Sum.elim_inr]
            rw [Fintype.card_subtype]
            have hce : ∀ b : Fin m, (p' b + 1 = c) ↔ (p' b = c - 1) := by
              intro b; omega
            simp only [hce]
            rw [← Fintype.card_subtype, Fintype.card_subtype]
            exact hp'card (c - 1)
          rw [hleft]; omega
      · -- below-block zero
        intro i j hlt
        rw [hRentry, hXblock]
        rcases hei : e i with a | a
        · -- e i = inl: p i = 0, but p j < p i = 0 impossible
          exfalso
          simp only [hq, hei, Sum.elim_inl] at hlt
          exact Nat.not_lt_zero _ hlt
        · rcases hej : e j with b | b
          · -- e i = inr a, e j = inl b: lower-left block is zero
            simp [Matrix.fromBlocks]
          · -- e i = inr a, e j = inr b: trailing block, use p' zero condition
            simp only [Matrix.fromBlocks_apply₂₂]
            apply hp'zero
            simp only [hq, hei, hej, Sum.elim_inr] at hlt
            omega

open RealInvariantSubspaceAux in
/-- Strengthened real quasi-Schur construction carrying spectral certificates
    for every adjacent `2 x 2` block produced by the recursive block map. -/
theorem exists_orthogonal_conj_quasiUpperTriangular_twoBlockSpectral :
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
      ∃ Q : Matrix (Fin n) (Fin n) ℝ, Q ∈ Matrix.orthogonalGroup (Fin n) ℝ ∧
        ∃ pmap : Fin n → ℕ,
          Monotone pmap ∧
          (∀ c : ℕ, (Finset.univ.filter (fun i => pmap i = c)).card ≤ 2) ∧
          (∀ i j : Fin n, pmap j < pmap i → (Qᵀ * A * Q) i j = 0) ∧
          HasRealQuasiSchurTwoBlockSpectral (Qᵀ * A * Q) pmap := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      refine ⟨1, Submonoid.one_mem _, ?_⟩
      refine ⟨fun _ => 0, monotone_const, ?_, ?_, ?_⟩
      · intro c; simp
      · intro i; exact absurd i.2 (Nat.not_lt_zero _)
      · intro p _q _hadj _hsame
        exact Fin.elim0 p
    · obtain ⟨W, hWbranch, hWinv⟩ :=
        exists_invariant_subspace_dim_one_or_two_frame_twoBlock_spectral hnpos A
      obtain ⟨d, hd, hdle, Q, hQorth, hQspan, hlead⟩ :
          ∃ d : ℕ, finrank ℝ W = d ∧ (d = 1 ∨ d = 2) ∧
            ∃ Q : Matrix (Fin n) (Fin n) ℝ,
              Q ∈ Matrix.orthogonalGroup (Fin n) ℝ ∧
              Submodule.span ℝ
                (Set.range
                  (fun c : {c : Fin n // (c : ℕ) < d} => (fun k => Q k c.1))) = W ∧
              (d = 2 →
                ∃ p q : Fin n, (p : ℕ) = 0 ∧ (q : ℕ) = 1 ∧
                  NumStability.MatrixNoRealEigenline
                    (NumStability.principalTwoBlock (Qᵀ * A * Q) p q)) := by
        rcases hWbranch with h1 | h2data
        · obtain ⟨Q, hQorth, _hQmem, hQspan⟩ := exists_orthogonal_frame W 1 h1
          refine ⟨1, h1, Or.inl rfl, Q, hQorth, hQspan, ?_⟩
          intro h12
          omega
        · obtain ⟨Q, p, q, h2, hQorth, hp, hq, hQspan, hno, _hdisc⟩ := h2data
          refine ⟨2, h2, Or.inr rfl, Q, hQorth, hQspan, ?_⟩
          intro _h22
          exact ⟨p, q, hp, hq, hno⟩
      have hdpos : 0 < d := by rcases hdle with h | h <;> omega
      have hdcard : d ≤ 2 := by rcases hdle with h | h <;> omega
      set m : ℕ := n - d with hm
      have hdn : d ≤ n := by
        have hle : finrank ℝ W ≤ finrank ℝ (Fin n → ℝ) := Submodule.finrank_le W
        rw [hd] at hle
        simpa using hle
      have hnm : d + m = n := by omega
      have hmlt : m < n := by omega
      have hinv : ∀ j : Fin n, (j : ℕ) < d →
          (A *ᵥ (fun k => Q k j)) ∈
            Submodule.span ℝ
              (Set.range (fun c : {c : Fin n // (c : ℕ) < d} => (fun k => Q k c.1))) := by
        intro j hj
        have hcolmem : (fun k => Q k j) ∈ W := by
          rw [← hQspan]
          exact Submodule.subset_span (Set.mem_range.mpr ⟨⟨j, hj⟩, rfl⟩)
        have hmap := hWinv (fun k => Q k j) hcolmem
        rw [hQspan]
        simpa [Matrix.mulVecLin_apply] using hmap
      have hMzero : ∀ i j : Fin n, d ≤ (i : ℕ) → (j : ℕ) < d →
          (Qᵀ * A * Q) i j = 0 :=
        fun i j hi hj => deflation_lower_left_zero A Q hQorth d hinv i j hi hj
      set e : Fin n ≃ Fin d ⊕ Fin m := splitEquiv hnm with he
      set M : Matrix (Fin n) (Fin n) ℝ := Qᵀ * A * Q with hMdef
      set M' : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ := Matrix.reindex e e M with hM'
      have hM'zero : M'.toBlocks₂₁ = 0 := by
        ext a b
        simp only [Matrix.toBlocks₂₁, hM', Matrix.reindex_apply, Matrix.submatrix_apply,
          Matrix.of_apply, Matrix.zero_apply]
        apply hMzero
        · have hsum : splitEquiv hnm (e.symm (Sum.inr a)) = Sum.inr a := by
            rw [← he]; exact e.apply_symm_apply _
          have hval := splitEquiv_inr_val hnm hsum
          omega
        · have hsum : splitEquiv hnm (e.symm (Sum.inl b)) = Sum.inl b := by
            rw [← he]; exact e.apply_symm_apply _
          have hval := splitEquiv_inl_val hnm hsum
          have hb := b.2
          omega
      have hM'block : M' = Matrix.fromBlocks M'.toBlocks₁₁ M'.toBlocks₁₂ 0 M'.toBlocks₂₂ := by
        conv_lhs => rw [← Matrix.fromBlocks_toBlocks M']
        rw [hM'zero]
      obtain ⟨U', hU'orth, p', hp'mono, hp'card, hp'zero, hp'spectral⟩ :=
        ih m hmlt M'.toBlocks₂₂
      set Q' : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ := Matrix.reindex e e Q with hQ'
      set A' : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ := Matrix.reindex e e A with hA'
      set V : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ := Q' * embedBlock U' with hV
      set Qfull : Matrix (Fin n) (Fin n) ℝ := Matrix.reindex e.symm e.symm V with hQfull
      have hQfullorth : Qfull ∈ Matrix.orthogonalGroup (Fin n) ℝ := by
        rw [hQfull]
        apply reindex_mem_orthogonal
        rw [hV]
        exact Submonoid.mul_mem _ (reindex_mem_orthogonal e hQorth)
          (embedBlock_mem_orthogonal hU'orth)
      set X : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ :=
        (embedBlock U')ᵀ * M' * embedBlock U' with hX
      have hconj : Qfullᵀ * A * Qfull = Matrix.reindex e.symm e.symm X := by
        have hM'conj : M' = Q'ᵀ * A' * Q' := by
          rw [hM', hMdef, hQ', hA', reindex_conj]
        have hXeq : X = Vᵀ * A' * V := by
          rw [hX, hM'conj, hV]
          rw [Matrix.transpose_mul]
          simp only [mul_assoc]
        rw [hXeq, reindex_conj, ← hQfull, hA', reindex_symm_reindex]
      have hXblock : X = Matrix.fromBlocks M'.toBlocks₁₁ (M'.toBlocks₁₂ * U') 0
          (U'ᵀ * M'.toBlocks₂₂ * U') := by
        rw [hX]
        conv_lhs => rw [hM'block]
        rw [conj_embedBlock_eq]
      have hRentry : ∀ i j : Fin n, (Matrix.reindex e.symm e.symm X) i j = X (e i) (e j) := by
        intro i j
        simp [Matrix.reindex_apply, Matrix.submatrix_apply]
      set q : Fin d ⊕ Fin m → ℕ := Sum.elim (fun _ => 0) (fun a => p' a + 1) with hq
      refine ⟨Qfull, hQfullorth, ?_⟩
      refine ⟨fun i => q (e i), ?_, ?_, ?_, ?_⟩
      · intro i i' hii'
        rcases hei : e i with a | a
        · simp [hq, hei]
        · have heisp : splitEquiv hnm i = Sum.inr a := by rw [← he]; exact hei
          have hia : d + (a : ℕ) = (i : ℕ) := splitEquiv_inr_val hnm heisp
          rcases hei' : e i' with a' | a'
          · have hei'sp : splitEquiv hnm i' = Sum.inl a' := by rw [← he]; exact hei'
            have hia' : (a' : ℕ) = (i' : ℕ) := splitEquiv_inl_val hnm hei'sp
            have ha'2 := a'.2
            have hii'val : (i : ℕ) ≤ (i' : ℕ) := hii'
            omega
          · have hei'sp : splitEquiv hnm i' = Sum.inr a' := by rw [← he]; exact hei'
            have hia' : d + (a' : ℕ) = (i' : ℕ) := splitEquiv_inr_val hnm hei'sp
            have haa' : (a : ℕ) ≤ (a' : ℕ) := by
              have hii'val : (i : ℕ) ≤ (i' : ℕ) := hii'
              omega
            simp only [hq, hei, hei', Sum.elim_inr]
            have := hp'mono (show a ≤ a' from haa')
            omega
      · intro c
        have hcardeq : (Finset.univ.filter (fun i : Fin n => q (e i) = c)).card
            = (Finset.univ.filter (fun x : Fin d ⊕ Fin m => q x = c)).card := by
          rw [← Fintype.card_subtype, ← Fintype.card_subtype]
          exact Fintype.card_congr (Equiv.subtypeEquiv e (fun a => Iff.rfl))
        rw [hcardeq, ← Fintype.card_subtype]
        rw [Fintype.card_congr (Equiv.subtypeSum (p := fun x : Fin d ⊕ Fin m => q x = c))]
        rw [Fintype.card_sum]
        by_cases hc0 : c = 0
        · subst hc0
          have hleft : Fintype.card {a : Fin d // q (Sum.inl a) = 0} = d := by
            simp only [hq, Sum.elim_inl]
            simp [Fintype.card_subtype]
          have hright : Fintype.card {b : Fin m // q (Sum.inr b) = 0} = 0 := by
            simp only [hq, Sum.elim_inr]
            rw [Fintype.card_subtype]
            simp only [Nat.succ_ne_zero, Finset.filter_false, Finset.card_empty]
          rw [hleft, hright]
          omega
        · have hleft : Fintype.card {a : Fin d // q (Sum.inl a) = c} = 0 := by
            simp only [hq, Sum.elim_inl]
            rw [Fintype.card_subtype]
            simp only [Finset.card_eq_zero]
            rw [Finset.filter_eq_empty_iff]
            intro a _
            exact fun h => hc0 h.symm
          have hright : Fintype.card {b : Fin m // q (Sum.inr b) = c} ≤ 2 := by
            simp only [hq, Sum.elim_inr]
            rw [Fintype.card_subtype]
            have hce : ∀ b : Fin m, (p' b + 1 = c) ↔ (p' b = c - 1) := by
              intro b
              omega
            simp only [hce]
            rw [← Fintype.card_subtype, Fintype.card_subtype]
            exact hp'card (c - 1)
          rw [hleft]
          omega
      · intro i j hlt
        rw [hconj, hRentry, hXblock]
        rcases hei : e i with a | a
        · exfalso
          simp only [hq, hei, Sum.elim_inl] at hlt
          exact Nat.not_lt_zero _ hlt
        · rcases hej : e j with b | b
          · simp [Matrix.fromBlocks]
          · simp only [Matrix.fromBlocks_apply₂₂]
            apply hp'zero
            simp only [hq, hei, hej, Sum.elim_inr] at hlt
            omega
      · intro i j hadj hsame
        rcases hei : e i with a | a
        · rcases hej : e j with b | b
          · have heisp : splitEquiv hnm i = Sum.inl a := by rw [← he]; exact hei
            have hejsp : splitEquiv hnm j = Sum.inl b := by rw [← he]; exact hej
            have hia : (a : ℕ) = (i : ℕ) := splitEquiv_inl_val hnm heisp
            have hjb : (b : ℕ) = (j : ℕ) := splitEquiv_inl_val hnm hejsp
            rcases hdle with hd1 | hd2
            · subst hd1
              have ha := a.2
              have hb := b.2
              omega
            · subst hd2
              obtain ⟨p0, q0, hp0, hq0, hno0⟩ := hlead rfl
              have hi0 : (i : ℕ) = 0 := by omega
              have hj1 : (j : ℕ) = 1 := by omega
              have hip0 : i = p0 := Fin.ext (by omega)
              have hjq0 : j = q0 := Fin.ext (by omega)
              have hnoij :
                  NumStability.MatrixNoRealEigenline
                    (NumStability.principalTwoBlock (Qᵀ * A * Q) i j) := by
                simpa [hip0, hjq0] using hno0
              simpa [hQfull, hV, hQ', e] using
                leading_twoBlock_spectral_preserved_after_trailing_conj
                  hnm A Q U' hi0 hj1 hnoij
          · exfalso
            simp only [hq, hei, hej, Sum.elim_inl, Sum.elim_inr] at hsame
            omega
        · rcases hej : e j with b | b
          · have heisp : splitEquiv hnm i = Sum.inr a := by rw [← he]; exact hei
            have hejsp : splitEquiv hnm j = Sum.inl b := by rw [← he]; exact hej
            have hia : d + (a : ℕ) = (i : ℕ) := splitEquiv_inr_val hnm heisp
            have hjb : (b : ℕ) = (j : ℕ) := splitEquiv_inl_val hnm hejsp
            have hb := b.2
            omega
          · have heisp : splitEquiv hnm i = Sum.inr a := by rw [← he]; exact hei
            have hejsp : splitEquiv hnm j = Sum.inr b := by rw [← he]; exact hej
            have hia : d + (a : ℕ) = (i : ℕ) := splitEquiv_inr_val hnm heisp
            have hjb : d + (b : ℕ) = (j : ℕ) := splitEquiv_inr_val hnm hejsp
            have hab : (b : ℕ) = (a : ℕ) + 1 := by omega
            have hsame' : p' a = p' b := by
              simp only [hq, hei, hej, Sum.elim_inr] at hsame
              omega
            have htrail :
                NumStability.MatrixNoRealEigenline
                    (NumStability.principalTwoBlock
                      (U'ᵀ * (Matrix.reindex e e (Qᵀ * A * Q)).toBlocks₂₂ * U') a b) ∧
                  ((U'ᵀ * (Matrix.reindex e e (Qᵀ * A * Q)).toBlocks₂₂ * U') a a -
                      (U'ᵀ * (Matrix.reindex e e (Qᵀ * A * Q)).toBlocks₂₂ * U') b b) ^ 2 +
                    4 * (U'ᵀ * (Matrix.reindex e e (Qᵀ * A * Q)).toBlocks₂₂ * U') a b *
                      (U'ᵀ * (Matrix.reindex e e (Qᵀ * A * Q)).toBlocks₂₂ * U') b a < 0 := by
              simpa [hM', hMdef] using hp'spectral a b hab hsame'
            simpa [hQfull, hV, hQ', e] using
              trailing_twoBlock_spectral_preserved_after_trailing_conj
                hnm A Q U' hia.symm hjb.symm htrail.1

end RealQuasiSchurAux

/-! ### The main theorems (Higham §16.2 (16.4)) -/

/-- **Real quasi-upper-triangular predicate (Higham (16.4)).**  A matrix `R` is
    *quasi-upper-triangular* when there is a block assignment `p : Fin n → ℕ` that
    is monotone (blocks are contiguous intervals), assigns at most `2` indices to
    each block (the diagonal blocks are `1×1` or `2×2`), and makes `R i j = 0`
    whenever row `i` is in a strictly later block than column `j` (everything
    strictly below the block diagonal vanishes).  This is the block-upper-
    triangular form with `1×1`/`2×2` diagonal blocks of Higham, *Accuracy and
    Stability of Numerical Algorithms*, 2nd ed., §16.2, equation (16.4). -/
def IsRealQuasiUpperTriangular {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  RealQuasiSchurAux.IsQuasiUpperTriangular R

/-- **Real quasi-triangular (quasi-)Schur decomposition (Higham §16.2 (16.4)).**

    Every real square matrix `A` is orthogonally similar to a real
    quasi-upper-triangular matrix `R`: there exist an orthogonal `Q` (`QᵀQ = 1`)
    and a matrix `R` that is block-upper-triangular with `1×1` and `2×2` diagonal
    blocks (`IsRealQuasiUpperTriangular`), with `Qᵀ A Q = R`.

    This is the real Schur decomposition of Higham, *Accuracy and Stability of
    Numerical Algorithms*, 2nd ed., §16.2, equation (16.4).  The `1×1` diagonal
    blocks carry the real eigenvalues and the `2×2` blocks the complex-conjugate
    eigenvalue pairs.  Proof by the variable-`d` (`d ∈ {1, 2}`) orthogonal
    deflation induction: peel a real invariant subspace of dimension `d`, extend
    an orthonormal basis of it to an orthogonal `Q`, conjugate to zero the block
    strictly below the leading `d` columns, and recurse on the trailing block. -/
theorem real_quasi_schur {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ (Q R : Matrix (Fin n) (Fin n) ℝ), Q ∈ Matrix.orthogonalGroup (Fin n) ℝ ∧
      Qᵀ * A * Q = R ∧ IsRealQuasiUpperTriangular R := by
  obtain ⟨Q, hQ, hqt⟩ :=
    RealQuasiSchurAux.exists_orthogonal_conj_quasiUpperTriangular n A
  exact ⟨Q, Qᵀ * A * Q, hQ, rfl, hqt⟩

/-- **Real quasi-triangular Schur decomposition, unpacked block structure
    (Higham §16.2 (16.4)).**

    Explicit form of `real_quasi_schur`: every real square matrix `A` admits an
    orthogonal `Q` and a block assignment `p : Fin n → ℕ` such that `R := Qᵀ A Q`
    is block-upper-triangular for `p`, namely:

    * `p` is monotone — the blocks `p⁻¹(c)` are contiguous intervals;
    * every block has at most `2` indices — the diagonal blocks are `1×1` or `2×2`
      (the `2×2` blocks carry complex-conjugate eigenvalue pairs, the `1×1` blocks
      the real eigenvalues);
    * `R i j = 0` whenever `p j < p i`, i.e. `R` vanishes strictly below the block
      diagonal.

    This exposes the full content of the real Schur decomposition of Higham,
    *Accuracy and Stability of Numerical Algorithms*, 2nd ed., §16.2, eq (16.4),
    with the diagonal-block-size `≤ 2` structure made explicit and honest. -/
theorem real_quasi_schur_blocks {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ (Q : Matrix (Fin n) (Fin n) ℝ) (p : Fin n → ℕ),
      Q ∈ Matrix.orthogonalGroup (Fin n) ℝ ∧
      Monotone p ∧
      (∀ c : ℕ, (Finset.univ.filter (fun i => p i = c)).card ≤ 2) ∧
      (∀ i j : Fin n, p j < p i → (Qᵀ * A * Q) i j = 0) := by
  obtain ⟨Q, hQ, p, hmono, hcard, hzero⟩ :=
    RealQuasiSchurAux.exists_orthogonal_conj_quasiUpperTriangular n A
  exact ⟨Q, p, hQ, hmono, hcard, hzero⟩

/-- **Real quasi-triangular Schur decomposition with `2 x 2` spectral
    certificates (Higham §16.2 (16.4)).**

    Strengthens `real_quasi_schur_blocks`: every adjacent pair in the same
    constructed `2 x 2` block has no real eigenline, hence negative
    discriminant.  This is the source-facing certificate that such blocks carry
    complex-conjugate eigenvalue pairs; it does not by itself assert Sylvester
    separation from another matrix. -/
theorem real_quasi_schur_blocks_twoBlockSpectral {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ (Q : Matrix (Fin n) (Fin n) ℝ) (p : Fin n → ℕ),
      Q ∈ Matrix.orthogonalGroup (Fin n) ℝ ∧
      Monotone p ∧
      (∀ c : ℕ, (Finset.univ.filter (fun i => p i = c)).card ≤ 2) ∧
      (∀ i j : Fin n, p j < p i → (Qᵀ * A * Q) i j = 0) ∧
      HasRealQuasiSchurTwoBlockSpectral (Qᵀ * A * Q) p := by
  obtain ⟨Q, hQ, p, hmono, hcard, hzero, hspectral⟩ :=
    RealQuasiSchurAux.exists_orthogonal_conj_quasiUpperTriangular_twoBlockSpectral n A
  exact ⟨Q, p, hQ, hmono, hcard, hzero, hspectral⟩

end NumStability
