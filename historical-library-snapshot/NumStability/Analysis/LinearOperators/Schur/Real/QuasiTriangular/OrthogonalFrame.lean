import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLin
import NumStability.Analysis.LinearOperators.Schur.Real.InvariantSubspace.Existence
import NumStability.Analysis.LinearOperators.Schur.Real.InvariantSubspace.TwoByTwo
import NumStability.Analysis.LinearOperators.Schur.Real.QuasiTriangular.Deflation

/-!
# Analysis.LinearOperators.Schur.Real.QuasiTriangular.OrthogonalFrame

W05 semantic leaf. Declaration commands are copied byte-identically from the frozen C0004 owners.
-/

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






open scoped BigOperators Matrix
open Module

namespace NumStability














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





/-! ### Block-diagonal orthogonal re-embedding over a sum index

Re-embedding an `m×m` orthogonal matrix `U` as the trailing block of a
`(Fin d ⊕ Fin m)`-indexed matrix with an identity `d×d` leading block, used to
lift the trailing-block reduction of Higham §16.2 (16.4) to the full space. -/

variable {d m : ℕ}





































/-! ### Deflation: an invariant leading block zeros the lower-left block

If the first `d` columns of an orthogonal `Q` span an `A`-invariant subspace,
then conjugating `A` by `Q` zeros the block strictly below those columns. -/

variable {n : ℕ}






























































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



































/-! ### The order-compatible splitting equivalence `Fin n ≃ Fin d ⊕ Fin m`

For `d + m = n`, the equivalence `splitEquiv` sends the first `d` indices to the
`Fin d` summand and the rest to the `Fin m` summand, order-preservingly. -/



































































/-! ### Block conjugation by the re-embedded trailing orthogonal matrix -/


















































































































































































































































































































































































/-! ### The variable-`d` orthogonal deflation induction (Higham (16.4)) -/

































































































































































































































































































































































































































































end RealQuasiSchurAux

/-! ### The main theorems (Higham §16.2 (16.4)) -/
















































































end NumStability
