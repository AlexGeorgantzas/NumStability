import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLin
import NumStability.Analysis.LinearOperators.Schur.Real.InvariantSubspace.Existence
import NumStability.Analysis.LinearOperators.Schur.Real.InvariantSubspace.TwoByTwo
import NumStability.Analysis.LinearOperators.Schur.Real.QuasiTriangular.Basic
import NumStability.Analysis.LinearOperators.Schur.Real.QuasiTriangular.BlockEmbedding
import NumStability.Analysis.LinearOperators.Schur.Real.QuasiTriangular.Deflation
import NumStability.Analysis.LinearOperators.Schur.Real.QuasiTriangular.OrthogonalFrame
import NumStability.Analysis.LinearOperators.Schur.Real.QuasiTriangular.Reindex
import NumStability.Analysis.LinearOperators.Schur.Real.QuasiTriangular.TrailingConjugation

/-!
# Analysis.LinearOperators.Schur.Real.QuasiTriangular.Existence

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
















































































end NumStability
