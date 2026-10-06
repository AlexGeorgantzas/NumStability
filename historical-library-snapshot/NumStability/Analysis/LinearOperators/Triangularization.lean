-- Analysis/LinearOperators/Triangularization.lean
--
-- Basis and quotient tools for finite-dimensional triangularization.

import Mathlib.LinearAlgebra.Basis.Flag
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Finite-dimensional triangularization

Defines `basisUpperTriangularizes`, proves quotient/basis gluing lemmas, and
constructs upper-triangular coordinate matrices over algebraically closed fields.
-/

namespace NumStability

/-- A basis upper-triangularizes an endomorphism when each basis vector is
    mapped into the span of itself and earlier basis vectors.  This is the
    flag-level algebraic bridge needed for the triangularization route in
    Higham Problem 6.8. -/
def basisUpperTriangularizes {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (f : Module.End K V) : Prop :=
  forall j : Fin n, Membership.mem (Module.Basis.flag b (Fin.succ j)) (f (b j))

/-- A flag-level upper-triangularizing basis gives an upper-triangular
    coordinate matrix in Mathlib's `BlockTriangular id` sense. -/
theorem basisUpperTriangularizes_blockTriangular_toMatrix
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    {b : Module.Basis (Fin n) K V} {f : Module.End K V}
    (h : basisUpperTriangularizes b f) :
    (LinearMap.toMatrix b b f).BlockTriangular id := by
  intro i j hji
  have hij : Fin.succ j <= Fin.castSucc i := by
    exact Nat.succ_le_iff.mpr hji
  have hz : Membership.mem (LinearMap.ker (b.coord i)) (f (b j)) :=
    (Module.Basis.flag_le_ker_coord b hij) (h j)
  change b.repr (f (b j)) i = 0 at hz
  simpa [LinearMap.toMatrix_apply] using hz

/-- Fin-indexed version of Mathlib's `Module.Basis.sumQuot`: a basis of an
    invariant subspace, followed by a lifted quotient basis, reindexed by
    `Fin (m+n)`.  This is the basis-combination primitive for the finite
    triangularization induction used by Higham Problem 6.8. -/
noncomputable def sumQuotFinBasis
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {m n : ℕ} {W : Submodule K V}
    (bW : Module.Basis (Fin m) K W)
    (bQ : Module.Basis (Fin n) K (V ⧸ W)) :
    Module.Basis (Fin (m + n)) K V :=
  (bW.sumQuot bQ).reindex finSumFinEquiv

/-- If an endomorphism preserves a subspace, and both the restricted map and
    the induced quotient map are upper triangular in chosen bases, then the
    `sumQuotFinBasis` glued basis upper triangularizes the original map. -/
theorem sumQuotFinBasis_blockTriangular_toMatrix
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {m n : ℕ} {W : Submodule K V} {f : Module.End K V}
    (hW : W <= W.comap f)
    {bW : Module.Basis (Fin m) K W}
    {bQ : Module.Basis (Fin n) K (V ⧸ W)}
    (hTW : (LinearMap.toMatrix bW bW
      (f.restrict (fun _ hx => hW hx))).BlockTriangular id)
    (hTQ : (LinearMap.toMatrix bQ bQ (W.mapQ W f hW)).BlockTriangular id) :
    (LinearMap.toMatrix (sumQuotFinBasis bW bQ) (sumQuotFinBasis bW bQ) f).BlockTriangular id := by
  intro i j hij
  refine Fin.addCases (motive := fun i => ∀ j, j < i →
      LinearMap.toMatrix (sumQuotFinBasis bW bQ) (sumQuotFinBasis bW bQ) f i j = 0)
    ?_ ?_ i j hij
  · intro iW j hij
    refine Fin.addCases (motive := fun j => j < Fin.castAdd n iW →
        LinearMap.toMatrix (sumQuotFinBasis bW bQ) (sumQuotFinBasis bW bQ) f
          (Fin.castAdd n iW) j = 0) ?_ ?_ j hij
    · intro jW hjW
      have hsmall : jW < iW := by
        exact hjW
      simp [sumQuotFinBasis, LinearMap.toMatrix_apply, Module.Basis.coe_reindex,
        Module.Basis.repr_reindex, Finsupp.mapDomain_equiv_apply]
      rw [Module.Basis.sumQuot_repr_inl_of_mem bW bQ]
      simpa [LinearMap.toMatrix_apply] using hTW (i := iW) (j := jW) hsmall
    · intro jQ hjQ
      exfalso
      have hv : m + jQ.val < iW.val := by
        exact hjQ
      have hi : iW.val < m := iW.isLt
      omega
  · intro iQ j hij
    refine Fin.addCases (motive := fun j => j < Fin.natAdd m iQ →
        LinearMap.toMatrix (sumQuotFinBasis bW bQ) (sumQuotFinBasis bW bQ) f
          (Fin.natAdd m iQ) j = 0) ?_ ?_ j hij
    · intro jW _hjW
      simp [sumQuotFinBasis, LinearMap.toMatrix_apply, Module.Basis.coe_reindex,
        Module.Basis.repr_reindex, Finsupp.mapDomain_equiv_apply]
      have hmem : f ↑(bW jW) ∈ W := hW (Submodule.coe_mem (bW jW))
      have hmk : (Submodule.Quotient.mk (f ↑(bW jW)) : V ⧸ W) = 0 := by
        rw [Submodule.Quotient.mk_eq_zero]
        exact hmem
      simp [hmk]
    · intro jQ hjQ
      have hsmall : jQ < iQ := by
        have hv : m + jQ.val < m + iQ.val := by
          exact hjQ
        omega
      simp [sumQuotFinBasis, LinearMap.toMatrix_apply, Module.Basis.coe_reindex,
        Module.Basis.repr_reindex, Finsupp.mapDomain_equiv_apply]
      have hbj :
          bQ jQ = (Submodule.Quotient.mk ((bW.sumQuot bQ) (Sum.inr jQ)) : V ⧸ W) := by
        exact (Module.Basis.sumQuot_inr bW bQ jQ).symm
      have hmap :
          (W.mapQ W f hW) (bQ jQ) =
            (Submodule.Quotient.mk (f ((bW.sumQuot bQ) (Sum.inr jQ))) : V ⧸ W) := by
        rw [hbj, Submodule.mapQ_apply]
      rw [← hmap]
      simpa [LinearMap.toMatrix_apply] using hTQ (i := iQ) (j := jQ) hsmall

/-- An eigenvector spans an invariant line.  This is the first subspace in
    the quotient induction route for triangularizing finite-dimensional
    complex endomorphisms in Higham Problem 6.8. -/
theorem eigenvector_span_le_comap
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {f : Module.End K V} {μ : K} {v : V}
    (hv : f.HasEigenvector μ v) :
    (K ∙ v) <= (K ∙ v).comap f := by
  rw [Submodule.span_singleton_le_iff_mem]
  rw [Submodule.mem_comap]
  rw [hv.apply_eq_smul]
  exact Submodule.smul_mem (K ∙ v) μ (Submodule.mem_span_singleton_self v)

/-- Every one-by-one matrix is upper triangular. -/
theorem finOne_blockTriangular
    {K : Type*} [Zero K] (M : Matrix (Fin 1) (Fin 1) K) :
    M.BlockTriangular id := by
  intro i j hij
  fin_cases i
  fin_cases j
  simp at hij

/-- Reindexing a finite basis along a cardinality equality preserves
    block-triangularity of the coordinate matrix. -/
theorem blockTriangular_reindex_finCongr
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {a b : ℕ} (h : a = b)
    {B : Module.Basis (Fin a) K V} {f : Module.End K V}
    (hB : (LinearMap.toMatrix B B f).BlockTriangular id) :
    (LinearMap.toMatrix (B.reindex (finCongr h)) (B.reindex (finCongr h)) f).BlockTriangular id := by
  cases h
  simpa using hB

/-- Algebraic triangularization bridge: over an algebraically closed field,
    every finite-dimensional endomorphism has a finite basis in which its
    coordinate matrix is upper triangular (`BlockTriangular id`).  This closes
    the basis-existence side of the triangularization route used for Higham
    Problem 6.8. -/
theorem exists_blockTriangular_toMatrix_of_finrank
    {K : Type*} [Field K] [IsAlgClosed K] :
    ∀ n : ℕ, ∀ {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V],
      Module.finrank K V = n →
      ∀ f : Module.End K V,
        ∃ b : Module.Basis (Fin n) K V,
          (LinearMap.toMatrix b b f).BlockTriangular id := by
  intro n
  induction n with
  | zero =>
      intro V _ _ _ hfin _f
      let b : Module.Basis (Fin 0) K V :=
        basisOfFinrankZero (K := K) (V := V) (ι := Fin 0) hfin
      refine ⟨b, ?_⟩
      intro i _j _hij
      exact Fin.elim0 i
  | succ n ih =>
      intro V _ _ _ hfin f
      have hpos : 0 < Module.finrank K V := by
        rw [hfin]
        exact Nat.succ_pos n
      haveI : Nontrivial V := Module.finrank_pos_iff.mp hpos
      obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue f
      obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
      have hvne : v ≠ 0 := (Module.End.hasEigenvector_iff.mp hv).2
      let W : Submodule K V := K ∙ v
      have hW : W <= W.comap f := by
        simpa [W] using eigenvector_span_le_comap (f := f) hv
      have hfinW : Module.finrank K W = 1 := by
        simpa [W] using finrank_span_singleton (K := K) hvne
      have hquot : Module.finrank K (V ⧸ W) = n := by
        have hsum := Submodule.finrank_quotient_add_finrank (R := K) (M := V) W
        rw [hfinW, hfin] at hsum
        omega
      let vv : W := ⟨v, Submodule.mem_span_singleton_self v⟩
      have hvv_ne : vv ≠ 0 := by
        intro hzero
        apply hvne
        exact congrArg Subtype.val hzero
      let bW : Module.Basis (Fin 1) K W :=
        FiniteDimensional.basisSingleton (Fin 1) hfinW vv hvv_ne
      have hTW :
          (LinearMap.toMatrix bW bW
            (f.restrict (fun _ hx => hW hx))).BlockTriangular id :=
        finOne_blockTriangular _
      obtain ⟨bQ, hTQ⟩ :=
        ih (V := V ⧸ W) hquot (W.mapQ W f hW)
      let b0 : Module.Basis (Fin (1 + n)) K V :=
        sumQuotFinBasis (K := K) (V := V) (m := 1) (n := n) (W := W) bW bQ
      have hb0 : (LinearMap.toMatrix b0 b0 f).BlockTriangular id :=
        sumQuotFinBasis_blockTriangular_toMatrix
          (K := K) (V := V) (m := 1) (n := n) (W := W) hW hTW hTQ
      have hdim : 1 + n = Nat.succ n := by omega
      let b : Module.Basis (Fin (Nat.succ n)) K V := b0.reindex (finCongr hdim)
      refine ⟨b, ?_⟩
      exact blockTriangular_reindex_finCongr hdim hb0
end NumStability
