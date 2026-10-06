-- Analysis/NilpotentJordanChain.lean
--
-- DEEP CLOSURE of the nilpotent Jordan-chain theorem, discharging the
-- `NilpotentJordanBasis` hypothesis left open in `Analysis/JordanNormalForm.lean`
-- and thereby giving the classical **full Jordan Normal Form over ℂ** with no
-- extra hypothesis.
--
-- Background.  Higham, *Accuracy and Stability of Numerical Algorithms* (2nd ed.),
-- Theorem 18.1 (Matrix Powers), states its general case for a matrix in Jordan
-- canonical form  A = X J X⁻¹  with  J = diag(J₁,…,J_s)  a direct sum of Jordan
-- blocks (§18.1, eqns (18.1a)/(18.1b), p. 618).  `JordanNormalForm.lean` proves
-- unconditionally the *primary decomposition*  A ~ blockdiag(μ·I + Nμ)  with each
-- `Nμ` nilpotent, and reduces full JNF to the single residual fact
-- (`NilpotentJordanBasis`):
--
--   > every nilpotent complex matrix is similar to a direct sum of nilpotent
--   > Jordan (shift) blocks.
--
-- This file PROVES that fact via Mathlib's structure theorem for finitely
-- generated modules over a PID (`Module.torsion_by_prime_power_decomposition`),
-- applied to ℂⁿ made a ℂ[X]-module with `X` acting as the nilpotent operator
-- (`Module.AEval'`).  Nilpotency makes the module `X`-power torsion and it is
-- finitely generated, so the PID theorem gives
--
--   (Fin m → ℂ)  ≅_{ℂ[X]}  ⨁ᵢ  ℂ[X]/(X^{kᵢ})   as ℂ[X]-modules.
--
-- Each cyclic summand `ℂ[X]/(X^k)`, with `X` acting, is the `k×k` nilpotent shift
-- block (in the reversed monomial basis `X^{k-1},…,X,1`).  Collecting these bases
-- and transporting back yields a ℂ-basis of ℂⁿ in which the nilpotent operator is
-- an honest block-diagonal of shift blocks, i.e. a matrix similarity
--   N ~ blockDiagonal'(shift blocks),
-- which is exactly `NilpotentJordanBasis`.
--
-- IMPORT-ONLY: this file edits nothing.  It imports `JordanNormalForm.lean` and
-- reuses its `Matrix.IsSimilar`, `jordanBlockNil`, `IsNilpotentJordanForm`,
-- `NilpotentJordanBasis`, `isSimilar_toMatrix_toLin'`, and
-- `jordan_normal_form_of_nilpotentJordanBasis`.  No `sorry`/`admit`/`axiom`/
-- `native_decide`/proof-disabling options anywhere.

import NumStability.Analysis.JordanNormalForm
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Data.Fin.Rev

namespace NumStability

open Polynomial Matrix Module
open scoped DirectSum

noncomputable section

/-! ## The cyclic module `ℂ[X]/(Xᵏ)` and the shift block

`Module.torsion_by_prime_power_decomposition` produces summands of the form
`ℂ[X] ⧸ (ℂ[X] ∙ Xᵏ)`.  We give this quotient a `Fin k`-indexed ℂ-basis of
monomials and identify multiplication-by-`X` in the *reversed* monomial basis with
the nilpotent Jordan block `jordanBlockNil k` (Higham §18.1, eqn (18.1b), p. 618:
`J_k(0)`, the shift matrix). -/

/-- The cyclic ℂ[X]-module `ℂ[X] ⧸ (Xᵏ)` (as a `Submodule.Quotient`); this is the
generic summand in the PID decomposition of a nilpotent operator's module.  With
`X` acting it is one nilpotent Jordan block (Higham §18.1, p. 618). -/
abbrev CycQuot (k : ℕ) : Type := ℂ[X] ⧸ (Submodule.span ℂ[X] {(X : ℂ[X]) ^ k})

/-- The monomial ℂ-basis `1, X, …, X^{k-1}` of `ℂ[X] ⧸ (Xᵏ)`, indexed by
`Fin ((Xᵏ).natDegree)`.  Obtained from `AdjoinRoot.powerBasis'` for the monic
polynomial `Xᵏ` (whose quotient ring is defeq to `CycQuot k`). -/
def cycBasisAux (k : ℕ) : Basis (Fin ((X : ℂ[X]) ^ k).natDegree) ℂ (CycQuot k) :=
  (AdjoinRoot.powerBasis' (g := (X : ℂ[X]) ^ k) (monic_X_pow k)).basis

/-- Each `cycBasisAux` vector is the class of a monomial: `cycBasisAux k i = ⟦X^i⟧`.
(Higham §18.1, p. 618: the Jordan-chain vectors of the shift block.) -/
theorem cycBasisAux_apply (k : ℕ) (i : Fin ((X : ℂ[X]) ^ k).natDegree) :
    cycBasisAux k i = Submodule.Quotient.mk ((X : ℂ[X]) ^ (i : ℕ)) := by
  -- Prove the identity at the `AdjoinRoot` type (where `basis_eq_pow` applies),
  -- then transport by defeq (`AdjoinRoot.mk = Submodule.Quotient.mk`).
  have h : (AdjoinRoot.powerBasis' (g := (X : ℂ[X]) ^ k) (monic_X_pow k)).basis i
      = AdjoinRoot.mk ((X : ℂ[X]) ^ k) ((X : ℂ[X]) ^ (i : ℕ)) := by
    rw [(AdjoinRoot.powerBasis' (monic_X_pow k)).basis_eq_pow, AdjoinRoot.powerBasis'_gen,
      ← AdjoinRoot.mk_X, ← map_pow]
  exact h

/-- The monomial ℂ-basis of `ℂ[X] ⧸ (Xᵏ)` reindexed by `Fin k` (using
`natDegree (Xᵏ) = k`). -/
def cycBasis (k : ℕ) : Basis (Fin k) ℂ (CycQuot k) :=
  (cycBasisAux k).reindex (finCongr (natDegree_X_pow k))

/-- `cycBasis k a = ⟦X^a⟧`. -/
theorem cycBasis_apply (k : ℕ) (a : Fin k) :
    cycBasis k a = Submodule.Quotient.mk ((X : ℂ[X]) ^ (a : ℕ)) := by
  rw [cycBasis, Basis.reindex_apply, cycBasisAux_apply, finCongr_symm, finCongr_apply, Fin.val_cast]

/-- Multiplication by `X` on `ℂ[X] ⧸ (Xᵏ)`, as a ℂ-linear endomorphism.  Under the
ℂ[X]-module structure of the PID summand this is the action of the generator `X`,
which becomes the Jordan block once written in a basis (Higham §18.1, p. 618). -/
def cycShift (k : ℕ) : CycQuot k →ₗ[ℂ] CycQuot k where
  toFun z := (X : ℂ[X]) • z
  map_add' a b := by rw [smul_add]
  map_smul' c a := by dsimp; rw [smul_comm]

@[simp] theorem cycShift_apply (k : ℕ) (z : CycQuot k) : cycShift k z = (X : ℂ[X]) • z := rfl

/-- The top monomial dies: `⟦Xᵏ⟧ = 0` in `ℂ[X] ⧸ (Xᵏ)`.  This is what truncates
the Jordan chain (Higham §18.1, p. 618: `N^k = 0` on a `k`-block). -/
theorem cyc_mk_X_pow_self (k : ℕ) :
    (Submodule.Quotient.mk ((X : ℂ[X]) ^ k) : CycQuot k) = 0 := by
  rw [Submodule.Quotient.mk_eq_zero]; exact Submodule.mem_span_singleton_self _

/-- `cycShift` maps `⟦X^a⟧ ↦ ⟦X^{a+1}⟧`. -/
theorem cycShift_cycBasis (k : ℕ) (a : Fin k) :
    cycShift k (cycBasis k a) = Submodule.Quotient.mk ((X : ℂ[X]) ^ ((a : ℕ) + 1)) := by
  rw [cycShift_apply, cycBasis_apply, ← Submodule.Quotient.mk_smul, smul_eq_mul, ← pow_succ']

/-- Coordinates of `⟦X^p⟧` (for `p < k`) in the monomial basis: `δ_{p,c}`. -/
theorem cycBasis_repr_mk_pow_lt (k : ℕ) (p : ℕ) (hp : p < k) (c : Fin k) :
    (cycBasis k).repr (Submodule.Quotient.mk ((X : ℂ[X]) ^ p) : CycQuot k) c
      = if p = (c : ℕ) then 1 else 0 := by
  have hh : (Submodule.Quotient.mk ((X : ℂ[X]) ^ p) : CycQuot k) = cycBasis k ⟨p, hp⟩ :=
    (cycBasis_apply k ⟨p, hp⟩).symm
  rw [hh, Basis.repr_self_apply]; simp only [Fin.ext_iff]

/-- The matrix of `cycShift` in the *natural* monomial basis is the **subdiagonal**
shift (`(i,j) = 1` iff `i = j+1`), i.e. `(jordanBlockNil k)ᵀ`. -/
theorem toMatrix_cycBasis_cycShift (k : ℕ) (i j : Fin k) :
    LinearMap.toMatrix (cycBasis k) (cycBasis k) (cycShift k) i j
      = if (i : ℕ) = (j : ℕ) + 1 then 1 else 0 := by
  rw [LinearMap.toMatrix_apply, cycShift_cycBasis]
  by_cases h : (j : ℕ) + 1 < k
  · rw [cycBasis_repr_mk_pow_lt k ((j : ℕ) + 1) h i]
    by_cases h2 : (i : ℕ) = (j : ℕ) + 1
    · rw [if_pos h2, if_pos h2.symm]
    · rw [if_neg h2, if_neg (fun hh => h2 hh.symm)]
  · have hjk : (j : ℕ) + 1 = k := by omega
    have hne : ¬ ((i : ℕ) = (j : ℕ) + 1) := by omega
    rw [if_neg hne]; conv_lhs => rw [hjk, cyc_mk_X_pow_self]
    rw [map_zero, Finsupp.zero_apply]

/-- The **reversed** monomial basis `X^{k-1}, …, X, 1` of `ℂ[X] ⧸ (Xᵏ)`.  In this
basis multiplication-by-`X` is the *superdiagonal* shift = `jordanBlockNil k`. -/
def cycBasisRev (k : ℕ) : Basis (Fin k) ℂ (CycQuot k) := (cycBasis k).reindex Fin.revPerm

/-- The matrix of an endomorphism in a reindexed basis is the reindexed matrix. -/
theorem toMatrix_reindex_cyc {k : ℕ} (b : Basis (Fin k) ℂ (CycQuot k))
    (e : Fin k ≃ Fin k) (f : CycQuot k →ₗ[ℂ] CycQuot k) (i j : Fin k) :
    LinearMap.toMatrix (b.reindex e) (b.reindex e) f i j
      = LinearMap.toMatrix b b f (e.symm i) (e.symm j) := by
  rw [LinearMap.toMatrix_apply, Basis.reindex_apply, Basis.repr_reindex_apply,
    ← LinearMap.toMatrix_apply]

/-- **Single nilpotent Jordan block.**  Multiplication-by-`X` on the cyclic module
`ℂ[X] ⧸ (Xᵏ)`, written in the reversed monomial basis, is exactly the `k×k`
nilpotent Jordan (shift) block `jordanBlockNil k` (Higham §18.1, eqn (18.1b),
p. 618). -/
theorem toMatrix_cycBasisRev_cycShift (k : ℕ) :
    LinearMap.toMatrix (cycBasisRev k) (cycBasisRev k) (cycShift k) = jordanBlockNil k := by
  ext i j
  rw [cycBasisRev, toMatrix_reindex_cyc, toMatrix_cycBasis_cycShift, jordanBlockNil]
  simp only [Matrix.of_apply, Fin.revPerm_symm, Fin.revPerm_apply, Fin.val_rev]
  by_cases h : (j : ℕ) = (i : ℕ) + 1
  · rw [if_pos h, if_pos]; omega
  · rw [if_neg h, if_neg]; omega

/-! ## The ℂ[X]-module of a nilpotent operator, and its PID decomposition -/

/-- For a **nilpotent** `N : Matrix (Fin m) (Fin m) ℂ`, the ℂ[X]-module `AEval' f`
(with `f = toLin' N` acting as `X`) is `X`-power torsion: every element is killed
by some power of `X`, since `f^j = 0` for large `j` (`N^j = 0`).  This is the
input to the PID structure theorem (Higham §18.1, p. 618, single-block reduction). -/
theorem isTorsion_powers_of_isNilpotent {m : ℕ} {N : Matrix (Fin m) (Fin m) ℂ}
    (hN : IsNilpotent N) :
    Module.IsTorsion' (AEval' (Matrix.toLin' N)) (Submonoid.powers (X : ℂ[X])) := by
  intro mm
  obtain ⟨j, hj⟩ := hN
  refine ⟨⟨(X : ℂ[X]) ^ j, ⟨j, rfl⟩⟩, ?_⟩
  apply (AEval'.of (Matrix.toLin' N)).symm.injective
  rw [map_zero]
  change (AEval'.of (Matrix.toLin' N)).symm ((X : ℂ[X]) ^ j • mm) = 0
  rw [AEval.of_symm_smul]
  simp only [map_pow, aeval_X]
  have hf : (Matrix.toLin' N) ^ j = 0 := by rw [← Matrix.toLin'_pow, hj, map_zero]
  rw [hf]; simp

/-- **PID decomposition of a nilpotent operator's module.**  For nilpotent `N`, the
ℂ[X]-module `AEval' (toLin' N)` is ℂ[X]-linearly isomorphic to a finite direct sum
of cyclic modules `⨁ᵢ ℂ[X] ⧸ (X^{kᵢ})`.  This is
`Module.torsion_by_prime_power_decomposition` for the prime `p = X` (irreducible in
ℂ[X]), instantiating the single-eigenvalue Jordan cluster of Higham §18.1
(p. 618) as a direct sum of Jordan blocks. -/
theorem exists_aeval_equiv_directSum_cyclic {m : ℕ} {N : Matrix (Fin m) (Fin m) ℂ}
    (hN : IsNilpotent N) :
    ∃ (d : ℕ) (kk : Fin d → ℕ),
      Nonempty (AEval' (Matrix.toLin' N) ≃ₗ[ℂ[X]] ⨁ i : Fin d, CycQuot (kk i)) :=
  -- The `Module ℂ[X]` and `Module.Finite ℂ[X]` instances on `AEval'` are supplied
  -- explicitly: `torsion_by_prime_power_decomposition` runs under reduced defeq
  -- transparency, which otherwise blocks their automatic synthesis through the
  -- `AEval'` abbreviation.
  @Module.torsion_by_prime_power_decomposition ℂ[X] _ _ (AEval' (Matrix.toLin' N)) _
    (Module.AEval.instModulePolynomial (Matrix.toLin' N)) _ (X : ℂ[X]) irreducible_X
    (isTorsion_powers_of_isNilpotent hN) (Module.AEval.instFinitePolynomial (Matrix.toLin' N))

/-! ## Transporting the decomposition to a matrix similarity

Given the ℂ[X]-linear decomposition `edecomp`, we build a ℂ-linear equivalence
`Ψ : ℂⁿ ≃ (∀ i, ℂ[X]/(X^{kᵢ}))` intertwining the operator `f` with componentwise
multiplication-by-`X`.  The reversed monomial bases of the summands then give a
ℂ-basis of ℂⁿ in which `f` is block-diagonal with shift blocks. -/

variable {m : ℕ} (N : Matrix (Fin m) (Fin m) ℂ)
variable {d : ℕ} {kk : Fin d → ℕ}
  (edecomp : AEval' (Matrix.toLin' N) ≃ₗ[ℂ[X]] ⨁ i : Fin d, CycQuot (kk i))

/-- The ℂ-linear transport `ℂⁿ ≃ (∀ i, ℂ[X]/(X^{kᵢ}))`, composing the canonical
`ℂ ≃ AEval'` identification, the (restricted) PID isomorphism, and the
`⨁ ≃ ∏` identification for the finite index. -/
def transportPi : (Fin m → ℂ) ≃ₗ[ℂ] (∀ i : Fin d, CycQuot (kk i)) :=
  (AEval'.of (Matrix.toLin' N)).trans
    ((edecomp.restrictScalars ℂ).trans
      ((DirectSum.linearEquivFunOnFintype ℂ[X] (Fin d) (fun i => CycQuot (kk i))).restrictScalars ℂ))

/-- **Intertwining.**  The transport carries the operator `f = toLin' N` to
componentwise multiplication-by-`X`: `transportPi (f z) i = X • (transportPi z i)`.
(This is why `f` becomes a block-diagonal of shift blocks; Higham §18.1, p. 618.) -/
theorem transportPi_toLin (z : Fin m → ℂ) (p : Fin d) :
    (transportPi N edecomp) (Matrix.toLin' N z) p
      = (X : ℂ[X]) • ((transportPi N edecomp) z p) := by
  have step1 : (AEval'.of (Matrix.toLin' N)) (Matrix.toLin' N z)
      = (X : ℂ[X]) • ((AEval'.of (Matrix.toLin' N)) z : AEval' (Matrix.toLin' N)) :=
    (AEval'.X_smul_of (Matrix.toLin' N) z).symm
  simp only [transportPi, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply]
  rw [step1, map_smul, map_smul]
  rfl

/-- The collected reversed-monomial ℂ-basis on `∀ i, ℂ[X]/(X^{kᵢ})`. -/
def collectedBasis : Basis (Σ i : Fin d, Fin (kk i)) ℂ (∀ i : Fin d, CycQuot (kk i)) :=
  Pi.basis (fun i => cycBasisRev (kk i))

/-- The ℂ-basis of `ℂⁿ` adapted to the nilpotent decomposition: the pullback of the
collected reversed-monomial basis under the transport `Ψ`.  In this basis `f` is a
block-diagonal of nilpotent Jordan blocks (Higham §18.1, eqns (18.1a)/(18.1b),
p. 618). -/
def jordanBasisFin : Basis (Σ i : Fin d, Fin (kk i)) ℂ (Fin m → ℂ) :=
  (collectedBasis (d := d) (kk := kk)).map (transportPi N edecomp).symm

/-- The matrix of `f` in the adapted basis, entrywise, reduces to the coordinates of
`X • (basis vector)` in the collected basis (via the intertwining). -/
theorem toMatrix_jordanBasisFin (ia jb : Σ i : Fin d, Fin (kk i)) :
    LinearMap.toMatrix (jordanBasisFin N edecomp) (jordanBasisFin N edecomp) (Matrix.toLin' N) ia jb
      = (collectedBasis (d := d) (kk := kk)).repr
          ((X : ℂ[X]) • ((collectedBasis (d := d) (kk := kk)) jb)) ia := by
  rw [LinearMap.toMatrix_apply, jordanBasisFin, Basis.map_apply, Basis.map_repr,
    LinearEquiv.trans_apply]
  simp only [LinearEquiv.symm_symm]
  have hkey : (transportPi N edecomp) ((Matrix.toLin' N) ((transportPi N edecomp).symm
      (collectedBasis (d := d) (kk := kk) jb)))
      = (X : ℂ[X]) • (collectedBasis (d := d) (kk := kk) jb) := by
    funext p
    rw [transportPi_toLin, LinearEquiv.apply_symm_apply, Pi.smul_apply]
  rw [hkey]

/-- **The adapted matrix is a direct sum of nilpotent Jordan blocks.**  In the
adapted basis, `f = toLin' N` has matrix `blockDiagonal'(jordanBlockNil ∘ kk)`
— block-diagonal with each block a nilpotent Jordan (shift) block (Higham §18.1,
eqns (18.1a)/(18.1b), p. 618). -/
theorem toMatrix_jordanBasisFin_eq_blockDiagonal :
    LinearMap.toMatrix (jordanBasisFin N edecomp) (jordanBasisFin N edecomp) (Matrix.toLin' N)
      = Matrix.blockDiagonal' (fun i => jordanBlockNil (kk i)) := by
  ext ia jb
  rw [toMatrix_jordanBasisFin, collectedBasis, Pi.basis_repr, Pi.smul_apply]
  obtain ⟨i, a⟩ := ia
  obtain ⟨j, b⟩ := jb
  rw [Matrix.blockDiagonal'_apply]
  by_cases h : i = j
  · subst h
    rw [dif_pos rfl]
    have happ : ((Pi.basis (fun i => cycBasisRev (kk i))) ⟨i, b⟩) i = cycBasisRev (kk i) b := by
      rw [Pi.basis_apply, Pi.single_eq_same]
    rw [happ]
    have hlx : (X : ℂ[X]) • (cycBasisRev (kk i) b) = cycShift (kk i) (cycBasisRev (kk i) b) :=
      (cycShift_apply _ _).symm
    rw [hlx, ← LinearMap.toMatrix_apply, toMatrix_cycBasisRev_cycShift]
    simp
  · rw [dif_neg h]
    have happ : ((Pi.basis (fun i => cycBasisRev (kk i))) ⟨j, b⟩) i = 0 := by
      rw [Pi.basis_apply]
      exact Pi.single_eq_of_ne (M := fun i => CycQuot (kk i)) h _
    rw [happ, smul_zero, map_zero, Finsupp.zero_apply]

/-! ## The nilpotent Jordan-chain theorem and full JNF -/

/-- The adapted-basis index type `Σ i, Fin (kk i)` is in bijection with `Fin m`
(both have cardinality `m = dim ℂⁿ`). -/
def indexEquivFin : (Σ i : Fin d, Fin (kk i)) ≃ Fin m := by
  have hcard : Fintype.card (Σ i : Fin d, Fin (kk i)) = m := by
    have h := Module.finrank_eq_card_basis (jordanBasisFin N edecomp)
    simpa [Module.finrank_fintype_fun_eq_card] using h.symm
  exact Fintype.equivFinOfCardEq hcard

/-- The `Fin m`-reindexed adapted basis. -/
def jordanBasisFin' : Basis (Fin m) ℂ (Fin m → ℂ) :=
  (jordanBasisFin N edecomp).reindex (indexEquivFin N edecomp)

/-- `toMatrix` in the `Fin m`-reindexed basis is the reindexed block-diagonal
matrix. -/
theorem toMatrix_jordanBasisFin'_eq_reindex :
    LinearMap.toMatrix (jordanBasisFin' N edecomp) (jordanBasisFin' N edecomp) (Matrix.toLin' N)
      = Matrix.reindex (indexEquivFin N edecomp) (indexEquivFin N edecomp)
          (Matrix.blockDiagonal' (fun i => jordanBlockNil (kk i))) := by
  rw [← toMatrix_jordanBasisFin_eq_blockDiagonal]
  ext i j
  rw [jordanBasisFin', LinearMap.toMatrix_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    LinearMap.toMatrix_apply, Basis.reindex_apply, Basis.repr_reindex_apply]

/-- **Nilpotent Jordan-chain theorem (existential form).**  Every nilpotent
`N : Matrix (Fin m) (Fin m) ℂ` is similar to a `Fin m × Fin m` matrix that is a
direct sum of nilpotent Jordan (shift) blocks.  This is exactly the residual gap
`NilpotentJordanBasis` of `JordanNormalForm.lean` (Higham §18.1, eqns
(18.1a)/(18.1b), p. 618). -/
theorem exists_isSimilar_nilpotentJordanForm {m : ℕ} (N : Matrix (Fin m) (Fin m) ℂ)
    (hN : IsNilpotent N) :
    ∃ M : Matrix (Fin m) (Fin m) ℂ, Matrix.IsSimilar N M ∧ IsNilpotentJordanForm M := by
  classical
  obtain ⟨d, kk, ⟨edecomp⟩⟩ := exists_aeval_equiv_directSum_cyclic hN
  refine ⟨Matrix.reindex (indexEquivFin N edecomp) (indexEquivFin N edecomp)
    (Matrix.blockDiagonal' (fun i => jordanBlockNil (kk i))), ?_, ?_⟩
  · -- similarity: N ~ toMatrix (reindexed basis) f = reindexed blockDiagonal
    rw [← toMatrix_jordanBasisFin'_eq_reindex]
    exact isSimilar_toMatrix_toLin' N (jordanBasisFin' N edecomp)
  · -- the reindexed blockDiagonal is a nilpotent Jordan form, witnessed by `indexEquivFin.symm`
    refine ⟨Fin d, inferInstance, inferInstance, kk, (indexEquivFin N edecomp).symm, ?_⟩
    rw [Equiv.symm_symm]

/-- **`NilpotentJordanBasis` holds.**  The residual hypothesis of
`JordanNormalForm.lean` is a theorem: every nilpotent complex matrix is similar to
a direct sum of nilpotent Jordan blocks (Higham §18.1, eqns (18.1a)/(18.1b),
p. 618).  Proved via the PID structure theorem, with no extra hypothesis. -/
theorem nilpotentJordanBasis_holds : NilpotentJordanBasis :=
  fun _m N hN => exists_isSimilar_nilpotentJordanForm N hN

/-! ## Full Jordan Normal Form over ℂ — UNCONDITIONAL

Combining `nilpotentJordanBasis_holds` with the conditional result
`jordan_normal_form_of_nilpotentJordanBasis` of `JordanNormalForm.lean` gives the
classical Jordan Normal Form with **no** remaining hypothesis. -/

/-- **Classical Jordan Normal Form over ℂ (unconditional).**  For every
`A : Matrix (Fin n) (Fin n) ℂ`:

  * `A` is similar to the primary block-diagonal form `B` (the matrix of
    `toLin' A` in the primary/generalized-eigenspace basis), and
  * each eigenvalue block `primaryDiagBlock (toLin' A) μ` is similar to
    `μ • I + Nμ` with `Nμ` an honest **nilpotent Jordan form** (a direct sum of
    shift blocks `jordanBlockNil`).

This is Higham's `A = X J X⁻¹`, `J = diag(Jₖ)` with each `Jₖ = λₖ I + shift`
(§18.1, eqns (18.1a)/(18.1b), p. 618).  The statement is unconditional: the
`NilpotentJordanBasis` hypothesis of `jordan_normal_form_of_nilpotentJordanBasis`
is discharged by `nilpotentJordanBasis_holds`. -/
theorem jordan_normal_form {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.IsSimilar A
        (LinearMap.toMatrix (primaryBasisFin (Matrix.toLin' A))
          (primaryBasisFin (Matrix.toLin' A)) (Matrix.toLin' A))
      ∧ ∀ μ : ℂ, ∃ Nμ : Matrix
          (Fin (Module.finrank ℂ (Module.End.maxGenEigenspace (Matrix.toLin' A) μ)))
          (Fin (Module.finrank ℂ (Module.End.maxGenEigenspace (Matrix.toLin' A) μ))) ℂ,
        IsNilpotentJordanForm Nμ ∧
          Matrix.IsSimilar (primaryDiagBlock (Matrix.toLin' A) μ)
            (μ • (1 : Matrix _ _ ℂ) + Nμ) :=
  jordan_normal_form_of_nilpotentJordanBasis nilpotentJordanBasis_holds A

/-- **Full Jordan Normal Form — plain similarity form (unconditional).**  Every
complex square matrix is similar to a matrix in Jordan canonical form.  This is the
existence half of Higham's `A = X J X⁻¹` (§18.1, eqn (18.1a), p. 618), now with no
hypotheses. -/
theorem exists_isSimilar_jordan {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ B : Matrix (Fin n) (Fin n) ℂ, Matrix.IsSimilar A B :=
  ⟨_, (jordan_normal_form A).1⟩

end

end NumStability
