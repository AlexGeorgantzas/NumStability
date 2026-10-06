import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Ring
import NumStability.Analysis.MatrixAlgebra

/-!
# Rectangular rank-factorization infrastructure

Exact finite-dimensional rank factorizations and orthonormal-completion
constructions used by the rectangular singular-value analysis.
-/

namespace NumStability

open scoped BigOperators

/-- An exact rectangular rank factorization certificate `A = X Y` through an
inner dimension `r`. -/
structure RectRankFactorization (m n r : ℕ) (A : Fin m → Fin n → ℝ) where
  left : Fin m → Fin r → ℝ
  right : Fin r → Fin n → ℝ
  factorization : ∀ i j, A i j = ∑ a : Fin r, left i a * right a j

/-- Canonical order-preserving cast from `Fin n` to mathlib's zero-indexed
Hermitian-eigenvalue domain for matrices indexed by `Fin n`. -/
def finCardIndex (n : ℕ) (j : Fin n) : Fin (Fintype.card (Fin n)) :=
  Fin.cast (by simp) j

/-- Concatenate exact left-head and left-tail bases as a single sum-indexed
left-basis block. -/
noncomputable def leftBasisBlock {m r q : ℕ}
    (U : Fin m → Fin r → ℝ) (Utail : Fin m → Fin q → ℝ) :
    Fin m → (Fin r ⊕ Fin q) → ℝ :=
  fun i bc =>
    match bc with
    | Sum.inl a => U i a
    | Sum.inr c => Utail i c

/-- Column orthonormality of the concatenated left-basis block `[U,Utail]`
implies head orthonormality, head-tail cross orthogonality, and tail
orthonormality. -/
theorem leftBasisBlock_component_orthonormal_fields_of_col_orthonormal
    {m r q : ℕ}
    (U : Fin m → Fin r → ℝ) (Utail : Fin m → Fin q → ℝ)
    (hcols :
      ∀ bc bd : Fin r ⊕ Fin q,
        (∑ i : Fin m,
          leftBasisBlock U Utail i bc * leftBasisBlock U Utail i bd) =
          if bc = bd then 1 else 0) :
    (∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b) ∧
      (∀ a c, ∑ i : Fin m, U i a * Utail i c = 0) ∧
      (∀ a c, ∑ i : Fin m, Utail i a * Utail i c = idMatrix q a c) := by
  constructor
  · intro a b
    have h := hcols (Sum.inl a) (Sum.inl b)
    simpa [leftBasisBlock, idMatrix] using h
  constructor
  · intro a c
    have h := hcols (Sum.inl a) (Sum.inr c)
    simpa [leftBasisBlock] using h
  · intro a c
    have h := hcols (Sum.inr a) (Sum.inr c)
    simpa [leftBasisBlock, idMatrix] using h

/-- A partially specified family of raw column-orthonormal columns in `ℝ^m`
can be extended to a full `m × m` column-orthonormal table while preserving the
specified columns.

This is a finite-dimensional orthonormal-completion bridge for exact matrices.
-/
theorem partialColOrthonormal_exists_fullColOrthonormal {m : ℕ}
    (X : Fin m → Fin m → ℝ) (s : Set (Fin m))
    (hX : ∀ a b : s,
      (∑ i : Fin m, X i a * X i b) = if a = b then 1 else 0) :
    ∃ Y : Fin m → Fin m → ℝ,
      (∀ a : Fin m, a ∈ s → ∀ i : Fin m, Y i a = X i a) ∧
        ∀ a b : Fin m,
          (∑ i : Fin m, Y i a * Y i b) = if a = b then 1 else 0 := by
  classical
  let v : Fin m → EuclideanSpace ℝ (Fin m) :=
    fun a => WithLp.toLp 2 (fun i : Fin m => X i a)
  have hv : Orthonormal ℝ (s.restrict v) := by
    rw [orthonormal_iff_ite]
    intro a b
    have h := hX a b
    unfold v
    rw [PiLp.inner_apply]
    simpa [Set.restrict, real_inner_eq_re_inner, RCLike.inner_apply, mul_comm] using h
  have hcard :
      Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = Fintype.card (Fin m) := by
    simp
  obtain ⟨b, hb⟩ :=
    hv.exists_orthonormalBasis_extension_of_card_eq
      (v := v) (s := s) hcard
  refine ⟨fun i a => b a i, ?_, ?_⟩
  · intro a ha i
    have h := hb a ha
    change b a i = X i a
    simpa [v] using congrArg (fun z : EuclideanSpace ℝ (Fin m) => z i) h
  · intro a c
    have h := b.inner_eq_ite a c
    rw [PiLp.inner_apply] at h
    simpa [real_inner_eq_re_inner, RCLike.inner_apply, mul_comm] using h

/-- Embedded block-column version of
`partialColOrthonormal_exists_fullColOrthonormal`.

If the head columns and any chosen tail columns of `[U,Utail₀]` are already a
partial orthonormal family, and the block indices embed into a full `Fin m`
coordinate set, then the unspecified tail columns can be replaced so that the
whole block `[U,Utail]` is column-orthonormal.  The replacement preserves every
tail column included in the partial set.

This is exact nullspace-completion infrastructure. -/
theorem partialLeftBasisBlock_exists_replacement_tail
    {m r q : ℕ}
    (e : Fin r ⊕ Fin q ↪ Fin m)
    (U : Fin m → Fin r → ℝ) (Utail₀ : Fin m → Fin q → ℝ)
    (s : Set (Fin r ⊕ Fin q))
    (hhead : ∀ a : Fin r, Sum.inl a ∈ s)
    (hpartial : ∀ a b : s,
      (∑ i : Fin m,
        leftBasisBlock U Utail₀ i a * leftBasisBlock U Utail₀ i b) =
        if a = b then 1 else 0) :
    ∃ Utail : Fin m → Fin q → ℝ,
      (∀ c : Fin q, Sum.inr c ∈ s → ∀ i : Fin m, Utail i c = Utail₀ i c) ∧
        ∀ bc bd : Fin r ⊕ Fin q,
          (∑ i : Fin m,
            leftBasisBlock U Utail i bc * leftBasisBlock U Utail i bd) =
            if bc = bd then 1 else 0 := by
  classical
  let blockCol : Fin r ⊕ Fin q → Fin m → ℝ :=
    fun bc i => leftBasisBlock U Utail₀ i bc
  let X : Fin m → Fin m → ℝ :=
    fun i a =>
      if ha : a ∈ Set.range (fun bc : Fin r ⊕ Fin q => e bc) then
        blockCol (Classical.choose ha) i
      else
        0
  let sFull : Set (Fin m) :=
    Set.image (fun bc : Fin r ⊕ Fin q => e bc) s
  have hX : ∀ a b : sFull,
      (∑ i : Fin m, X i a * X i b) = if a = b then 1 else 0 := by
    intro a b
    rcases a.2 with ⟨bc, hbc, hbc_eq⟩
    rcases b.2 with ⟨bd, hbd, hbd_eq⟩
    have hmem_a : (a : Fin m) ∈ Set.range (fun x : Fin r ⊕ Fin q => e x) :=
      ⟨bc, hbc_eq⟩
    have hmem_b : (b : Fin m) ∈ Set.range (fun x : Fin r ⊕ Fin q => e x) :=
      ⟨bd, hbd_eq⟩
    have hchoose_a : Classical.choose hmem_a = bc :=
      e.injective (by
        calc
          e (Classical.choose hmem_a) = (a : Fin m) :=
            Classical.choose_spec hmem_a
          _ = e bc := hbc_eq.symm)
    have hchoose_b : Classical.choose hmem_b = bd :=
      e.injective (by
        calc
          e (Classical.choose hmem_b) = (b : Fin m) :=
            Classical.choose_spec hmem_b
          _ = e bd := hbd_eq.symm)
    have h := hpartial ⟨bc, hbc⟩ ⟨bd, hbd⟩
    have hsum :
        (∑ i : Fin m, X i a * X i b) =
          ∑ i : Fin m,
            leftBasisBlock U Utail₀ i bc * leftBasisBlock U Utail₀ i bd := by
      apply Finset.sum_congr rfl
      intro i _
      have hXa : X i a = leftBasisBlock U Utail₀ i bc := by
        dsimp [X, blockCol]
        rw [dif_pos hmem_a]
        simp [hchoose_a]
      have hXb : X i b = leftBasisBlock U Utail₀ i bd := by
        dsimp [X, blockCol]
        rw [dif_pos hmem_b]
        simp [hchoose_b]
      rw [hXa, hXb]
    have hite_s :
        (if (⟨bc, hbc⟩ : s) = (⟨bd, hbd⟩ : s) then (1 : ℝ) else 0) =
          if bc = bd then 1 else 0 := by
      by_cases hbdc : bc = bd
      · subst hbdc
        simp
      · have hne : (⟨bc, hbc⟩ : s) ≠ (⟨bd, hbd⟩ : s) := by
          intro hEq
          exact hbdc (Subtype.ext_iff.mp hEq)
        simp [hbdc, hne]
    have hite_full : (if a = b then (1 : ℝ) else 0) =
        if bc = bd then 1 else 0 := by
      by_cases hbdc : bc = bd
      · subst hbdc
        have hab : a = b := by
          apply Subtype.ext
          calc
            (a : Fin m) = e bc := hbc_eq.symm
            _ = (b : Fin m) := hbd_eq
        simp [hab]
      · have hne :
          a ≠ b := by
          intro hEq
          apply hbdc
          apply e.injective
          calc
            e bc = (a : Fin m) := hbc_eq
            _ = (b : Fin m) := congrArg Subtype.val hEq
            _ = e bd := hbd_eq.symm
        simp [hbdc, hne]
    calc
      (∑ i : Fin m, X i a * X i b)
          = ∑ i : Fin m,
              leftBasisBlock U Utail₀ i bc * leftBasisBlock U Utail₀ i bd := hsum
      _ = if (⟨bc, hbc⟩ : s) = (⟨bd, hbd⟩ : s) then 1 else 0 := h
      _ = if bc = bd then 1 else 0 := hite_s
      _ = if a = b then 1 else 0 := hite_full.symm
  obtain ⟨Y, hYspec, hYcols⟩ :=
    partialColOrthonormal_exists_fullColOrthonormal X sFull hX
  refine ⟨fun i c => Y i (e (Sum.inr c)), ?_, ?_⟩
  · intro c hc i
    have hmem : e (Sum.inr c) ∈ sFull := ⟨Sum.inr c, hc, rfl⟩
    have hrange : e (Sum.inr c) ∈ Set.range (fun x : Fin r ⊕ Fin q => e x) :=
      ⟨Sum.inr c, rfl⟩
    have hchoose : Classical.choose hrange = Sum.inr c :=
      e.injective (Classical.choose_spec hrange)
    simpa [X, blockCol, leftBasisBlock, hrange, hchoose] using
      hYspec (e (Sum.inr c)) hmem i
  · intro bc bd
    have hrewrite_left :
        (fun i : Fin m => leftBasisBlock U (fun i c => Y i (e (Sum.inr c))) i bc) =
          fun i : Fin m => Y i (e bc) := by
      funext i
      cases bc with
      | inl a =>
          have hmem : e (Sum.inl a) ∈ sFull := ⟨Sum.inl a, hhead a, rfl⟩
          have hrange : e (Sum.inl a) ∈ Set.range (fun x : Fin r ⊕ Fin q => e x) :=
            ⟨Sum.inl a, rfl⟩
          have hchoose : Classical.choose hrange = Sum.inl a :=
            e.injective (Classical.choose_spec hrange)
          have h := hYspec (e (Sum.inl a)) hmem i
          simpa [X, blockCol, leftBasisBlock, hrange, hchoose] using h.symm
      | inr _ =>
          rfl
    have hrewrite_right :
        (fun i : Fin m => leftBasisBlock U (fun i c => Y i (e (Sum.inr c))) i bd) =
          fun i : Fin m => Y i (e bd) := by
      funext i
      cases bd with
      | inl a =>
          have hmem : e (Sum.inl a) ∈ sFull := ⟨Sum.inl a, hhead a, rfl⟩
          have hrange : e (Sum.inl a) ∈ Set.range (fun x : Fin r ⊕ Fin q => e x) :=
            ⟨Sum.inl a, rfl⟩
          have hchoose : Classical.choose hrange = Sum.inl a :=
            e.injective (Classical.choose_spec hrange)
          have h := hYspec (e (Sum.inl a)) hmem i
          simpa [X, blockCol, leftBasisBlock, hrange, hchoose] using h.symm
      | inr _ =>
          rfl
    have hcols := hYcols (e bc) (e bd)
    have hite : (if e bc = e bd then (1 : ℝ) else 0) =
        if bc = bd then 1 else 0 := by
      by_cases hbc : bc = bd
      · subst hbc
        simp
      · have hne : e bc ≠ e bd := fun h => hbc (e.injective h)
        simp [hbc, hne]
    calc
      (∑ i : Fin m,
        leftBasisBlock U (fun i c => Y i (e (Sum.inr c))) i bc *
          leftBasisBlock U (fun i c => Y i (e (Sum.inr c))) i bd)
          = ∑ i : Fin m, Y i (e bc) * Y i (e bd) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [congr_fun hrewrite_left i, congr_fun hrewrite_right i]
      _ = if e bc = e bd then 1 else 0 := hcols
      _ = if bc = bd then 1 else 0 := hite

end NumStability
