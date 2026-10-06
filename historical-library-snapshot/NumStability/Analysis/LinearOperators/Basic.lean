-- Analysis/LinearOperators/Basic.lean
--
-- Basic finite complex-linear operator infrastructure.

import NumStability.Analysis.VectorNorms.Basic

/-!
# Finite complex-linear operator infrastructure

Defines the finite complex-vector map interfaces and linear-map bridges used
by subordinate operator and matrix norms.
-/

namespace NumStability

open scoped BigOperators
open scoped ComplexOrder
open ENNReal


/-- A linear-map-shaped object from `C^n` to `C^m`.  This keeps Chapter 6's
    mixed subordinate norm infrastructure independent of a concrete matrix
    representation until the matrix API is fixed. -/
abbrev ComplexVectorMap (n m : ℕ) := CVec n → CVec m

/-- Explicit linearity predicate for source-facing maps `C^n -> C^m`. -/
structure IsComplexVectorMapLinear {n m : ℕ} (T : ComplexVectorMap n m) : Prop where
  map_add : ∀ x y : CVec n,
    T (complexVecAdd x y) = complexVecAdd (T x) (T y)
  map_smul : ∀ (a : ℂ) (x : CVec n),
    T (complexVecSMul a x) = complexVecSMul a (T x)

/-- Composition of source-facing vector maps. -/
def complexVectorMapComp {n m k : ℕ} (A : ComplexVectorMap m k)
    (B : ComplexVectorMap n m) : ComplexVectorMap n k :=
  fun x => A (B x)

/-- Pointwise addition of source-facing vector maps. -/
noncomputable def complexVectorMapAdd {n m : ℕ} (A B : ComplexVectorMap n m) :
    ComplexVectorMap n m :=
  fun x => complexVecAdd (A x) (B x)

/-- Scalar multiplication of a source-facing vector map. -/
noncomputable def complexVectorMapSMul {n m : ℕ} (a : ℂ)
    (A : ComplexVectorMap n m) : ComplexVectorMap n m :=
  fun x => complexVecSMul a (A x)

/-- Pointwise negation of a source-facing vector map. -/
noncomputable def complexVectorMapNeg {n m : ℕ} (A : ComplexVectorMap n m) :
    ComplexVectorMap n m :=
  complexVectorMapSMul (-1 : ℂ) A

/-- Pointwise subtraction of source-facing vector maps. -/
noncomputable def complexVectorMapSub {n m : ℕ} (A B : ComplexVectorMap n m) :
    ComplexVectorMap n m :=
  complexVectorMapAdd A (complexVectorMapNeg B)

/-- A source-facing square map is singular if it has a nonzero kernel vector. -/
def IsSingularComplexVectorMap {n : ℕ} (A : ComplexVectorMap n n) : Prop :=
  ∃ x : CVec n, x ≠ 0 ∧ A x = 0

lemma complexVectorMapComp_linear {n m k : ℕ} {A : ComplexVectorMap m k}
    {B : ComplexVectorMap n m} (hA : IsComplexVectorMapLinear A)
    (hB : IsComplexVectorMapLinear B) :
    IsComplexVectorMapLinear (complexVectorMapComp A B) := by
  constructor
  · intro x y
    simp [complexVectorMapComp, hB.map_add x y, hA.map_add]
  · intro a x
    simp [complexVectorMapComp, hB.map_smul a x, hA.map_smul]

lemma complexVectorMapAdd_linear {n m : ℕ} {A B : ComplexVectorMap n m}
    (hA : IsComplexVectorMapLinear A) (hB : IsComplexVectorMapLinear B) :
    IsComplexVectorMapLinear (complexVectorMapAdd A B) := by
  constructor
  · intro x y
    ext i
    simp [complexVectorMapAdd, complexVecAdd, hA.map_add, hB.map_add]
    ring
  · intro a x
    ext i
    simp [complexVectorMapAdd, complexVecAdd, complexVecSMul, hA.map_smul,
      hB.map_smul]
    ring

lemma complexVectorMapSMul_linear {n m : ℕ} {A : ComplexVectorMap n m}
    (a : ℂ) (hA : IsComplexVectorMapLinear A) :
    IsComplexVectorMapLinear (complexVectorMapSMul a A) := by
  constructor
  · intro x y
    ext i
    simp [complexVectorMapSMul, complexVecAdd, complexVecSMul, hA.map_add]
    ring
  · intro b x
    ext i
    simp [complexVectorMapSMul, complexVecSMul, hA.map_smul]
    ring

lemma complexVectorMapNeg_linear {n m : ℕ} {A : ComplexVectorMap n m}
    (hA : IsComplexVectorMapLinear A) :
    IsComplexVectorMapLinear (complexVectorMapNeg A) := by
  exact complexVectorMapSMul_linear (-1 : ℂ) hA

lemma complexVectorMapSub_linear {n m : ℕ} {A B : ComplexVectorMap n m}
    (hA : IsComplexVectorMapLinear A) (hB : IsComplexVectorMapLinear B) :
    IsComplexVectorMapLinear (complexVectorMapSub A B) := by
  exact complexVectorMapAdd_linear hA (complexVectorMapNeg_linear hB)

lemma IsComplexVectorMapLinear.map_zero {n m : ℕ} {T : ComplexVectorMap n m}
    (hT : IsComplexVectorMapLinear T) : T 0 = 0 := by
  have h := hT.map_smul (0 : ℂ) (0 : CVec n)
  have hleft : complexVecSMul (0 : ℂ) (0 : CVec n) = 0 := by
    ext i
    simp [complexVecSMul]
  have hright : complexVecSMul (0 : ℂ) (T 0) = 0 := by
    ext i
    simp [complexVecSMul]
  rw [hleft, hright] at h
  exact h

/-- Mathlib linear-map wrapper for a source-facing complex vector map. -/
noncomputable def complexVectorMapLinearMap {n m : ℕ}
    (T : ComplexVectorMap n m) (hT : IsComplexVectorMapLinear T) :
    CVec n →ₗ[ℂ] CVec m where
  toFun := T
  map_add' := by
    intro x y
    simpa [complexVecAdd] using hT.map_add x y
  map_smul' := by
    intro a x
    simpa [complexVecSMul] using hT.map_smul a x

-- Keep lazily generated theorems in their frozen semantic owner.
run_meta do
  for declName in #[
      ``NumStability.complexVectorMapNeg,
      ``NumStability.complexVectorMapSub] do
    discard <| Lean.Meta.getEqnsFor? declName
  discard <| Lean.Meta.mkCongrSimpForConst?
    ``NumStability.complexVectorMapLinearMap []

@[simp]
theorem complexVectorMapLinearMap_apply {n m : ℕ}
    (T : ComplexVectorMap n m) (hT : IsComplexVectorMapLinear T)
    (x : CVec n) :
    complexVectorMapLinearMap T hT x = T x := rfl

theorem complexVectorNorm_pullback_of_linear_injective
    {n : ℕ} {μ : CVec n → ℝ} {S : ComplexVectorMap n n}
    (hμ : IsComplexVectorNorm μ) (hS : IsComplexVectorMapLinear S)
    (hinj_zero : ∀ x : CVec n, S x = 0 → x = 0) :
    IsComplexVectorNorm (fun x : CVec n => μ (S x)) := by
  constructor
  · intro x
    exact hμ.nonneg (S x)
  · intro x
    constructor
    · intro hx
      exact hinj_zero x ((hμ.eq_zero_iff (S x)).mp hx)
    · intro hx
      subst hx
      have hS0 : S 0 = 0 := hS.map_zero
      rw [hS0]
      exact (hμ.eq_zero_iff 0).mpr rfl
  · intro a x
    rw [hS.map_smul, hμ.smul]
  · intro x y
    rw [hS.map_add]
    exact hμ.add_le (S x) (S y)
end NumStability
