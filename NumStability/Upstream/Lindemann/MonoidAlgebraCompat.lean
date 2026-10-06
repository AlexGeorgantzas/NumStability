/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: Johannes Hölzl, Yury Kudryashov, Kim Morrison
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.TransferInstance
public import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Compatibility surface for the Lindemann–Weierstrass development

The pinned Mathlib commit predates the explicit `coeff`/`ofCoeff` API and the
automorphism homomorphisms used by mathlib4 PR #28013.  This file backports only
that API from these exact upstream sources:

* mathlib4 PR #36762, https://github.com/leanprover-community/mathlib4/pull/36762,
  commit `cbdf82d6b083de3a961936dbea002185060b46c3`;
* mathlib4 PR #37797, https://github.com/leanprover-community/mathlib4/pull/37797,
  commit `d8255d64167683fc82500473c77d08285b6804ed`.

The target Lindemann development is mathlib4 PR #28013,
https://github.com/leanprover-community/mathlib4/pull/28013, at commit
`5abb7c68488b527e4d7ecf5d7bbe085db8d2a388`.  Every compatibility definition
is reducible to the older `Finsupp`-based implementation already present in the
pinned library.
-/

@[expose] public section

noncomputable section

open Finsupp Function

variable {R S T M N ι : Type*}

namespace MonoidAlgebra

section Coeff

variable [Semiring R] {x y : MonoidAlgebra R M}

/-- Construct a monoid-algebra element from its coefficient `Finsupp`. -/
@[to_additive
/-- Construct an additive-monoid-algebra element from its coefficient `Finsupp`. -/]
def ofCoeff (x : M →₀ R) : MonoidAlgebra R M := x

/-- Extract the coefficient `Finsupp` of a monoid-algebra element. -/
@[to_additive
/-- Extract the coefficient `Finsupp` of an additive-monoid-algebra element. -/]
def coeff (x : MonoidAlgebra R M) : M →₀ R := x

@[to_additive (attr := simp)]
theorem coeff_ofCoeff (x : M →₀ R) : coeff (ofCoeff x) = x := rfl

@[to_additive (attr := simp)]
theorem ofCoeff_coeff (x : MonoidAlgebra R M) : ofCoeff x.coeff = x := rfl

/-- Coefficients as an equivalence. -/
@[to_additive (attr := simps apply symm_apply)
/-- Additive-monoid-algebra coefficients as an equivalence. -/]
def coeffEquiv : MonoidAlgebra R M ≃ (M →₀ R) where
  toFun := coeff
  invFun := ofCoeff
  left_inv _ := rfl
  right_inv _ := rfl

@[to_additive]
theorem coeff_injective : (coeff : MonoidAlgebra R M → M →₀ R).Injective :=
  coeffEquiv.injective

@[to_additive]
theorem ofCoeff_injective : (ofCoeff : (M →₀ R) → MonoidAlgebra R M).Injective :=
  coeffEquiv.symm.injective

@[to_additive]
theorem coeff_inj : x.coeff = y.coeff ↔ x = y := coeff_injective.eq_iff

@[to_additive]
theorem ofCoeff_inj {x y : M →₀ R} : ofCoeff x = ofCoeff y ↔ x = y :=
  ofCoeff_injective.eq_iff

/-- Coefficients as an additive equivalence. -/
@[to_additive (attr := simps! apply symm_apply)
/-- Additive-monoid-algebra coefficients as an additive equivalence. -/]
def coeffAddEquiv : MonoidAlgebra R M ≃+ (M →₀ R) := coeffEquiv.addEquiv

@[to_additive (attr := simp)] theorem coeff_zero : coeff (0 : MonoidAlgebra R M) = 0 := rfl
@[to_additive (attr := simp)] theorem ofCoeff_zero : (ofCoeff 0 : MonoidAlgebra R M) = 0 := rfl
@[to_additive (attr := simp)] theorem coeff_eq_zero : coeff x = 0 ↔ x = 0 := coeff_inj
@[to_additive (attr := simp)] theorem ofCoeff_eq_zero {x : M →₀ R} : ofCoeff x = 0 ↔ x = 0 :=
  ofCoeff_inj

@[to_additive (attr := simp)]
theorem coeff_add (x y : MonoidAlgebra R M) : coeff (x + y) = coeff x + coeff y := rfl

@[to_additive (attr := simp)]
theorem ofCoeff_add (x y : M →₀ R) : ofCoeff (x + y) = ofCoeff x + ofCoeff y := rfl

@[to_additive (attr := simp)]
theorem coeff_sum (s : Finset ι) (f : ι → MonoidAlgebra R M) :
    coeff (∑ i ∈ s, f i) = ∑ i ∈ s, coeff (f i) := map_sum coeffAddEquiv ..

@[to_additive (attr := simp)]
theorem ofCoeff_sum (s : Finset ι) (f : ι → M →₀ R) :
    ofCoeff (∑ i ∈ s, f i) = ∑ i ∈ s, ofCoeff (f i) := map_sum coeffAddEquiv.symm ..

variable {A : Type*} [SMulZeroClass A R]

@[to_additive (dont_translate := A) (attr := simp)]
theorem coeff_smul (a : A) (x : MonoidAlgebra R M) : coeff (a • x) = a • coeff x := rfl

@[to_additive (dont_translate := A) (attr := simp)]
theorem ofCoeff_smul (a : A) (x : M →₀ R) : ofCoeff (a • x) = a • ofCoeff x := rfl

end Coeff

section Map

variable [Semiring R] [Semiring S]

/-- Map every coefficient through an additive homomorphism. -/
@[to_additive (attr := simps!)
/-- Map every coefficient through an additive homomorphism. -/]
def map (f : R →+ S) (x : MonoidAlgebra R M) : MonoidAlgebra S M :=
  .ofCoeff <| x.coeff.mapRange f f.map_zero

@[to_additive (attr := simp)]
theorem coeff_map (f : R →+ S) (x : MonoidAlgebra R M) :
    (map f x).coeff = x.coeff.mapRange f f.map_zero := rfl

@[to_additive]
theorem ofCoeff_mapRange (f : R →+ S) (x : M →₀ R) :
    ofCoeff (.mapRange f f.map_zero x) = map f (ofCoeff x) := rfl

@[to_additive]
theorem ofCoeff_mapDomain (f : M → N) (x : M →₀ R) :
    ofCoeff (.mapDomain f x) = Finsupp.mapDomain f (ofCoeff x) := rfl

@[to_additive]
theorem range_map (f : R →+ S) :
    Set.range (map (M := M) f) = {x | ∀ i, x.coeff i ∈ Set.range f} :=
  calc
    _ = coeffEquiv ⁻¹' (Set.range (Finsupp.mapRange f (map_zero f) ∘ coeffEquiv)) := by
      simp_rw [Function.comp_def, Equiv.eq_preimage_iff_image_eq, ← Set.range_comp',
        coeffEquiv_apply, coeff_map]
    _ = _ := by simp [Finsupp.range_mapRange]

@[to_additive]
theorem map_injective (f : R →+ S) (he : Injective f) : Injective (map (M := M) f) := by
  have hmap : map (M := M) f =
      coeffEquiv.symm ∘ Finsupp.mapRange f (map_zero f) ∘ coeffEquiv := by
    ext
    simp [ofCoeff_mapRange]
  simpa [hmap] using Finsupp.mapRange_injective _ (map_zero f) he

/-- Ring-hom form of coefficient mapping. -/
@[to_additive (dont_translate := R S)
/-- Ring-hom form of additive-monoid-algebra coefficient mapping. -/]
noncomputable def mapRingHom (M : Type*) [Monoid M] (f : R →+* S) :
    MonoidAlgebra R M →+* MonoidAlgebra S M :=
  MonoidAlgebra.mapRangeRingHom M f

@[to_additive (dont_translate := R S)]
theorem coe_mapRingHom (M : Type*) [Monoid M] (f : R →+* S) :
    ⇑(mapRingHom M f) = map (M := M) f := by
  funext x
  rfl

end Map

end MonoidAlgebra

namespace AddMonoidAlgebra

variable {A : Type*}

section Automorphisms

variable [CommSemiring R] [AddMonoid M] [Semiring A] [Algebra R A]

variable (R A) in
/-- `domCongr` assembled as a monoid homomorphism on additive automorphisms. -/
@[simps]
def domCongrAut : AddAut M →* AddMonoidAlgebra A M ≃ₐ[R] AddMonoidAlgebra A M where
  toFun := AddMonoidAlgebra.domCongr R A
  map_one' := by ext; simp [AddAut.one_def]
  map_mul' _ _ := by ext; simp [AddAut.mul_def]

variable (R M) in
/-- Coefficient automorphisms assembled as a monoid homomorphism. -/
@[simps]
def mapAlgAut : (A ≃ₐ[R] A) →* AddMonoidAlgebra A M ≃ₐ[R] AddMonoidAlgebra A M where
  toFun f := mapRangeAlgEquiv R M f
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mapRangeAlgEquiv_trans]

end Automorphisms

section LiftAlias

variable [CommSemiring R] [AddMonoid M] [Semiring A] [Algebra R A]
  [CommSemiring S] [Algebra S A] [Algebra R S] [IsScalarTower R S A]

theorem lift_mapRingHom_algebraMap (f : Multiplicative M →* A)
    (x : AddMonoidAlgebra R M) :
    AddMonoidAlgebra.lift S A M f (AddMonoidAlgebra.mapRingHom M (algebraMap R S) x) =
      AddMonoidAlgebra.lift R A M f x :=
  AddMonoidAlgebra.lift_mapRangeRingHom_algebraMap f x

end LiftAlias

end AddMonoidAlgebra

/- Renaming aliases added immediately after the pinned Mathlib revision. -/
namespace Finsupp

alias finsetSum_apply := finset_sum_apply
alias coe_finsetSum := coe_finset_sum

end Finsupp

namespace AddSubmonoidClass

alias coe_finsetSum := coe_finset_sum

end AddSubmonoidClass
