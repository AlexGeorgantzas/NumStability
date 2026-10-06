/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Analysis.MatrixAlgebra

namespace NumStability

/-! # Higham Chapter 26: Multidirectional-Search Simplexes

The simplex representation, ordering operation, and reflection, expansion, and contraction transformations used in Section 26.2.
-/

/-! ### Multidirectional-search iteration (Section 26.2) -/

/-- An `n`-dimensional MDS simplex is stored as its distinguished vertex
`v₀` together with the other `n` vertices.  The source reorders these `n+1`
vertices after a successful trial so that `v₀` has maximal objective value. -/
structure MDSSimplex (n : ℕ) where
  base : RVec n
  other : Fin n → RVec n

namespace MDSSimplex

/-- All `n+1` vertices, with source vertex zero represented by `base`. -/
def point {n : ℕ} (s : MDSSimplex n) : Fin (n + 1) → RVec n :=
  Fin.cases s.base s.other

@[simp] theorem point_zero {n : ℕ} (s : MDSSimplex n) :
    s.point 0 = s.base := rfl

@[simp] theorem point_succ {n : ℕ} (s : MDSSimplex n) (i : Fin n) :
    s.point i.succ = s.other i := rfl

/-- The source ordering invariant `f(v₀) = maxᵢ f(vᵢ)`. -/
def OrderedFor {n : ℕ} (s : MDSSimplex n) (f : RVec n → ℝ) : Prop :=
  ∀ i, f (s.other i) ≤ f s.base

/-- A maximizing vertex of the finite family.  This is a deterministic
mathematical choice, not a hypothesis that the search finds a global maximizer
of the objective on `ℝⁿ`. -/
noncomputable def bestIndex {n : ℕ} (f : RVec n → ℝ)
    (s : MDSSimplex n) : Fin (n + 1) :=
  Classical.choose (Finite.exists_max (fun i : Fin (n + 1) => f (s.point i)))

theorem le_bestIndex {n : ℕ} (f : RVec n → ℝ)
    (s : MDSSimplex n) (i : Fin (n + 1)) :
    f (s.point i) ≤ f (s.point (bestIndex f s)) :=
  Classical.choose_spec
    (Finite.exists_max (fun i : Fin (n + 1) => f (s.point i))) i

/-- The maximum objective value among the `n+1` simplex vertices. -/
noncomputable def bestValue {n : ℕ} (f : RVec n → ℝ)
    (s : MDSSimplex n) : ℝ :=
  f (s.point (bestIndex f s))

theorem point_le_bestValue {n : ℕ} (f : RVec n → ℝ)
    (s : MDSSimplex n) (i : Fin (n + 1)) :
    f (s.point i) ≤ bestValue f s := by
  exact le_bestIndex f s i

/-- Reorder a simplex by swapping a maximizing vertex into position zero.
The remaining vertices are permuted by the same swap, so no vertex is added or
discarded. -/
noncomputable def reorderBest {n : ℕ} (f : RVec n → ℝ)
    (s : MDSSimplex n) : MDSSimplex n where
  base := s.point (bestIndex f s)
  other := fun i =>
    s.point ((Equiv.swap (0 : Fin (n + 1)) (bestIndex f s)) i.succ)

theorem reorderBest_orderedFor {n : ℕ} (f : RVec n → ℝ)
    (s : MDSSimplex n) : (reorderBest f s).OrderedFor f := by
  intro i
  exact le_bestIndex f s
    ((Equiv.swap (0 : Fin (n + 1)) (bestIndex f s)) i.succ)

/-- Reflection of every non-base vertex through `v₀`:
`rᵢ = v₀ + (v₀-vᵢ) = 2v₀-vᵢ`. -/
def reflect {n : ℕ} (s : MDSSimplex n) : MDSSimplex n where
  base := s.base
  other := fun i j => s.base j + (s.base j - s.other i j)

/-- Expansion doubles each reflected edge from `v₀`:
`eᵢ = v₀ + 2(v₀-vᵢ)`. -/
def expand {n : ℕ} (s : MDSSimplex n) : MDSSimplex n where
  base := s.base
  other := fun i j => s.base j + 2 * (s.base j - s.other i j)

/-- Contraction halves every edge incident on `v₀`:
`cᵢ = v₀ + (vᵢ-v₀)/2`. -/
noncomputable def contract {n : ℕ} (s : MDSSimplex n) : MDSSimplex n where
  base := s.base
  other := fun i j => s.base j + (s.other i j - s.base j) / 2

@[simp] theorem reflect_base {n : ℕ} (s : MDSSimplex n) :
    s.reflect.base = s.base := rfl

@[simp] theorem reflect_other {n : ℕ} (s : MDSSimplex n)
    (i : Fin n) (j : Fin n) :
    s.reflect.other i j = s.base j + (s.base j - s.other i j) := rfl

@[simp] theorem expand_base {n : ℕ} (s : MDSSimplex n) :
    s.expand.base = s.base := rfl

@[simp] theorem expand_other {n : ℕ} (s : MDSSimplex n)
    (i : Fin n) (j : Fin n) :
    s.expand.other i j = s.base j + 2 * (s.base j - s.other i j) := rfl

@[simp] theorem contract_base {n : ℕ} (s : MDSSimplex n) :
    s.contract.base = s.base := rfl

@[simp] theorem contract_other {n : ℕ} (s : MDSSimplex n)
    (i : Fin n) (j : Fin n) :
    s.contract.other i j = s.base j + (s.other i j - s.base j) / 2 := rfl


end MDSSimplex


end NumStability
