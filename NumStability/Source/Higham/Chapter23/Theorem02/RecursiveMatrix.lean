/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.NoncommRing
import NumStability.Source.Higham.Chapter23.BlockAlgorithms

namespace NumStability

/-!
# Higham Chapter 23, Theorem 23.2: recursive matrix model

This module supplies the recursive block-matrix carrier, algebraic instances,
and projection lemmas used by the literal recursive Strassen analysis for
Theorem 23.2. Declaration names and bodies are preserved from the historical
Chapter 23 implementation.
-/

instance {R : Type*} [Zero R] : Zero (Higham23Block2 (R := R)) :=
  ⟨⟨0, 0, 0, 0⟩⟩

instance {R : Type*} [Add R] : Add (Higham23Block2 (R := R)) :=
  ⟨fun A B ↦ ⟨A.c11 + B.c11, A.c12 + B.c12,
    A.c21 + B.c21, A.c22 + B.c22⟩⟩

instance {R : Type*} [Neg R] : Neg (Higham23Block2 (R := R)) :=
  ⟨fun A ↦ ⟨-A.c11, -A.c12, -A.c21, -A.c22⟩⟩

instance {R : Type*} [Sub R] : Sub (Higham23Block2 (R := R)) :=
  ⟨fun A B ↦ ⟨A.c11 - B.c11, A.c12 - B.c12,
    A.c21 - B.c21, A.c22 - B.c22⟩⟩

instance {S R : Type*} [SMul S R] : SMul S (Higham23Block2 (R := R)) :=
  ⟨fun s A ↦ ⟨s • A.c11, s • A.c12, s • A.c21, s • A.c22⟩⟩

@[simp] theorem higham23Block2_zero_c11 {R : Type*} [Zero R] :
    (0 : Higham23Block2 (R := R)).c11 = 0 := rfl
@[simp] theorem higham23Block2_zero_c12 {R : Type*} [Zero R] :
    (0 : Higham23Block2 (R := R)).c12 = 0 := rfl
@[simp] theorem higham23Block2_zero_c21 {R : Type*} [Zero R] :
    (0 : Higham23Block2 (R := R)).c21 = 0 := rfl
@[simp] theorem higham23Block2_zero_c22 {R : Type*} [Zero R] :
    (0 : Higham23Block2 (R := R)).c22 = 0 := rfl

@[simp] theorem higham23Block2_add_c11 {R : Type*} [Add R]
    (A B : Higham23Block2 (R := R)) : (A + B).c11 = A.c11 + B.c11 := rfl
@[simp] theorem higham23Block2_add_c12 {R : Type*} [Add R]
    (A B : Higham23Block2 (R := R)) : (A + B).c12 = A.c12 + B.c12 := rfl
@[simp] theorem higham23Block2_add_c21 {R : Type*} [Add R]
    (A B : Higham23Block2 (R := R)) : (A + B).c21 = A.c21 + B.c21 := rfl
@[simp] theorem higham23Block2_add_c22 {R : Type*} [Add R]
    (A B : Higham23Block2 (R := R)) : (A + B).c22 = A.c22 + B.c22 := rfl

private def higham23Block2EquivProd {R : Type*} :
    Higham23Block2 (R := R) ≃ R × R × R × R where
  toFun A := (A.c11, A.c12, A.c21, A.c22)
  invFun q := ⟨q.1, q.2.1, q.2.2.1, q.2.2.2⟩
  left_inv A := by cases A; rfl
  right_inv q := by rcases q with ⟨a, b, c, d⟩; rfl

instance {R : Type*} [AddCommGroup R] :
    AddCommGroup (Higham23Block2 (R := R)) := by
  apply higham23Block2EquivProd.injective.addCommGroup <;> intros <;> rfl

/-- Block multiplication equips `Higham23Block2 R` with the same distributive
nonassociative ring structure as its block entries. -/
instance higham23Block2NonUnitalNonAssocRing
    {R : Type*} [NonUnitalNonAssocRing R] :
    NonUnitalNonAssocRing (Higham23Block2 (R := R)) where
  mul := higham23BlockMul
  left_distrib := by
    intro A B C
    change higham23BlockMul A (B + C) =
      higham23BlockMul A B + higham23BlockMul A C
    cases A
    cases B
    cases C
    ext <;> dsimp [higham23BlockMul] <;> noncomm_ring
  right_distrib := by
    intro A B C
    change higham23BlockMul (A + B) C =
      higham23BlockMul A C + higham23BlockMul B C
    cases A
    cases B
    cases C
    ext <;> dsimp [higham23BlockMul] <;> noncomm_ring
  zero_mul := by
    intro A
    change higham23BlockMul 0 A = 0
    cases A
    ext <;> dsimp [higham23BlockMul] <;> simp
  mul_zero := by
    intro A
    change higham23BlockMul A 0 = 0
    cases A
    ext <;> dsimp [higham23BlockMul] <;> simp

@[simp] theorem higham23Block2_mul_c11 {R : Type*}
    [NonUnitalNonAssocRing R] (A B : Higham23Block2 (R := R)) :
    (A * B).c11 = A.c11 * B.c11 + A.c12 * B.c21 := rfl
@[simp] theorem higham23Block2_mul_c12 {R : Type*}
    [NonUnitalNonAssocRing R] (A B : Higham23Block2 (R := R)) :
    (A * B).c12 = A.c11 * B.c12 + A.c12 * B.c22 := rfl
@[simp] theorem higham23Block2_mul_c21 {R : Type*}
    [NonUnitalNonAssocRing R] (A B : Higham23Block2 (R := R)) :
    (A * B).c21 = A.c21 * B.c11 + A.c22 * B.c21 := rfl
@[simp] theorem higham23Block2_mul_c22 {R : Type*}
    [NonUnitalNonAssocRing R] (A B : Higham23Block2 (R := R)) :
    (A * B).c22 = A.c21 * B.c12 + A.c22 * B.c22 := rfl

@[simp] theorem higham23Block2_sub_c11 {R : Type*} [Sub R]
    (A B : Higham23Block2 (R := R)) : (A - B).c11 = A.c11 - B.c11 := rfl
@[simp] theorem higham23Block2_sub_c12 {R : Type*} [Sub R]
    (A B : Higham23Block2 (R := R)) : (A - B).c12 = A.c12 - B.c12 := rfl
@[simp] theorem higham23Block2_sub_c21 {R : Type*} [Sub R]
    (A B : Higham23Block2 (R := R)) : (A - B).c21 = A.c21 - B.c21 := rfl
@[simp] theorem higham23Block2_sub_c22 {R : Type*} [Sub R]
    (A B : Higham23Block2 (R := R)) : (A - B).c22 = A.c22 - B.c22 := rfl

/-- Recursive block presentation of a matrix of order `2^(r+depth)`. -/
def Higham23RecursiveMatrix (r : ℕ) : ℕ → Type
  | 0 => Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ
  | depth + 1 => Higham23Block2 (R := Higham23RecursiveMatrix r depth)

instance (r depth : ℕ) : NonUnitalNonAssocRing
    (Higham23RecursiveMatrix r depth) := by
  induction depth with
  | zero =>
      dsimp [Higham23RecursiveMatrix]
      infer_instance
  | succ depth ih =>
      dsimp [Higham23RecursiveMatrix]
      infer_instance

end NumStability
