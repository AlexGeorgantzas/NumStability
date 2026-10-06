/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter23.Theorem02.RecursiveMatrix

namespace NumStability

open scoped BigOperators

/-!
# Higham Chapter 23, Theorem 23.2: recursive error relations

This module defines rounded recursive addition and subtraction together with
the max-entry norm and error relations used in the proof of Theorem 23.2. It
also establishes their composition and product-transfer laws.
-/

noncomputable def higham23RecursiveFlAdd (fp : FPModel) (r : ℕ) :
    (depth : ℕ) → Higham23RecursiveMatrix r depth →
      Higham23RecursiveMatrix r depth → Higham23RecursiveMatrix r depth
  | 0, A, B => fun i j ↦ fp.fl_add (A i j) (B i j)
  | depth + 1, A, B =>
      { c11 := higham23RecursiveFlAdd fp r depth A.c11 B.c11
        c12 := higham23RecursiveFlAdd fp r depth A.c12 B.c12
        c21 := higham23RecursiveFlAdd fp r depth A.c21 B.c21
        c22 := higham23RecursiveFlAdd fp r depth A.c22 B.c22 }

/-- Entrywise rounded subtraction at every scalar leaf. -/
noncomputable def higham23RecursiveFlSub (fp : FPModel) (r : ℕ) :
    (depth : ℕ) → Higham23RecursiveMatrix r depth →
      Higham23RecursiveMatrix r depth → Higham23RecursiveMatrix r depth
  | 0, A, B => fun i j ↦ fp.fl_sub (A i j) (B i j)
  | depth + 1, A, B =>
      { c11 := higham23RecursiveFlSub fp r depth A.c11 B.c11
        c12 := higham23RecursiveFlSub fp r depth A.c12 B.c12
        c21 := higham23RecursiveFlSub fp r depth A.c21 B.c21
        c22 := higham23RecursiveFlSub fp r depth A.c22 B.c22 }

/-- Max-entry norm inequality on the recursive block presentation. -/
def Higham23RecursiveMaxNormLe (r : ℕ) :
    (depth : ℕ) → Higham23RecursiveMatrix r depth → ℝ → Prop
  | 0, A, bound => ∀ i j, |A i j| ≤ bound
  | depth + 1, A, bound =>
      Higham23RecursiveMaxNormLe r depth A.c11 bound ∧
      Higham23RecursiveMaxNormLe r depth A.c12 bound ∧
      Higham23RecursiveMaxNormLe r depth A.c21 bound ∧
      Higham23RecursiveMaxNormLe r depth A.c22 bound

/-- Entrywise error inequality on the recursive block presentation. -/
def Higham23RecursiveErrorLe (r : ℕ) :
    (depth : ℕ) → Higham23RecursiveMatrix r depth →
      Higham23RecursiveMatrix r depth → ℝ → Prop
  | 0, A, B, bound => ∀ i j, |A i j - B i j| ≤ bound
  | depth + 1, A, B, bound =>
      Higham23RecursiveErrorLe r depth A.c11 B.c11 bound ∧
      Higham23RecursiveErrorLe r depth A.c12 B.c12 bound ∧
      Higham23RecursiveErrorLe r depth A.c21 B.c21 bound ∧
      Higham23RecursiveErrorLe r depth A.c22 B.c22 bound

theorem higham23_recursiveMaxNormLe_mono (r : ℕ) :
    ∀ depth (A : Higham23RecursiveMatrix r depth) {a b : ℝ},
      Higham23RecursiveMaxNormLe r depth A a → a ≤ b →
        Higham23RecursiveMaxNormLe r depth A b
  | 0, A, a, b, hA, hab => by
      intro i j
      exact (hA i j).trans hab
  | depth + 1, A, a, b, hA, hab => by
      rcases hA with ⟨h11, h12, h21, h22⟩
      exact ⟨higham23_recursiveMaxNormLe_mono r depth A.c11 h11 hab,
        higham23_recursiveMaxNormLe_mono r depth A.c12 h12 hab,
        higham23_recursiveMaxNormLe_mono r depth A.c21 h21 hab,
        higham23_recursiveMaxNormLe_mono r depth A.c22 h22 hab⟩

theorem higham23_recursiveErrorLe_mono (r : ℕ) :
    ∀ depth (A B : Higham23RecursiveMatrix r depth) {a b : ℝ},
      Higham23RecursiveErrorLe r depth A B a → a ≤ b →
        Higham23RecursiveErrorLe r depth A B b
  | 0, A, B, a, b, h, hab => by
      intro i j
      exact (h i j).trans hab
  | depth + 1, A, B, a, b, h, hab => by
      rcases h with ⟨h11, h12, h21, h22⟩
      exact ⟨higham23_recursiveErrorLe_mono r depth A.c11 B.c11 h11 hab,
        higham23_recursiveErrorLe_mono r depth A.c12 B.c12 h12 hab,
        higham23_recursiveErrorLe_mono r depth A.c21 B.c21 h21 hab,
        higham23_recursiveErrorLe_mono r depth A.c22 B.c22 h22 hab⟩

theorem higham23_recursiveMaxNormLe_add (r : ℕ) :
    ∀ depth (A B : Higham23RecursiveMatrix r depth) {a b : ℝ},
      Higham23RecursiveMaxNormLe r depth A a →
      Higham23RecursiveMaxNormLe r depth B b →
      Higham23RecursiveMaxNormLe r depth (A + B) (a + b)
  | 0, A, B, a, b, hA, hB => by
      intro i j
      exact (abs_add_le (A i j) (B i j)).trans
        (add_le_add (hA i j) (hB i j))
  | depth + 1, A, B, a, b, hA, hB => by
      rcases hA with ⟨hA11, hA12, hA21, hA22⟩
      rcases hB with ⟨hB11, hB12, hB21, hB22⟩
      simpa only [higham23Block2_add_c11, higham23Block2_add_c12,
        higham23Block2_add_c21, higham23Block2_add_c22] using
        (show Higham23RecursiveMaxNormLe r depth (A.c11 + B.c11) (a + b) ∧
            Higham23RecursiveMaxNormLe r depth (A.c12 + B.c12) (a + b) ∧
            Higham23RecursiveMaxNormLe r depth (A.c21 + B.c21) (a + b) ∧
            Higham23RecursiveMaxNormLe r depth (A.c22 + B.c22) (a + b) from
          ⟨higham23_recursiveMaxNormLe_add r depth _ _ hA11 hB11,
        higham23_recursiveMaxNormLe_add r depth _ _ hA12 hB12,
        higham23_recursiveMaxNormLe_add r depth _ _ hA21 hB21,
        higham23_recursiveMaxNormLe_add r depth _ _ hA22 hB22⟩)

theorem higham23_recursiveMaxNormLe_sub (r : ℕ) :
    ∀ depth (A B : Higham23RecursiveMatrix r depth) {a b : ℝ},
      Higham23RecursiveMaxNormLe r depth A a →
      Higham23RecursiveMaxNormLe r depth B b →
      Higham23RecursiveMaxNormLe r depth (A - B) (a + b)
  | 0, A, B, a, b, hA, hB => by
      intro i j
      exact (abs_sub (A i j) (B i j)).trans
        (add_le_add (hA i j) (hB i j))
  | depth + 1, A, B, a, b, hA, hB => by
      rcases hA with ⟨hA11, hA12, hA21, hA22⟩
      rcases hB with ⟨hB11, hB12, hB21, hB22⟩
      simpa only [higham23Block2_sub_c11, higham23Block2_sub_c12,
        higham23Block2_sub_c21, higham23Block2_sub_c22] using
        (show Higham23RecursiveMaxNormLe r depth (A.c11 - B.c11) (a + b) ∧
            Higham23RecursiveMaxNormLe r depth (A.c12 - B.c12) (a + b) ∧
            Higham23RecursiveMaxNormLe r depth (A.c21 - B.c21) (a + b) ∧
            Higham23RecursiveMaxNormLe r depth (A.c22 - B.c22) (a + b) from
          ⟨higham23_recursiveMaxNormLe_sub r depth _ _ hA11 hB11,
        higham23_recursiveMaxNormLe_sub r depth _ _ hA12 hB12,
        higham23_recursiveMaxNormLe_sub r depth _ _ hA21 hB21,
        higham23_recursiveMaxNormLe_sub r depth _ _ hA22 hB22⟩)

theorem higham23_recursiveErrorLe_refl (r : ℕ) :
    ∀ depth (A : Higham23RecursiveMatrix r depth),
      Higham23RecursiveErrorLe r depth A A 0
  | 0, A => by simp [Higham23RecursiveErrorLe]
  | depth + 1, A => ⟨higham23_recursiveErrorLe_refl r depth A.c11,
      higham23_recursiveErrorLe_refl r depth A.c12,
      higham23_recursiveErrorLe_refl r depth A.c21,
      higham23_recursiveErrorLe_refl r depth A.c22⟩

theorem higham23_recursiveErrorLe_symm (r : ℕ) :
    ∀ depth (A B : Higham23RecursiveMatrix r depth) {e : ℝ},
      Higham23RecursiveErrorLe r depth A B e →
      Higham23RecursiveErrorLe r depth B A e
  | 0, A, B, e, h => by
      intro i j
      simpa [abs_sub_comm] using h i j
  | depth + 1, A, B, e, h => by
      rcases h with ⟨h11, h12, h21, h22⟩
      exact ⟨higham23_recursiveErrorLe_symm r depth _ _ h11,
        higham23_recursiveErrorLe_symm r depth _ _ h12,
        higham23_recursiveErrorLe_symm r depth _ _ h21,
        higham23_recursiveErrorLe_symm r depth _ _ h22⟩

theorem higham23_recursiveErrorLe_trans (r : ℕ) :
    ∀ depth (A B C : Higham23RecursiveMatrix r depth) {e f : ℝ},
      Higham23RecursiveErrorLe r depth A B e →
      Higham23RecursiveErrorLe r depth B C f →
      Higham23RecursiveErrorLe r depth A C (e + f)
  | 0, A, B, C, e, f, hAB, hBC => by
      intro i j
      calc
        |A i j - C i j| ≤ |A i j - B i j| + |B i j - C i j| := by
          have := abs_add_le (A i j - B i j) (B i j - C i j)
          convert this using 1 <;> ring
        _ ≤ e + f := add_le_add (hAB i j) (hBC i j)
  | depth + 1, A, B, C, e, f, hAB, hBC => by
      rcases hAB with ⟨hAB11, hAB12, hAB21, hAB22⟩
      rcases hBC with ⟨hBC11, hBC12, hBC21, hBC22⟩
      exact ⟨higham23_recursiveErrorLe_trans r depth _ _ _ hAB11 hBC11,
        higham23_recursiveErrorLe_trans r depth _ _ _ hAB12 hBC12,
        higham23_recursiveErrorLe_trans r depth _ _ _ hAB21 hBC21,
        higham23_recursiveErrorLe_trans r depth _ _ _ hAB22 hBC22⟩

theorem higham23_recursiveErrorLe_add (r : ℕ) :
    ∀ depth (A A' B B' : Higham23RecursiveMatrix r depth) {e f : ℝ},
      Higham23RecursiveErrorLe r depth A A' e →
      Higham23RecursiveErrorLe r depth B B' f →
      Higham23RecursiveErrorLe r depth (A + B) (A' + B') (e + f)
  | 0, A, A', B, B', e, f, hA, hB => by
      intro i j
      calc
        |(A + B) i j - (A' + B') i j| ≤
            |A i j - A' i j| + |B i j - B' i j| := by
          have := abs_add_le (A i j - A' i j) (B i j - B' i j)
          change |(A i j + B i j) - (A' i j + B' i j)| ≤ _
          convert this using 1 <;> ring
        _ ≤ e + f := add_le_add (hA i j) (hB i j)
  | depth + 1, A, A', B, B', e, f, hA, hB => by
      rcases hA with ⟨hA11, hA12, hA21, hA22⟩
      rcases hB with ⟨hB11, hB12, hB21, hB22⟩
      simpa only [higham23Block2_add_c11, higham23Block2_add_c12,
        higham23Block2_add_c21, higham23Block2_add_c22] using
        (show Higham23RecursiveErrorLe r depth (A.c11 + B.c11)
              (A'.c11 + B'.c11) (e + f) ∧
            Higham23RecursiveErrorLe r depth (A.c12 + B.c12)
              (A'.c12 + B'.c12) (e + f) ∧
            Higham23RecursiveErrorLe r depth (A.c21 + B.c21)
              (A'.c21 + B'.c21) (e + f) ∧
            Higham23RecursiveErrorLe r depth (A.c22 + B.c22)
              (A'.c22 + B'.c22) (e + f) from
          ⟨higham23_recursiveErrorLe_add r depth _ _ _ _ hA11 hB11,
        higham23_recursiveErrorLe_add r depth _ _ _ _ hA12 hB12,
        higham23_recursiveErrorLe_add r depth _ _ _ _ hA21 hB21,
        higham23_recursiveErrorLe_add r depth _ _ _ _ hA22 hB22⟩)

theorem higham23_recursiveErrorLe_sub (r : ℕ) :
    ∀ depth (A A' B B' : Higham23RecursiveMatrix r depth) {e f : ℝ},
      Higham23RecursiveErrorLe r depth A A' e →
      Higham23RecursiveErrorLe r depth B B' f →
      Higham23RecursiveErrorLe r depth (A - B) (A' - B') (e + f)
  | 0, A, A', B, B', e, f, hA, hB => by
      intro i j
      calc
        |(A - B) i j - (A' - B') i j| ≤
            |A i j - A' i j| + |B i j - B' i j| := by
          have := abs_sub (A i j - A' i j) (B i j - B' i j)
          change |(A i j - B i j) - (A' i j - B' i j)| ≤ _
          convert this using 1 <;> ring
        _ ≤ e + f := add_le_add (hA i j) (hB i j)
  | depth + 1, A, A', B, B', e, f, hA, hB => by
      rcases hA with ⟨hA11, hA12, hA21, hA22⟩
      rcases hB with ⟨hB11, hB12, hB21, hB22⟩
      simpa only [higham23Block2_sub_c11, higham23Block2_sub_c12,
        higham23Block2_sub_c21, higham23Block2_sub_c22] using
        (show Higham23RecursiveErrorLe r depth (A.c11 - B.c11)
              (A'.c11 - B'.c11) (e + f) ∧
            Higham23RecursiveErrorLe r depth (A.c12 - B.c12)
              (A'.c12 - B'.c12) (e + f) ∧
            Higham23RecursiveErrorLe r depth (A.c21 - B.c21)
              (A'.c21 - B'.c21) (e + f) ∧
            Higham23RecursiveErrorLe r depth (A.c22 - B.c22)
              (A'.c22 - B'.c22) (e + f) from
          ⟨higham23_recursiveErrorLe_sub r depth _ _ _ _ hA11 hB11,
        higham23_recursiveErrorLe_sub r depth _ _ _ _ hA12 hB12,
        higham23_recursiveErrorLe_sub r depth _ _ _ _ hA21 hB21,
        higham23_recursiveErrorLe_sub r depth _ _ _ _ hA22 hB22⟩)

/-- A norm bound and an error bound control the computed object. -/
theorem higham23_recursiveMaxNormLe_of_error (r : ℕ) :
    ∀ depth (A B : Higham23RecursiveMatrix r depth) {a e : ℝ},
      Higham23RecursiveMaxNormLe r depth A a →
      Higham23RecursiveErrorLe r depth A B e →
      Higham23RecursiveMaxNormLe r depth B (a + e)
  | 0, A, B, a, e, hA, hE => by
      intro i j
      calc
        |B i j| ≤ |A i j| + |A i j - B i j| := by
          have := abs_add_le (A i j) (B i j - A i j)
          rw [show A i j + (B i j - A i j) = B i j by ring] at this
          simpa [abs_sub_comm] using this
        _ ≤ a + e := add_le_add (hA i j) (hE i j)
  | depth + 1, A, B, a, e, hA, hE => by
      rcases hA with ⟨hA11, hA12, hA21, hA22⟩
      rcases hE with ⟨hE11, hE12, hE21, hE22⟩
      exact ⟨higham23_recursiveMaxNormLe_of_error r depth _ _ hA11 hE11,
        higham23_recursiveMaxNormLe_of_error r depth _ _ hA12 hE12,
        higham23_recursiveMaxNormLe_of_error r depth _ _ hA21 hE21,
        higham23_recursiveMaxNormLe_of_error r depth _ _ hA22 hE22⟩

/-- Exact matrix multiplication has the usual dimension factor in max-entry
norm, stated on the recursive block representation. -/
theorem higham23_recursiveMaxNormLe_mul (r : ℕ) :
    ∀ depth (A B : Higham23RecursiveMatrix r depth) (a b : ℝ),
      0 ≤ a → 0 ≤ b →
      Higham23RecursiveMaxNormLe r depth A a →
      Higham23RecursiveMaxNormLe r depth B b →
      Higham23RecursiveMaxNormLe r depth (A * B)
        ((2 ^ (r + depth) : ℕ) * a * b)
  | 0, A, B, a, b, ha, _hb, hA, hB => by
      intro i j
      change |∑ k : Fin (2 ^ r), A i k * B k j| ≤ _
      calc
        |∑ k : Fin (2 ^ r), A i k * B k j| ≤
            ∑ k : Fin (2 ^ r), |A i k * B k j| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k : Fin (2 ^ r), a * b := by
          apply Finset.sum_le_sum
          intro k _
          rw [abs_mul]
          exact mul_le_mul (hA i k) (hB k j) (abs_nonneg _) ha
        _ = ((2 ^ (r + 0) : ℕ) : ℝ) * a * b := by simp; ring
  | depth + 1, A, B, a, b, ha, hb, hA, hB => by
      rcases hA with ⟨hA11, hA12, hA21, hA22⟩
      rcases hB with ⟨hB11, hB12, hB21, hB22⟩
      let m : ℝ := (2 ^ (r + depth) : ℕ)
      have h11a := higham23_recursiveMaxNormLe_mul r depth
        A.c11 B.c11 a b ha hb hA11 hB11
      have h11b := higham23_recursiveMaxNormLe_mul r depth
        A.c12 B.c21 a b ha hb hA12 hB21
      have h12a := higham23_recursiveMaxNormLe_mul r depth
        A.c11 B.c12 a b ha hb hA11 hB12
      have h12b := higham23_recursiveMaxNormLe_mul r depth
        A.c12 B.c22 a b ha hb hA12 hB22
      have h21a := higham23_recursiveMaxNormLe_mul r depth
        A.c21 B.c11 a b ha hb hA21 hB11
      have h21b := higham23_recursiveMaxNormLe_mul r depth
        A.c22 B.c21 a b ha hb hA22 hB21
      have h22a := higham23_recursiveMaxNormLe_mul r depth
        A.c21 B.c12 a b ha hb hA21 hB12
      have h22b := higham23_recursiveMaxNormLe_mul r depth
        A.c22 B.c22 a b ha hb hA22 hB22
      have h11 := higham23_recursiveMaxNormLe_add r depth _ _ h11a h11b
      have h12 := higham23_recursiveMaxNormLe_add r depth _ _ h12a h12b
      have h21 := higham23_recursiveMaxNormLe_add r depth _ _ h21a h21b
      have h22 := higham23_recursiveMaxNormLe_add r depth _ _ h22a h22b
      have hpow : ((2 ^ (r + (depth + 1)) : ℕ) : ℝ) * a * b =
          (((2 ^ (r + depth) : ℕ) : ℝ) * a * b) +
            (((2 ^ (r + depth) : ℕ) : ℝ) * a * b) := by
        rw [show r + (depth + 1) = (r + depth) + 1 by omega, pow_succ]
        push_cast
        ring
      rw [hpow]
      simpa only [higham23Block2_mul_c11, higham23Block2_mul_c12,
        higham23Block2_mul_c21, higham23Block2_mul_c22] using
        (show Higham23RecursiveMaxNormLe r depth
              (A.c11 * B.c11 + A.c12 * B.c21) _ ∧
            Higham23RecursiveMaxNormLe r depth
              (A.c11 * B.c12 + A.c12 * B.c22) _ ∧
            Higham23RecursiveMaxNormLe r depth
              (A.c21 * B.c11 + A.c22 * B.c21) _ ∧
            Higham23RecursiveMaxNormLe r depth
              (A.c21 * B.c12 + A.c22 * B.c22) _ from
          ⟨h11, h12, h21, h22⟩)

theorem higham23_recursiveMaxNormLe_sub_of_error (r : ℕ) :
    ∀ depth (A B : Higham23RecursiveMatrix r depth) {e : ℝ},
      Higham23RecursiveErrorLe r depth A B e →
      Higham23RecursiveMaxNormLe r depth (A - B) e
  | 0, A, B, e, h => by simpa [Higham23RecursiveMaxNormLe] using h
  | depth + 1, A, B, e, h => by
      rcases h with ⟨h11, h12, h21, h22⟩
      exact ⟨higham23_recursiveMaxNormLe_sub_of_error r depth _ _ h11,
        higham23_recursiveMaxNormLe_sub_of_error r depth _ _ h12,
        higham23_recursiveMaxNormLe_sub_of_error r depth _ _ h21,
        higham23_recursiveMaxNormLe_sub_of_error r depth _ _ h22⟩

theorem higham23_recursiveErrorLe_of_maxNorm_sub (r : ℕ) :
    ∀ depth (A B : Higham23RecursiveMatrix r depth) {e : ℝ},
      Higham23RecursiveMaxNormLe r depth (A - B) e →
      Higham23RecursiveErrorLe r depth A B e
  | 0, A, B, e, h => by simpa [Higham23RecursiveMaxNormLe] using h
  | depth + 1, A, B, e, h => by
      rcases h with ⟨h11, h12, h21, h22⟩
      exact ⟨higham23_recursiveErrorLe_of_maxNorm_sub r depth _ _ h11,
        higham23_recursiveErrorLe_of_maxNorm_sub r depth _ _ h12,
        higham23_recursiveErrorLe_of_maxNorm_sub r depth _ _ h21,
        higham23_recursiveErrorLe_of_maxNorm_sub r depth _ _ h22⟩

/-- Perturbing both inputs of an exact product. -/
theorem higham23_recursiveErrorLe_mul (r depth : ℕ)
    (A Ahat B Bhat : Higham23RecursiveMatrix r depth)
    (aHat b dx dy : ℝ) (haHat : 0 ≤ aHat) (hb : 0 ≤ b)
    (hdx : 0 ≤ dx) (hdy : 0 ≤ dy)
    (hAhat : Higham23RecursiveMaxNormLe r depth Ahat aHat)
    (hB : Higham23RecursiveMaxNormLe r depth B b)
    (hAerr : Higham23RecursiveErrorLe r depth Ahat A dx)
    (hBerr : Higham23RecursiveErrorLe r depth Bhat B dy) :
    Higham23RecursiveErrorLe r depth (Ahat * Bhat) (A * B)
      (((2 ^ (r + depth) : ℕ) : ℝ) * dx * b +
        ((2 ^ (r + depth) : ℕ) : ℝ) * aHat * dy) := by
  have hDA := higham23_recursiveMaxNormLe_sub_of_error r depth Ahat A hAerr
  have hDB := higham23_recursiveMaxNormLe_sub_of_error r depth Bhat B hBerr
  have hfirst := higham23_recursiveMaxNormLe_mul r depth
    (Ahat - A) B dx b hdx hb hDA hB
  have hsecond := higham23_recursiveMaxNormLe_mul r depth
    Ahat (Bhat - B) aHat dy haHat hdy hAhat hDB
  have hsum := higham23_recursiveMaxNormLe_add r depth _ _ hfirst hsecond
  have hid : Ahat * Bhat - A * B =
      (Ahat - A) * B + Ahat * (Bhat - B) := by noncomm_ring
  rw [← hid] at hsum
  exact higham23_recursiveErrorLe_of_maxNorm_sub r depth _ _ hsum

/-- One rounded recursive addition introduces the standard local relative
error, uniformly across all scalar leaves. -/
theorem higham23_recursiveFlAdd_error (fp : FPModel) (r : ℕ) :
    ∀ depth (A B : Higham23RecursiveMatrix r depth) (a b : ℝ),
      0 ≤ a → 0 ≤ b →
      Higham23RecursiveMaxNormLe r depth A a →
      Higham23RecursiveMaxNormLe r depth B b →
      Higham23RecursiveErrorLe r depth (A + B)
        (higham23RecursiveFlAdd fp r depth A B) (fp.u * (a + b))
  | 0, A, B, a, b, ha, hb, hA, hB => by
      intro i j
      obtain ⟨delta, hdelta, hfl⟩ := fp.model_add (A i j) (B i j)
      change |A i j + B i j - fp.fl_add (A i j) (B i j)| ≤ _
      rw [hfl, show A i j + B i j - (A i j + B i j) * (1 + delta) =
        -(A i j + B i j) * delta by ring, abs_mul, abs_neg]
      calc
        |A i j + B i j| * |delta| ≤ (a + b) * fp.u := by
          exact mul_le_mul
            ((abs_add_le _ _).trans (add_le_add (hA i j) (hB i j)))
            hdelta (abs_nonneg _) (add_nonneg ha hb)
        _ = fp.u * (a + b) := by ring
  | depth + 1, A, B, a, b, ha, hb, hA, hB => by
      rcases hA with ⟨hA11, hA12, hA21, hA22⟩
      rcases hB with ⟨hB11, hB12, hB21, hB22⟩
      exact ⟨higham23_recursiveFlAdd_error fp r depth _ _ a b ha hb hA11 hB11,
        higham23_recursiveFlAdd_error fp r depth _ _ a b ha hb hA12 hB12,
        higham23_recursiveFlAdd_error fp r depth _ _ a b ha hb hA21 hB21,
        higham23_recursiveFlAdd_error fp r depth _ _ a b ha hb hA22 hB22⟩

theorem higham23_recursiveFlSub_error (fp : FPModel) (r : ℕ) :
    ∀ depth (A B : Higham23RecursiveMatrix r depth) (a b : ℝ),
      0 ≤ a → 0 ≤ b →
      Higham23RecursiveMaxNormLe r depth A a →
      Higham23RecursiveMaxNormLe r depth B b →
      Higham23RecursiveErrorLe r depth (A - B)
        (higham23RecursiveFlSub fp r depth A B) (fp.u * (a + b))
  | 0, A, B, a, b, ha, hb, hA, hB => by
      intro i j
      obtain ⟨delta, hdelta, hfl⟩ := fp.model_sub (A i j) (B i j)
      change |A i j - B i j - fp.fl_sub (A i j) (B i j)| ≤ _
      rw [hfl, show A i j - B i j - (A i j - B i j) * (1 + delta) =
        -(A i j - B i j) * delta by ring, abs_mul, abs_neg]
      calc
        |A i j - B i j| * |delta| ≤ (a + b) * fp.u := by
          exact mul_le_mul
            ((abs_sub _ _).trans (add_le_add (hA i j) (hB i j)))
            hdelta (abs_nonneg _) (add_nonneg ha hb)
        _ = fp.u * (a + b) := by ring
  | depth + 1, A, B, a, b, ha, hb, hA, hB => by
      rcases hA with ⟨hA11, hA12, hA21, hA22⟩
      rcases hB with ⟨hB11, hB12, hB21, hB22⟩
      exact ⟨higham23_recursiveFlSub_error fp r depth _ _ a b ha hb hA11 hB11,
        higham23_recursiveFlSub_error fp r depth _ _ a b ha hb hA12 hB12,
        higham23_recursiveFlSub_error fp r depth _ _ a b ha hb hA21 hB21,
        higham23_recursiveFlSub_error fp r depth _ _ a b ha hb hA22 hB22⟩

theorem higham23_recursiveFlAdd_norm (fp : FPModel) (r depth : ℕ)
    (A B : Higham23RecursiveMatrix r depth) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : Higham23RecursiveMaxNormLe r depth A a)
    (hB : Higham23RecursiveMaxNormLe r depth B b) :
    Higham23RecursiveMaxNormLe r depth
      (higham23RecursiveFlAdd fp r depth A B) ((1 + fp.u) * (a + b)) := by
  have hExact := higham23_recursiveMaxNormLe_add r depth A B hA hB
  have hErr := higham23_recursiveFlAdd_error fp r depth A B a b ha hb hA hB
  have h := higham23_recursiveMaxNormLe_of_error r depth _ _ hExact hErr
  convert h using 1 <;> ring

theorem higham23_recursiveFlSub_norm (fp : FPModel) (r depth : ℕ)
    (A B : Higham23RecursiveMatrix r depth) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : Higham23RecursiveMaxNormLe r depth A a)
    (hB : Higham23RecursiveMaxNormLe r depth B b) :
    Higham23RecursiveMaxNormLe r depth
      (higham23RecursiveFlSub fp r depth A B) ((1 + fp.u) * (a + b)) := by
  have hExact := higham23_recursiveMaxNormLe_sub r depth A B hA hB
  have hErr := higham23_recursiveFlSub_error fp r depth A B a b ha hb hA hB
  have h := higham23_recursiveMaxNormLe_of_error r depth _ _ hExact hErr
  convert h using 1 <;> ring

theorem higham23_recursiveFlAdd_pair (fp : FPModel) (r depth : ℕ)
    (A B : Higham23RecursiveMatrix r depth) (a : ℝ) (ha : 0 ≤ a)
    (hA : Higham23RecursiveMaxNormLe r depth A a)
    (hB : Higham23RecursiveMaxNormLe r depth B a) :
    Higham23RecursiveMaxNormLe r depth
        (higham23RecursiveFlAdd fp r depth A B) (2 * (1 + fp.u) * a) ∧
      Higham23RecursiveErrorLe r depth
        (higham23RecursiveFlAdd fp r depth A B) (A + B) (2 * fp.u * a) := by
  constructor
  · convert higham23_recursiveFlAdd_norm fp r depth A B a a ha ha hA hB using 1 <;>
      ring
  · apply higham23_recursiveErrorLe_symm r depth
    convert higham23_recursiveFlAdd_error fp r depth A B a a ha ha hA hB using 1 <;>
      ring

theorem higham23_recursiveFlSub_pair (fp : FPModel) (r depth : ℕ)
    (A B : Higham23RecursiveMatrix r depth) (a : ℝ) (ha : 0 ≤ a)
    (hA : Higham23RecursiveMaxNormLe r depth A a)
    (hB : Higham23RecursiveMaxNormLe r depth B a) :
    Higham23RecursiveMaxNormLe r depth
        (higham23RecursiveFlSub fp r depth A B) (2 * (1 + fp.u) * a) ∧
      Higham23RecursiveErrorLe r depth
        (higham23RecursiveFlSub fp r depth A B) (A - B) (2 * fp.u * a) := by
  constructor
  · convert higham23_recursiveFlSub_norm fp r depth A B a a ha ha hA hB using 1 <;>
      ring
  · apply higham23_recursiveErrorLe_symm r depth
    convert higham23_recursiveFlSub_error fp r depth A B a a ha ha hA hB using 1 <;>
      ring

/-- Transfer a recursive-product error theorem across rounded input
preparations.  This is the operation-level step used for each of the seven
Strassen products. -/
theorem higham23_recursiveProduct_transfer (r depth : ℕ)
    (X Xhat Y Yhat P : Higham23RecursiveMatrix r depth)
    (xHat y dx dy e : ℝ)
    (hxHat : 0 ≤ xHat) (hy : 0 ≤ y) (hdx : 0 ≤ dx)
    (hdy : 0 ≤ dy)
    (hXhat : Higham23RecursiveMaxNormLe r depth Xhat xHat)
    (hY : Higham23RecursiveMaxNormLe r depth Y y)
    (hYhat : Higham23RecursiveMaxNormLe r depth Yhat (y + dy))
    (hXerr : Higham23RecursiveErrorLe r depth Xhat X dx)
    (hYerr : Higham23RecursiveErrorLe r depth Yhat Y dy)
    (hRec : Higham23RecursiveErrorLe r depth (Xhat * Yhat) P
      (e * xHat * (y + dy))) :
    Higham23RecursiveErrorLe r depth (X * Y) P
        ((((2 ^ (r + depth) : ℕ) : ℝ) * dx * y +
          ((2 ^ (r + depth) : ℕ) : ℝ) * xHat * dy) +
            e * xHat * (y + dy)) ∧
      Higham23RecursiveMaxNormLe r depth P
        ((((2 ^ (r + depth) : ℕ) : ℝ) + e) * xHat * (y + dy)) := by
  have hyHat0 : 0 ≤ y + dy := add_nonneg hy hdy
  have hInput := higham23_recursiveErrorLe_mul r depth
    X Xhat Y Yhat xHat y dx dy hxHat hy hdx hdy hXhat hY hXerr hYerr
  have hInput' := higham23_recursiveErrorLe_symm r depth _ _ hInput
  have hErr := higham23_recursiveErrorLe_trans r depth _ _ _ hInput' hRec
  have hExact := higham23_recursiveMaxNormLe_mul r depth
    Xhat Yhat xHat (y + dy) hxHat hyHat0 hXhat hYhat
  have hNorm := higham23_recursiveMaxNormLe_of_error r depth _ _ hExact hRec
  refine ⟨hErr, ?_⟩
  convert hNorm using 1 <;> ring

end NumStability
