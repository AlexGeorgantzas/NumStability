/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import Mathlib.Tactic.NoncommRing
import NumStability.Algorithms.DotProduct

namespace NumStability

open scoped BigOperators

/-!
# Higham Chapter 23: Bini--Lotti recursive algebra

Recursive matrices, rounded dot products, error relations, and product certificates used by the Bini--Lotti bilinear evaluator.
-/

abbrev Higham23BiniMatrix (h : ℕ) : ℕ → Type
  | 0 => ℝ
  | depth + 1 => Matrix (Fin h) (Fin h) (Higham23BiniMatrix h depth)

noncomputable def higham23BiniExactDot (h n : ℕ) :
    ∀ depth, (Fin n → ℝ) → (Fin n → Higham23BiniMatrix h depth) →
      Higham23BiniMatrix h depth
  | 0, c, X => ∑ q, c q * X q
  | depth + 1, c, X => fun i j ↦
      higham23BiniExactDot h n depth c (fun q ↦ X q i j)

noncomputable def higham23BiniAdd (h : ℕ) :
    ∀ depth, Higham23BiniMatrix h depth → Higham23BiniMatrix h depth →
      Higham23BiniMatrix h depth
  | 0, x, y => x + y
  | depth + 1, X, Y => fun i j ↦ higham23BiniAdd h depth (X i j) (Y i j)

noncomputable def higham23BiniSub (h : ℕ) :
    ∀ depth, Higham23BiniMatrix h depth → Higham23BiniMatrix h depth →
      Higham23BiniMatrix h depth
  | 0, x, y => x - y
  | depth + 1, X, Y => fun i j ↦ higham23BiniSub h depth (X i j) (Y i j)

noncomputable def higham23BiniMul (h : ℕ) :
    ∀ depth, Higham23BiniMatrix h depth → Higham23BiniMatrix h depth →
      Higham23BiniMatrix h depth
  | 0, x, y => x * y
  | depth + 1, A, B => fun i j ↦
      higham23BiniExactDot h h depth (fun _ ↦ (1 : ℝ))
        (fun k ↦ higham23BiniMul h depth (A i k) (B k j))

noncomputable def higham23BiniFlDot (fp : FPModel) (h n : ℕ) :
    ∀ depth, (Fin n → ℝ) → (Fin n → Higham23BiniMatrix h depth) →
      Higham23BiniMatrix h depth
  | 0, c, X => fl_dotProduct fp n c X
  | depth + 1, c, X => fun i j ↦
      higham23BiniFlDot fp h n depth c (fun q ↦ X q i j)

def Higham23BiniNormLe (h : ℕ) :
    ∀ depth, Higham23BiniMatrix h depth → ℝ → Prop
  | 0, x, a => |x| ≤ a
  | depth + 1, A, a => ∀ i j, Higham23BiniNormLe h depth (A i j) a

def Higham23BiniErrorLe (h : ℕ) :
    ∀ depth, Higham23BiniMatrix h depth → Higham23BiniMatrix h depth → ℝ → Prop
  | 0, x, y, e => |x - y| ≤ e
  | depth + 1, A, B, e => ∀ i j, Higham23BiniErrorLe h depth (A i j) (B i j) e

theorem higham23_biniError_refl (h : ℕ) :
    ∀ depth (X : Higham23BiniMatrix h depth), Higham23BiniErrorLe h depth X X 0
  | 0, X => by simp [Higham23BiniErrorLe]
  | depth + 1, X => fun i j ↦ higham23_biniError_refl h depth (X i j)

theorem higham23_biniError_symm (h : ℕ) :
    ∀ depth (X Y : Higham23BiniMatrix h depth) {e : ℝ},
      Higham23BiniErrorLe h depth X Y e → Higham23BiniErrorLe h depth Y X e
  | 0, X, Y, e, hE => by simpa [Higham23BiniErrorLe, abs_sub_comm] using hE
  | depth + 1, X, Y, e, hE => fun i j ↦
      higham23_biniError_symm h depth (X i j) (Y i j) (hE i j)

theorem higham23_biniError_trans (h : ℕ) :
    ∀ depth (X Y Z : Higham23BiniMatrix h depth) {e f : ℝ},
      Higham23BiniErrorLe h depth X Y e →
      Higham23BiniErrorLe h depth Y Z f →
      Higham23BiniErrorLe h depth X Z (e + f)
  | 0, X, Y, Z, e, f, hXY, hYZ => by
      change |X - Z| ≤ e + f
      calc
        |X - Z| ≤ |X - Y| + |Y - Z| := by
          have h := abs_add_le (X - Y) (Y - Z)
          convert h using 1 <;> ring
        _ ≤ e + f := add_le_add hXY hYZ
  | depth + 1, X, Y, Z, e, f, hXY, hYZ => fun i j ↦
      higham23_biniError_trans h depth (X i j) (Y i j) (Z i j)
        (hXY i j) (hYZ i j)

theorem higham23_biniError_mono (h : ℕ) :
    ∀ depth (X Y : Higham23BiniMatrix h depth) {e f : ℝ},
      Higham23BiniErrorLe h depth X Y e → e ≤ f →
      Higham23BiniErrorLe h depth X Y f
  | 0, X, Y, e, f, hE, hef => hE.trans hef
  | depth + 1, X, Y, e, f, hE, hef => fun i j ↦
      higham23_biniError_mono h depth (X i j) (Y i j) (hE i j) hef

theorem higham23_biniNorm_of_error (h : ℕ) :
    ∀ depth (X Y : Higham23BiniMatrix h depth) {a e : ℝ},
      Higham23BiniNormLe h depth X a → Higham23BiniErrorLe h depth X Y e →
      Higham23BiniNormLe h depth Y (a + e)
  | 0, X, Y, a, e, hX, hE => by
      change |Y| ≤ a + e
      calc
        |Y| ≤ |X| + |X - Y| := by
          have h := abs_add_le X (Y - X)
          rw [show X + (Y - X) = Y by ring] at h
          simpa [abs_sub_comm] using h
        _ ≤ a + e := add_le_add hX hE
  | depth + 1, X, Y, a, e, hX, hE => fun i j ↦
      higham23_biniNorm_of_error h depth (X i j) (Y i j) (hX i j) (hE i j)

/-- A varying-radius leafwise dot-product certificate. -/
theorem higham23_biniFlDot_certificate
    (fp : FPModel) (h n : ℕ) (hvalid : gammaValid fp n) :
    ∀ depth (c : Fin n → ℝ)
      (X Xhat : Fin n → Higham23BiniMatrix h depth)
      (e rad : Fin n → ℝ),
      (∀ q, 0 ≤ e q) → (∀ q, 0 ≤ rad q) →
      (∀ q, Higham23BiniErrorLe h depth (X q) (Xhat q) (e q)) →
      (∀ q, Higham23BiniNormLe h depth (Xhat q) (rad q)) →
      Higham23BiniErrorLe h depth (higham23BiniExactDot h n depth c X)
        (higham23BiniFlDot fp h n depth c Xhat)
        ((∑ q, |c q| * e q) + gamma fp n * (∑ q, |c q| * rad q)) ∧
      Higham23BiniNormLe h depth (higham23BiniFlDot fp h n depth c Xhat)
        ((1 + gamma fp n) * (∑ q, |c q| * rad q))
  | 0, c, X, Xhat, e, rad, he0, hr0, hE, hN => by
      have hinput : |(∑ q, c q * X q) - ∑ q, c q * Xhat q| ≤
          ∑ q, |c q| * e q := by
        rw [← Finset.sum_sub_distrib]
        calc
          |∑ q, (c q * X q - c q * Xhat q)| ≤
              ∑ q, |c q * X q - c q * Xhat q| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ q, |c q| * e q := by
            apply Finset.sum_le_sum
            intro q _
            rw [show c q * X q - c q * Xhat q = c q * (X q - Xhat q) by ring,
              abs_mul]
            exact mul_le_mul_of_nonneg_left (hE q) (abs_nonneg _)
      have hweighted : (∑ q, |c q| * |Xhat q|) ≤ ∑ q, |c q| * rad q := by
        apply Finset.sum_le_sum
        intro q _
        exact mul_le_mul_of_nonneg_left (hN q) (abs_nonneg _)
      have hlocalRaw := dotProduct_error_bound fp n c Xhat hvalid
      have hlocal : |(∑ q, c q * Xhat q) - fl_dotProduct fp n c Xhat| ≤
          gamma fp n * (∑ q, |c q| * rad q) := by
        rw [abs_sub_comm]
        exact hlocalRaw.trans
          (mul_le_mul_of_nonneg_left hweighted (gamma_nonneg fp hvalid))
      have htotal : |(∑ q, c q * X q) - fl_dotProduct fp n c Xhat| ≤
          (∑ q, |c q| * e q) + gamma fp n * (∑ q, |c q| * rad q) := by
        calc
          |(∑ q, c q * X q) - fl_dotProduct fp n c Xhat| ≤
              |(∑ q, c q * X q) - ∑ q, c q * Xhat q| +
                |(∑ q, c q * Xhat q) - fl_dotProduct fp n c Xhat| := by
            have hh := abs_add_le
              ((∑ q, c q * X q) - ∑ q, c q * Xhat q)
              ((∑ q, c q * Xhat q) - fl_dotProduct fp n c Xhat)
            convert hh using 1 <;> ring
          _ ≤ _ := add_le_add hinput hlocal
      have hExactHat : |∑ q, c q * Xhat q| ≤ ∑ q, |c q| * rad q := by
        calc
          |∑ q, c q * Xhat q| ≤ ∑ q, |c q * Xhat q| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ q, |c q| * rad q := by
            apply Finset.sum_le_sum
            intro q _
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hN q) (abs_nonneg _)
      have hflNorm : |fl_dotProduct fp n c Xhat| ≤
          (1 + gamma fp n) * (∑ q, |c q| * rad q) := by
        calc
          |fl_dotProduct fp n c Xhat| ≤ |∑ q, c q * Xhat q| +
              |(∑ q, c q * Xhat q) - fl_dotProduct fp n c Xhat| := by
            have hh := abs_add_le (∑ q, c q * Xhat q)
              (fl_dotProduct fp n c Xhat - ∑ q, c q * Xhat q)
            rw [show (∑ q, c q * Xhat q) +
              (fl_dotProduct fp n c Xhat - ∑ q, c q * Xhat q) =
                fl_dotProduct fp n c Xhat by ring] at hh
            simpa [abs_sub_comm] using hh
          _ ≤ (∑ q, |c q| * rad q) +
              gamma fp n * (∑ q, |c q| * rad q) :=
            add_le_add hExactHat hlocal
          _ = _ := by ring
      exact ⟨htotal, hflNorm⟩
  | depth + 1, c, X, Xhat, e, rad, he0, hr0, hE, hN => by
      constructor
      · intro i j
        exact (higham23_biniFlDot_certificate fp h n hvalid depth c
          (fun q ↦ X q i j) (fun q ↦ Xhat q i j) e rad he0 hr0
          (fun q ↦ hE q i j) (fun q ↦ hN q i j)).1
      · intro i j
        exact (higham23_biniFlDot_certificate fp h n hvalid depth c
          (fun q ↦ X q i j) (fun q ↦ Xhat q i j) e rad he0 hr0
          (fun q ↦ hE q i j) (fun q ↦ hN q i j)).2

theorem higham23_biniExactDot_norm (h n : ℕ) :
    ∀ depth (c : Fin n → ℝ) (X : Fin n → Higham23BiniMatrix h depth)
      (rad : Fin n → ℝ),
      (∀ q, 0 ≤ rad q) →
      (∀ q, Higham23BiniNormLe h depth (X q) (rad q)) →
      Higham23BiniNormLe h depth (higham23BiniExactDot h n depth c X)
        (∑ q, |c q| * rad q)
  | 0, c, X, rad, _hr0, hN => by
      calc
        |∑ q, c q * X q| ≤ ∑ q, |c q * X q| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ q, |c q| * rad q := by
          apply Finset.sum_le_sum
          intro q _
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hN q) (abs_nonneg _)
  | depth + 1, c, X, rad, hr0, hN => fun i j ↦
      higham23_biniExactDot_norm h n depth c (fun q ↦ X q i j) rad hr0
        (fun q ↦ hN q i j)

theorem higham23_biniNorm_add (h : ℕ) :
    ∀ depth (X Y : Higham23BiniMatrix h depth) {a b : ℝ},
      Higham23BiniNormLe h depth X a → Higham23BiniNormLe h depth Y b →
      Higham23BiniNormLe h depth (higham23BiniAdd h depth X Y) (a + b)
  | 0, X, Y, a, b, hX, hY => by
      exact (abs_add_le X Y).trans (add_le_add hX hY)
  | depth + 1, X, Y, a, b, hX, hY => fun i j ↦
      higham23_biniNorm_add h depth (X i j) (Y i j) (hX i j) (hY i j)

theorem higham23_biniNorm_sub_of_error (h : ℕ) :
    ∀ depth (X Y : Higham23BiniMatrix h depth) {e : ℝ},
      Higham23BiniErrorLe h depth X Y e →
      Higham23BiniNormLe h depth (higham23BiniSub h depth X Y) e
  | 0, X, Y, e, hE => hE
  | depth + 1, X, Y, e, hE => fun i j ↦
      higham23_biniNorm_sub_of_error h depth (X i j) (Y i j) (hE i j)

theorem higham23_biniError_of_norm_sub (h : ℕ) :
    ∀ depth (X Y : Higham23BiniMatrix h depth) {e : ℝ},
      Higham23BiniNormLe h depth (higham23BiniSub h depth X Y) e →
      Higham23BiniErrorLe h depth X Y e
  | 0, X, Y, e, hE => hE
  | depth + 1, X, Y, e, hE => fun i j ↦
      higham23_biniError_of_norm_sub h depth (X i j) (Y i j) (hE i j)

theorem higham23_biniNorm_mul (h : ℕ) :
    ∀ depth (A B : Higham23BiniMatrix h depth) (a b : ℝ),
      0 ≤ a → 0 ≤ b →
      Higham23BiniNormLe h depth A a → Higham23BiniNormLe h depth B b →
      Higham23BiniNormLe h depth (higham23BiniMul h depth A B)
        (((h ^ depth : ℕ) : ℝ) * a * b)
  | 0, A, B, a, b, ha, _hb, hA, hB => by
      change |A * B| ≤ _
      rw [abs_mul]
      have hh := mul_le_mul hA hB (abs_nonneg _) ha
      simpa using hh
  | depth + 1, A, B, a, b, ha, hb, hA, hB => by
      intro i j
      let nrad : ℝ := ((h ^ depth : ℕ) : ℝ) * a * b
      have hprod (k : Fin h) : Higham23BiniNormLe h depth
          (higham23BiniMul h depth (A i k) (B k j)) nrad :=
        higham23_biniNorm_mul h depth (A i k) (B k j) a b ha hb
          (hA i k) (hB k j)
      have hsum := higham23_biniExactDot_norm h h depth
        (fun _ ↦ (1 : ℝ))
        (fun k ↦ higham23BiniMul h depth (A i k) (B k j)) (fun _ ↦ nrad)
        (fun _ ↦ by dsimp [nrad]; positivity) hprod
      have hpow : (∑ _k : Fin h, |(1 : ℝ)| * nrad) =
          (((h ^ (depth + 1) : ℕ) : ℝ) * a * b) := by
        simp [nrad, pow_succ]
        push_cast
        ring
      rw [← hpow]
      exact hsum

theorem higham23_biniExactDot_error (h n : ℕ) :
    ∀ depth (c : Fin n → ℝ)
      (X Y : Fin n → Higham23BiniMatrix h depth) (e : Fin n → ℝ),
      (∀ q, 0 ≤ e q) →
      (∀ q, Higham23BiniErrorLe h depth (X q) (Y q) (e q)) →
      Higham23BiniErrorLe h depth
        (higham23BiniExactDot h n depth c X)
        (higham23BiniExactDot h n depth c Y)
        (∑ q, |c q| * e q)
  | 0, c, X, Y, e, _he0, hE => by
      change |(∑ q, c q * X q) - ∑ q, c q * Y q| ≤ ∑ q, |c q| * e q
      rw [← Finset.sum_sub_distrib]
      calc
        |∑ q, (c q * X q - c q * Y q)| ≤
            ∑ q, |c q * X q - c q * Y q| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ q, |c q| * e q := by
          apply Finset.sum_le_sum
          intro q _
          rw [show c q * X q - c q * Y q = c q * (X q - Y q) by ring,
            abs_mul]
          exact mul_le_mul_of_nonneg_left (hE q) (abs_nonneg _)
  | depth + 1, c, X, Y, e, he0, hE => fun i j ↦
      higham23_biniExactDot_error h n depth c
        (fun q ↦ X q i j) (fun q ↦ Y q i j) e he0 (fun q ↦ hE q i j)

theorem higham23_biniError_mul (h : ℕ) :
    ∀ depth (A Ahat B Bhat : Higham23BiniMatrix h depth)
      (aHat b dx dy : ℝ),
      0 ≤ aHat → 0 ≤ b → 0 ≤ dx → 0 ≤ dy →
      Higham23BiniNormLe h depth Ahat aHat →
      Higham23BiniNormLe h depth B b →
      Higham23BiniErrorLe h depth Ahat A dx →
      Higham23BiniErrorLe h depth Bhat B dy →
      Higham23BiniErrorLe h depth
        (higham23BiniMul h depth Ahat Bhat) (higham23BiniMul h depth A B)
        (((h ^ depth : ℕ) : ℝ) * dx * b +
          ((h ^ depth : ℕ) : ℝ) * aHat * dy)
  | 0, A, Ahat, B, Bhat, aHat, b, dx, dy,
      haHat, hb, hdx, hdy, hAhat, hB, hAerr, hBerr => by
      change |Ahat * Bhat - A * B| ≤ _
      calc
        |Ahat * Bhat - A * B| = |(Ahat - A) * B + Ahat * (Bhat - B)| := by ring_nf
        _ ≤ |Ahat - A| * |B| + |Ahat| * |Bhat - B| := by
          simpa [abs_mul] using abs_add_le ((Ahat - A) * B) (Ahat * (Bhat - B))
        _ ≤ dx * b + aHat * dy := by
          exact add_le_add
            (mul_le_mul hAerr hB (abs_nonneg _) hdx)
            (mul_le_mul hAhat hBerr (abs_nonneg _) haHat)
        _ = _ := by norm_num
  | depth + 1, A, Ahat, B, Bhat, aHat, b, dx, dy,
      haHat, hb, hdx, hdy, hAhat, hB, hAerr, hBerr => by
      intro i j
      let er : ℝ := (((h ^ depth : ℕ) : ℝ) * dx * b +
        ((h ^ depth : ℕ) : ℝ) * aHat * dy)
      have hterm (k : Fin h) : Higham23BiniErrorLe h depth
          (higham23BiniMul h depth (Ahat i k) (Bhat k j))
          (higham23BiniMul h depth (A i k) (B k j)) er :=
        higham23_biniError_mul h depth (A i k) (Ahat i k) (B k j) (Bhat k j)
          aHat b dx dy haHat hb hdx hdy (hAhat i k) (hB k j)
          (hAerr i k) (hBerr k j)
      have hsum := higham23_biniExactDot_error h h depth
        (fun _ ↦ (1 : ℝ))
        (fun k ↦ higham23BiniMul h depth (Ahat i k) (Bhat k j))
        (fun k ↦ higham23BiniMul h depth (A i k) (B k j))
        (fun _ ↦ er) (fun _ ↦ by dsimp [er]; positivity) hterm
      convert hsum using 1 <;> dsimp [er] <;> simp [pow_succ] <;> push_cast <;> ring

structure Higham23BiniCertificate (h depth : ℕ)
    (X Xhat : Higham23BiniMatrix h depth) (error norm : ℝ) : Prop where
  error_le : Higham23BiniErrorLe h depth X Xhat error
  norm_le : Higham23BiniNormLe h depth Xhat norm

theorem higham23_biniCertificate_product (h depth : ℕ)
    (X Xhat Y Yhat P : Higham23BiniMatrix h depth)
    (yExact ex nx ey ny e : ℝ)
    (hyExact : 0 ≤ yExact) (hex : 0 ≤ ex) (hnx : 0 ≤ nx)
    (hey : 0 ≤ ey) (hny : 0 ≤ ny)
    (hYexact : Higham23BiniNormLe h depth Y yExact)
    (hX : Higham23BiniCertificate h depth X Xhat ex nx)
    (hY : Higham23BiniCertificate h depth Y Yhat ey ny)
    (hRec : Higham23BiniErrorLe h depth (higham23BiniMul h depth Xhat Yhat)
      P (e * nx * ny)) :
    let N : ℝ := ((h ^ depth : ℕ) : ℝ)
    Higham23BiniCertificate h depth (higham23BiniMul h depth X Y) P
      (N * ex * yExact + N * nx * ey + e * nx * ny)
      ((N + e) * nx * ny) := by
  dsimp only
  have hinputComputed := higham23_biniError_mul h depth
    X Xhat Y Yhat nx yExact ex ey hnx hyExact hex hey
    hX.norm_le hYexact
    (higham23_biniError_symm h depth _ _ hX.error_le)
    (higham23_biniError_symm h depth _ _ hY.error_le)
  have hinput := higham23_biniError_symm h depth _ _ hinputComputed
  have herr := higham23_biniError_trans h depth _ _ _ hinput hRec
  have hprod := higham23_biniNorm_mul h depth Xhat Yhat nx ny hnx hny
    hX.norm_le hY.norm_le
  have hout := higham23_biniNorm_of_error h depth _ _ hprod hRec
  constructor
  · exact higham23_biniError_mono h depth _ _ herr (by ring_nf; linarith)
  · convert hout using 1 <;> ring

end NumStability
