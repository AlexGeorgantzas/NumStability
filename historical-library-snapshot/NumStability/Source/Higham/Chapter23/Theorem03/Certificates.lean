/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Source.Higham.Chapter23.Theorem02.ErrorRelations
import NumStability.Source.Higham.Chapter23.Theorem02.RecursiveMatrix

namespace NumStability

/-!
# Higham Chapter 23, Theorem 23.3: recursive error certificates

This module packages simultaneous recursive error and computed-norm bounds
and proves their preservation by rounded addition, subtraction, and recursive
products for the Winograd-Strassen analysis.
-/

/-- A simultaneously certified error radius and computed max-entry norm. -/
structure Higham23RecursiveCertificate (r depth : ℕ)
    (X Xhat : Higham23RecursiveMatrix r depth) (error norm : ℝ) : Prop where
  error_le : Higham23RecursiveErrorLe r depth X Xhat error
  norm_le : Higham23RecursiveMaxNormLe r depth Xhat norm

theorem higham23_recursiveCertificate_refl (r depth : ℕ)
    (X : Higham23RecursiveMatrix r depth) (x : ℝ)
    (hX : Higham23RecursiveMaxNormLe r depth X x) :
    Higham23RecursiveCertificate r depth X X 0 x :=
  ⟨higham23_recursiveErrorLe_refl r depth X, hX⟩

/-- Certificate composition for one rounded addition. -/
theorem higham23_recursiveCertificate_flAdd
    (fp : FPModel) (r depth : ℕ)
    (X Xhat Y Yhat : Higham23RecursiveMatrix r depth)
    (ex nx ey ny : ℝ)
    (hnx : 0 ≤ nx) (hny : 0 ≤ ny)
    (hX : Higham23RecursiveCertificate r depth X Xhat ex nx)
    (hY : Higham23RecursiveCertificate r depth Y Yhat ey ny) :
    Higham23RecursiveCertificate r depth (X + Y)
      (higham23RecursiveFlAdd fp r depth Xhat Yhat)
      (ex + ey + fp.u * (nx + ny)) ((1 + fp.u) * (nx + ny)) := by
  have hlocal := higham23_recursiveFlAdd_error fp r depth
    Xhat Yhat nx ny hnx hny hX.norm_le hY.norm_le
  have hinput := higham23_recursiveErrorLe_add r depth
    X Xhat Y Yhat hX.error_le hY.error_le
  refine ⟨?_, higham23_recursiveFlAdd_norm fp r depth
    Xhat Yhat nx ny hnx hny hX.norm_le hY.norm_le⟩
  have h := higham23_recursiveErrorLe_trans r depth _ _ _ hinput hlocal
  exact higham23_recursiveErrorLe_mono r depth _ _ h (by ring_nf; linarith)

/-- Certificate composition for one rounded subtraction. -/
theorem higham23_recursiveCertificate_flSub
    (fp : FPModel) (r depth : ℕ)
    (X Xhat Y Yhat : Higham23RecursiveMatrix r depth)
    (ex nx ey ny : ℝ)
    (hnx : 0 ≤ nx) (hny : 0 ≤ ny)
    (hX : Higham23RecursiveCertificate r depth X Xhat ex nx)
    (hY : Higham23RecursiveCertificate r depth Y Yhat ey ny) :
    Higham23RecursiveCertificate r depth (X - Y)
      (higham23RecursiveFlSub fp r depth Xhat Yhat)
      (ex + ey + fp.u * (nx + ny)) ((1 + fp.u) * (nx + ny)) := by
  have hlocal := higham23_recursiveFlSub_error fp r depth
    Xhat Yhat nx ny hnx hny hX.norm_le hY.norm_le
  have hinput := higham23_recursiveErrorLe_sub r depth
    X Xhat Y Yhat hX.error_le hY.error_le
  refine ⟨?_, higham23_recursiveFlSub_norm fp r depth
    Xhat Yhat nx ny hnx hny hX.norm_le hY.norm_le⟩
  have h := higham23_recursiveErrorLe_trans r depth _ _ _ hinput hlocal
  exact higham23_recursiveErrorLe_mono r depth _ _ h (by ring_nf; linarith)

/-- Feed two prepared-input certificates through a recursively rounded
product whose normalized recursive error coefficient is `e`. -/
theorem higham23_recursiveCertificate_product
    (r depth : ℕ)
    (X Xhat Y Yhat P : Higham23RecursiveMatrix r depth)
    (xExact yExact ex nx ey ny e : ℝ)
    (hxExact : 0 ≤ xExact) (hyExact : 0 ≤ yExact)
    (hex : 0 ≤ ex) (hnx : 0 ≤ nx) (hey : 0 ≤ ey) (hny : 0 ≤ ny)
    (he : 0 ≤ e)
    (hXexact : Higham23RecursiveMaxNormLe r depth X xExact)
    (hYexact : Higham23RecursiveMaxNormLe r depth Y yExact)
    (hX : Higham23RecursiveCertificate r depth X Xhat ex nx)
    (hY : Higham23RecursiveCertificate r depth Y Yhat ey ny)
    (hRec : Higham23RecursiveErrorLe r depth (Xhat * Yhat) P
      (e * nx * ny)) :
    let m : ℝ := (2 ^ (r + depth) : ℕ)
    Higham23RecursiveCertificate r depth (X * Y) P
      (m * ex * yExact + m * nx * ey + e * nx * ny)
      ((m + e) * nx * ny) := by
  dsimp only
  let m : ℝ := (2 ^ (r + depth) : ℕ)
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have hinputComputed := higham23_recursiveErrorLe_mul r depth
    X Xhat Y Yhat nx yExact ex ey hnx hyExact hex hey
    hX.norm_le hYexact
    (higham23_recursiveErrorLe_symm r depth _ _ hX.error_le)
    (higham23_recursiveErrorLe_symm r depth _ _ hY.error_le)
  have hinput := higham23_recursiveErrorLe_symm r depth _ _ hinputComputed
  have herrRaw := higham23_recursiveErrorLe_trans r depth _ _ _ hinput hRec
  have hprodNorm := higham23_recursiveMaxNormLe_mul r depth
    Xhat Yhat nx ny hnx hny hX.norm_le hY.norm_le
  have houtNorm := higham23_recursiveMaxNormLe_of_error r depth
    (Xhat * Yhat) P hprodNorm hRec
  constructor
  · exact higham23_recursiveErrorLe_mono r depth _ _ herrRaw (by
      ring_nf
      linarith)
  · convert houtNorm using 1 <;> dsimp [m] <;> ring

end NumStability
