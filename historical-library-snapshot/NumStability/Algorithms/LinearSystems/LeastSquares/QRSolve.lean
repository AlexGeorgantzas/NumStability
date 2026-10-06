import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.QR.Householder.PanelApplication
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.FloatingPoint.Model

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-!
# QRSolve

Canonical reusable module extracted without change from LSQRSolve.
-/

/-- Concrete stored-Householder QR matrix sequence used by the Chapter 20,
    Theorem 20.3 stored-loop wrappers.

For `k < n`, step `k + 1` applies the rounded stored Householder panel update
with the signed `alpha` computed from the current active column.  After the QR
horizon the sequence is held fixed. -/
noncomputable def storedHouseholderQRMatrixSeq (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ) :
    ℕ → Fin m → Fin n → ℝ
  | 0 => A
  | k + 1 =>
      if hk : k < n then
        let Aprev := storedHouseholderQRMatrixSeq fp hmn A k
        let alpha :=
          signedHouseholderAlpha
            (Real.sqrt
              (householderTrailingNorm2Sq m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => Aprev a ⟨k, hk⟩)))
            (Aprev ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩)
        let v :=
          householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => Aprev a ⟨k, hk⟩) alpha
        let beta := householderBetaSpec m v
        fl_householderStoredPanelStep fp m n k v beta Aprev
      else
        storedHouseholderQRMatrixSeq fp hmn A k
/-- Signed Householder scalar chosen by the concrete stored-Householder QR
    matrix sequence. -/
noncomputable def storedHouseholderQRAlphaSeq (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ) (k : ℕ) : ℝ :=
  if hk : k < n then
    signedHouseholderAlpha
      (Real.sqrt
        (householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => storedHouseholderQRMatrixSeq fp hmn A k a ⟨k, hk⟩)))
      (storedHouseholderQRMatrixSeq fp hmn A k
        ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩)
  else
    0
/-- Concrete stored-Householder QR right-hand-side sequence paired with
    `storedHouseholderQRMatrixSeq`. -/
noncomputable def storedHouseholderQRRhsSeq (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    ℕ → Fin m → ℝ
  | 0 => b
  | k + 1 =>
      if hk : k < n then
        let Aprev := storedHouseholderQRMatrixSeq fp hmn A k
        let alpha := storedHouseholderQRAlphaSeq fp hmn A k
        let v :=
          householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => Aprev a ⟨k, hk⟩) alpha
        let beta := householderBetaSpec m v
        fl_householderStoredRhsStep fp m k v beta
          (storedHouseholderQRRhsSeq fp hmn A b k)
      else
        storedHouseholderQRRhsSeq fp hmn A b k
@[simp] theorem storedHouseholderQRMatrixSeq_zero (fp : FPModel)
    {m n : ℕ} (hmn : n ≤ m) (A : Fin m → Fin n → ℝ) :
    storedHouseholderQRMatrixSeq fp hmn A 0 = A := rfl
@[simp] theorem storedHouseholderQRRhsSeq_zero (fp : FPModel)
    {m n : ℕ} (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) :
    storedHouseholderQRRhsSeq fp hmn A b 0 = b := rfl
theorem storedHouseholderQRAlphaSeq_eq_signed (fp : FPModel)
    {m n : ℕ} (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (k : ℕ) (hk : k < n) :
    storedHouseholderQRAlphaSeq fp hmn A k =
      signedHouseholderAlpha
        (Real.sqrt
          (householderTrailingNorm2Sq m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => storedHouseholderQRMatrixSeq fp hmn A k a ⟨k, hk⟩)))
        (storedHouseholderQRMatrixSeq fp hmn A k
          ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩) := by
  simp [storedHouseholderQRAlphaSeq, hk]
theorem storedHouseholderQRMatrixSeq_succ_of_lt (fp : FPModel)
    {m n : ℕ} (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (k : ℕ) (hk : k < n) :
    storedHouseholderQRMatrixSeq fp hmn A (k + 1) =
      fl_householderStoredPanelStep fp m n k
        (householderTrailingActiveVector m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => storedHouseholderQRMatrixSeq fp hmn A k a ⟨k, hk⟩)
          (storedHouseholderQRAlphaSeq fp hmn A k))
        (householderBetaSpec m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => storedHouseholderQRMatrixSeq fp hmn A k a ⟨k, hk⟩)
            (storedHouseholderQRAlphaSeq fp hmn A k)))
        (storedHouseholderQRMatrixSeq fp hmn A k) := by
  simp [storedHouseholderQRMatrixSeq, storedHouseholderQRAlphaSeq, hk]
theorem storedHouseholderQRRhsSeq_succ_of_lt (fp : FPModel)
    {m n : ℕ} (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (k : ℕ) (hk : k < n) :
    storedHouseholderQRRhsSeq fp hmn A b (k + 1) =
      fl_householderStoredRhsStep fp m k
        (householderTrailingActiveVector m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => storedHouseholderQRMatrixSeq fp hmn A k a ⟨k, hk⟩)
          (storedHouseholderQRAlphaSeq fp hmn A k))
        (householderBetaSpec m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => storedHouseholderQRMatrixSeq fp hmn A k a ⟨k, hk⟩)
            (storedHouseholderQRAlphaSeq fp hmn A k)))
        (storedHouseholderQRRhsSeq fp hmn A b k) := by
  simp [storedHouseholderQRRhsSeq, storedHouseholderQRAlphaSeq, hk]

end NumStability
