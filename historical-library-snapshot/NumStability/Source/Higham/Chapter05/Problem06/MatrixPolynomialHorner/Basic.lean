import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.PolynomialEvaluation.MatrixNorms
import NumStability.Analysis.FloatingPointArithmetic.IeeeSpecialValueOperations.Results
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter05.Equation14.MatrixPolynomialForms.Basic
import NumStability.Source.Higham.Chapter05.Section01.Horner.Basic

/-!
# Chapter05 Problem06 MatrixPolynomialHorner Basic

Canonical destination for material split out of
`NumStability.Algorithms.Horner` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- One exact matrix Horner step for `P₁`; a scalar coefficient is inserted
as the scalar matrix `aI`. -/
noncomputable def complexMatrixHornerP1Step (n : ℕ)
    (X Y : Matrix (Fin n) (Fin n) ℂ) (a : ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Y * X + a • (1 : Matrix (Fin n) (Fin n) ℂ)

/-- Exact Horner evaluator for the `P₁` form in (5.14). -/
noncomputable def complexMatrixHornerP1Desc (n : ℕ)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    List ℂ → Matrix (Fin n) (Fin n) ℂ
  | [] => 0
  | a :: rest =>
      rest.foldl (complexMatrixHornerP1Step n X)
        (a • (1 : Matrix (Fin n) (Fin n) ℂ))

lemma complexMatrixHornerP1Fold_eq_acc_mul_pow_add_poly
    (n : ℕ) (X : Matrix (Fin n) (Fin n) ℂ) :
    ∀ (rest : List ℂ) (Y : Matrix (Fin n) (Fin n) ℂ),
      rest.foldl (complexMatrixHornerP1Step n X) Y =
        Y * X ^ rest.length + complexMatrixPolyP1Desc n X rest := by
  intro rest
  induction rest with
  | nil =>
      intro Y
      simp [complexMatrixPolyP1Desc]
  | cons a rest ih =>
      intro Y
      rw [List.foldl, ih]
      simp only [complexMatrixPolyP1Desc, List.length_cons]
      rw [pow_succ']
      simp [complexMatrixHornerP1Step, add_mul, mul_assoc]
      ac_rfl

/-- Exact Horner evaluation realizes the full complex `P₁` expression in
(5.14). -/
theorem complexMatrixHornerP1Desc_eq_complexMatrixPolyP1Desc
    (n : ℕ) (X : Matrix (Fin n) (Fin n) ℂ) (coeffsDesc : List ℂ) :
    complexMatrixHornerP1Desc n X coeffsDesc =
      complexMatrixPolyP1Desc n X coeffsDesc := by
  cases coeffsDesc with
  | nil => rfl
  | cons a rest =>
      simpa [complexMatrixHornerP1Desc, complexMatrixPolyP1Desc]
        using complexMatrixHornerP1Fold_eq_acc_mul_pow_add_poly
          n X rest (a • (1 : Matrix (Fin n) (Fin n) ℂ))

/-- One exact Horner step for the scalar-argument/matrix-coefficient `P₂`
form in (5.14). -/
noncomputable def complexMatrixHornerP2Step (n : ℕ) (α : ℂ)
    (Y A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  α • Y + A

/-- Exact Horner evaluator for the `P₂` form in (5.14). -/
noncomputable def complexMatrixHornerP2Desc (n : ℕ) (α : ℂ) :
    List (Matrix (Fin n) (Fin n) ℂ) → Matrix (Fin n) (Fin n) ℂ
  | [] => 0
  | A :: rest => rest.foldl (complexMatrixHornerP2Step n α) A

lemma complexMatrixHornerP2Fold_eq_pow_smul_acc_add_poly
    (n : ℕ) (α : ℂ) :
    ∀ (rest : List (Matrix (Fin n) (Fin n) ℂ))
      (Y : Matrix (Fin n) (Fin n) ℂ),
      rest.foldl (complexMatrixHornerP2Step n α) Y =
        (α ^ rest.length) • Y + complexMatrixPolyP2Desc n α rest := by
  intro rest
  induction rest with
  | nil =>
      intro Y
      simp [complexMatrixPolyP2Desc]
  | cons A rest ih =>
      intro Y
      rw [List.foldl, ih]
      simp only [complexMatrixPolyP2Desc, List.length_cons]
      rw [pow_succ']
      ext i j
      simp [complexMatrixHornerP2Step]
      ring

/-- Exact Horner evaluation realizes the full complex `P₂` expression in
(5.14). -/
theorem complexMatrixHornerP2Desc_eq_complexMatrixPolyP2Desc
    (n : ℕ) (α : ℂ)
    (coeffsDesc : List (Matrix (Fin n) (Fin n) ℂ)) :
    complexMatrixHornerP2Desc n α coeffsDesc =
      complexMatrixPolyP2Desc n α coeffsDesc := by
  cases coeffsDesc with
  | nil => rfl
  | cons A rest =>
      simpa [complexMatrixHornerP2Desc, complexMatrixPolyP2Desc]
        using complexMatrixHornerP2Fold_eq_pow_smul_acc_add_poly
          n α rest A

/-- Exact complex matrix Horner evaluator for `P₃` in (5.14). -/
noncomputable def complexMatrixHornerP3Desc (n : ℕ)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    List (Matrix (Fin n) (Fin n) ℂ) → Matrix (Fin n) (Fin n) ℂ
  | [] => 0
  | A :: rest => rest.foldl (fun Y B => Y * X + B) A

lemma complexMatrixHornerP3Fold_eq_acc_mul_pow_add_poly
    (n : ℕ) (X : Matrix (Fin n) (Fin n) ℂ) :
    ∀ (rest : List (Matrix (Fin n) (Fin n) ℂ))
      (Y : Matrix (Fin n) (Fin n) ℂ),
      rest.foldl (fun Z B => Z * X + B) Y =
        Y * X ^ rest.length + complexMatrixPolyP3Desc n X rest := by
  intro rest
  induction rest with
  | nil =>
      intro Y
      simp [complexMatrixPolyP3Desc]
  | cons A rest ih =>
      intro Y
      rw [List.foldl, ih]
      simp only [complexMatrixPolyP3Desc, List.length_cons]
      rw [pow_succ']
      simp [add_mul, mul_assoc]
      abel

/-- Exact Horner evaluation realizes the full complex `P₃` expression in
(5.14), completing the three displayed complex forms. -/
theorem complexMatrixHornerP3Desc_eq_complexMatrixPolyP3Desc
    (n : ℕ) (X : Matrix (Fin n) (Fin n) ℂ)
    (coeffsDesc : List (Matrix (Fin n) (Fin n) ℂ)) :
    complexMatrixHornerP3Desc n X coeffsDesc =
      complexMatrixPolyP3Desc n X coeffsDesc := by
  cases coeffsDesc with
  | nil => rfl
  | cons A rest =>
      simpa [complexMatrixHornerP3Desc, complexMatrixPolyP3Desc]
        using complexMatrixHornerP3Fold_eq_acc_mul_pow_add_poly
          n X rest A

/-- One exact Horner step for the matrix polynomial `P3` in (5.14), with
matrix coefficients on the left of powers of `X`. -/
noncomputable def matrixHornerP3Step (n : ℕ)
    (X Y A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  matAdd n (matMul n Y X) A

/-- Exact Horner evaluation of `P3` from descending matrix coefficients
`[A_n, ..., A_0]`. -/
noncomputable def matrixHornerP3Desc (n : ℕ)
    (X : Fin n → Fin n → ℝ) :
    List (Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ
  | [] => zeroMatrix n
  | A :: rest => rest.foldl (matrixHornerP3Step n X) A

lemma matrixHornerP3Fold_eq_acc_mul_pow_add_polyDesc
    (n : ℕ) (X : Fin n → Fin n → ℝ) :
    ∀ (rest : List (Fin n → Fin n → ℝ)) (Y : Fin n → Fin n → ℝ),
      rest.foldl (matrixHornerP3Step n X) Y =
        matAdd n (matMul n Y (matPow n X rest.length))
          (matrixPolyP3Desc n X rest) := by
  intro rest
  induction rest with
  | nil =>
      intro Y
      ext i j
      simp [matrixPolyP3Desc, matAdd, zeroMatrix,
        matPow_zero, matMul_id_right]
  | cons A rest ih =>
      intro Y
      have hmul :
          matMul n (matrixHornerP3Step n X Y A)
              (matPow n X rest.length) =
            fun i j =>
              matMul n Y (matPow n X (rest.length + 1)) i j +
                matMul n A (matPow n X rest.length) i j := by
        calc
          matMul n (matrixHornerP3Step n X Y A)
              (matPow n X rest.length)
              =
            matMul n (fun i j => matMul n Y X i j + A i j)
              (matPow n X rest.length) := rfl
          _ =
            fun i j =>
              matMul n (matMul n Y X) (matPow n X rest.length) i j +
                matMul n A (matPow n X rest.length) i j :=
              matMul_add_left n (matMul n Y X) A (matPow n X rest.length)
          _ =
            fun i j =>
              matMul n Y (matPow n X (rest.length + 1)) i j +
                matMul n A (matPow n X rest.length) i j := by
              have hassoc :
                  matMul n (matMul n Y X) (matPow n X rest.length) =
                    matMul n Y (matPow n X (rest.length + 1)) := by
                rw [matMul_assoc]
                rfl
              rw [hassoc]
      rw [List.foldl, ih]
      ext i j
      simp [matrixPolyP3Desc, matrixHornerP3Step, matAdd] at hmul ⊢
      rw [congrFun (congrFun hmul i) j]
      ring

/-- Exact matrix Horner evaluation equals the displayed matrix polynomial
`P3(X) = A_0 + A_1 X + ... + A_n X^n` from (5.14), for descending
coefficient lists. -/
theorem matrixHornerP3Desc_eq_matrixPolyP3Desc
    (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ)) :
    matrixHornerP3Desc n X coeffsDesc =
      matrixPolyP3Desc n X coeffsDesc := by
  cases coeffsDesc with
  | nil =>
      rfl
  | cons A rest =>
      have h :=
        matrixHornerP3Fold_eq_acc_mul_pow_add_polyDesc n X rest A
      ext i j
      simpa [matrixHornerP3Desc, matrixPolyP3Desc, matAdd] using
        congrFun (congrFun h i) j

theorem matrixHornerP3Fold_infNorm_le_acc_majorant
    (n : ℕ) (X Y : Fin n → Fin n → ℝ)
    (rest : List (Fin n → Fin n → ℝ))
    (hnpos : 0 < n) :
    infNorm (rest.foldl (matrixHornerP3Step n X) Y) ≤
      infNorm Y * infNorm X ^ rest.length +
        matrixPolyP3InfNormMajorant n X rest := by
  rw [matrixHornerP3Fold_eq_acc_mul_pow_add_polyDesc n X rest Y]
  let term : Fin n → Fin n → ℝ := matMul n Y (matPow n X rest.length)
  let tail : Fin n → Fin n → ℝ := matrixPolyP3Desc n X rest
  have hadd :
      infNorm (matAdd n term tail) ≤ infNorm term + infNorm tail := by
    simpa [matAdd] using infNorm_add_le term tail
  have hmul :
      infNorm term ≤ infNorm Y * infNorm (matPow n X rest.length) := by
    simpa [term] using
      infNorm_matMul_le hnpos Y (matPow n X rest.length)
  have hpow :
      infNorm (matPow n X rest.length) ≤ infNorm X ^ rest.length :=
    infNorm_matPow_le hnpos X rest.length
  have hterm :
      infNorm term ≤ infNorm Y * infNorm X ^ rest.length :=
    le_trans hmul
      (mul_le_mul_of_nonneg_left hpow (infNorm_nonneg Y))
  have htail :
      infNorm tail ≤ matrixPolyP3InfNormMajorant n X rest := by
    simpa [tail] using matrixPolyP3Desc_infNorm_le_majorant n X rest hnpos
  calc
    infNorm (matAdd n term tail)
        ≤ infNorm term + infNorm tail := hadd
    _ ≤ infNorm Y * infNorm X ^ rest.length +
          matrixPolyP3InfNormMajorant n X rest :=
        add_le_add hterm htail

theorem matrixHornerP3Fold_oneNorm_le_acc_majorant
    (n : ℕ) (X Y : Fin n → Fin n → ℝ)
    (rest : List (Fin n → Fin n → ℝ)) :
    oneNorm (rest.foldl (matrixHornerP3Step n X) Y) ≤
      oneNorm Y * oneNorm X ^ rest.length +
        matrixPolyP3OneNormMajorant n X rest := by
  rw [matrixHornerP3Fold_eq_acc_mul_pow_add_polyDesc n X rest Y]
  let term : Fin n → Fin n → ℝ := matMul n Y (matPow n X rest.length)
  let tail : Fin n → Fin n → ℝ := matrixPolyP3Desc n X rest
  have hadd :
      oneNorm (matAdd n term tail) ≤ oneNorm term + oneNorm tail := by
    simpa [matAdd] using oneNorm_add_le term tail
  have hmul :
      oneNorm term ≤ oneNorm Y * oneNorm (matPow n X rest.length) := by
    simpa [term] using
      oneNorm_matMul_le Y (matPow n X rest.length)
  have hpow :
      oneNorm (matPow n X rest.length) ≤ oneNorm X ^ rest.length :=
    oneNorm_matPow_le X rest.length
  have hterm :
      oneNorm term ≤ oneNorm Y * oneNorm X ^ rest.length :=
    le_trans hmul
      (mul_le_mul_of_nonneg_left hpow (oneNorm_nonneg Y))
  have htail :
      oneNorm tail ≤ matrixPolyP3OneNormMajorant n X rest := by
    simpa [tail] using matrixPolyP3Desc_oneNorm_le_majorant n X rest
  calc
    oneNorm (matAdd n term tail)
        ≤ oneNorm term + oneNorm tail := hadd
    _ ≤ oneNorm Y * oneNorm X ^ rest.length +
          matrixPolyP3OneNormMajorant n X rest :=
        add_le_add hterm htail

/-- One rounded matrix-Horner step for `P3`: first form the rounded matrix
product `fl(YX)`, then round the entrywise addition with `A`. -/
noncomputable def fl_matrixHornerP3Step
    (fp : FPModel) (n : ℕ)
    (X Y A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fl_matAdd fp n (fl_matMul fp n n n Y X) A

/-- Rounded matrix-Horner evaluation of `P3` from descending matrix
coefficients `[A_n, ..., A_0]`. -/
noncomputable def fl_matrixHornerP3Desc
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ) :
    List (Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ
  | [] => zeroMatrix n
  | A :: rest => rest.foldl (fl_matrixHornerP3Step fp n X) A

/-- Local infinity-norm budget for one rounded matrix-Horner step. -/
noncomputable def matrixHornerP3StepInfErrorBudget
    (fp : FPModel) (n : ℕ)
    (X Y A : Fin n → Fin n → ℝ) : ℝ :=
  fp.u * infNorm (matAdd n (fl_matMul fp n n n Y X) A) +
    gamma fp n * infNorm Y * infNorm X

/-- Local one-norm budget for one rounded matrix-Horner step. -/
noncomputable def matrixHornerP3StepOneNormErrorBudget
    (fp : FPModel) (n : ℕ)
    (X Y A : Fin n → Fin n → ℝ) : ℝ :=
  fp.u * oneNorm (matAdd n (fl_matMul fp n n n Y X) A) +
    gamma fp n * oneNorm Y * oneNorm X

theorem fl_matrixHornerP3Step_infNorm_error_bound
    (fp : FPModel) (n : ℕ)
    (X Y A : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n) :
    infNorm
        (fun i j =>
          fl_matrixHornerP3Step fp n X Y A i j -
            matrixHornerP3Step n X Y A i j) ≤
      matrixHornerP3StepInfErrorBudget fp n X Y A := by
  let Bhat : Fin n → Fin n → ℝ := fl_matMul fp n n n Y X
  let B : Fin n → Fin n → ℝ := matMul n Y X
  let Eadd : Fin n → Fin n → ℝ :=
    fun i j => fl_matAdd fp n Bhat A i j - matAdd n Bhat A i j
  let Emul : Fin n → Fin n → ℝ := fun i j => Bhat i j - B i j
  have hdecomp :
      (fun i j =>
          fl_matrixHornerP3Step fp n X Y A i j -
            matrixHornerP3Step n X Y A i j) =
        fun i j => Eadd i j + Emul i j := by
    ext i j
    simp [fl_matrixHornerP3Step, matrixHornerP3Step,
      fl_matAdd, matAdd, Eadd, Emul, Bhat, B]
    ring
  rw [hdecomp]
  have hAdd :
      infNorm Eadd ≤ fp.u * infNorm (matAdd n Bhat A) := by
    simpa [Eadd] using fl_matAdd_infNorm_error_bound fp n Bhat A
  have hMul :
      infNorm Emul ≤ gamma fp n * infNorm Y * infNorm X := by
    simpa [Emul, Bhat, B] using
      fl_matMul_infNorm_error_bound fp n Y X hn
  calc
    infNorm (fun i j => Eadd i j + Emul i j)
        ≤ infNorm Eadd + infNorm Emul := infNorm_add_le Eadd Emul
    _ ≤ fp.u * infNorm (matAdd n Bhat A) +
          gamma fp n * infNorm Y * infNorm X :=
        add_le_add hAdd hMul
    _ = matrixHornerP3StepInfErrorBudget fp n X Y A := rfl

theorem fl_matrixHornerP3Step_oneNorm_error_bound
    (fp : FPModel) (n : ℕ)
    (X Y A : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n) :
    oneNorm
        (fun i j =>
          fl_matrixHornerP3Step fp n X Y A i j -
            matrixHornerP3Step n X Y A i j) ≤
      matrixHornerP3StepOneNormErrorBudget fp n X Y A := by
  let Bhat : Fin n → Fin n → ℝ := fl_matMul fp n n n Y X
  let B : Fin n → Fin n → ℝ := matMul n Y X
  let Eadd : Fin n → Fin n → ℝ :=
    fun i j => fl_matAdd fp n Bhat A i j - matAdd n Bhat A i j
  let Emul : Fin n → Fin n → ℝ := fun i j => Bhat i j - B i j
  have hdecomp :
      (fun i j =>
          fl_matrixHornerP3Step fp n X Y A i j -
            matrixHornerP3Step n X Y A i j) =
        fun i j => Eadd i j + Emul i j := by
    ext i j
    simp [fl_matrixHornerP3Step, matrixHornerP3Step,
      fl_matAdd, matAdd, Eadd, Emul, Bhat, B]
    ring
  rw [hdecomp]
  have hAdd :
      oneNorm Eadd ≤ fp.u * oneNorm (matAdd n Bhat A) := by
    simpa [Eadd] using fl_matAdd_oneNorm_error_bound fp n Bhat A
  have hMul :
      oneNorm Emul ≤ gamma fp n * oneNorm Y * oneNorm X := by
    simpa [Emul, Bhat, B] using
      fl_matMul_oneNorm_error_bound fp n Y X hn
  calc
    oneNorm (fun i j => Eadd i j + Emul i j)
        ≤ oneNorm Eadd + oneNorm Emul := oneNorm_add_le Eadd Emul
    _ ≤ fp.u * oneNorm (matAdd n Bhat A) +
          gamma fp n * oneNorm Y * oneNorm X :=
        add_le_add hAdd hMul
    _ = matrixHornerP3StepOneNormErrorBudget fp n X Y A := rfl

theorem matrixHornerP3StepInfErrorBudget_le_acc_majorant
    (fp : FPModel) (n : ℕ)
    (X Yhat A : Fin n → Fin n → ℝ) (eta mu : ℝ)
    (hnpos : 0 < n) (hn : gammaValid fp n)
    (hYhat : infNorm Yhat ≤ eta + mu) :
    matrixHornerP3StepInfErrorBudget fp n X Yhat A ≤
      fp.u * ((1 + gamma fp n) * (eta + mu) * infNorm X +
          infNorm A) +
        gamma fp n * (eta + mu) * infNorm X := by
  let Bhat : Fin n → Fin n → ℝ := fl_matMul fp n n n Yhat X
  let B : Fin n → Fin n → ℝ := matMul n Yhat X
  have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have hX : 0 ≤ infNorm X := infNorm_nonneg X
  have hY : 0 ≤ infNorm Yhat := infNorm_nonneg Yhat
  have hsrc_nonneg : 0 ≤ eta + mu := le_trans hY hYhat
  have hBhat :
      infNorm Bhat ≤ (1 + gamma fp n) * infNorm Yhat * infNorm X := by
    have htri := infNorm_le_sub_add Bhat B
    have herr :
        infNorm (fun i j => Bhat i j - B i j) ≤
          gamma fp n * infNorm Yhat * infNorm X := by
      simpa [Bhat, B] using
        fl_matMul_infNorm_error_bound fp n Yhat X hn
    have hmul :
        infNorm B ≤ infNorm Yhat * infNorm X := by
      simpa [B] using infNorm_matMul_le hnpos Yhat X
    calc
      infNorm Bhat
          ≤ infNorm (fun i j => Bhat i j - B i j) + infNorm B := htri
      _ ≤ gamma fp n * infNorm Yhat * infNorm X +
            infNorm Yhat * infNorm X := add_le_add herr hmul
      _ = (1 + gamma fp n) * infNorm Yhat * infNorm X := by
          ring
  have hadd :
      infNorm (matAdd n Bhat A) ≤
        (1 + gamma fp n) * infNorm Yhat * infNorm X + infNorm A := by
    calc
      infNorm (matAdd n Bhat A)
          ≤ infNorm Bhat + infNorm A := by
            simpa [matAdd] using infNorm_add_le Bhat A
      _ ≤ (1 + gamma fp n) * infNorm Yhat * infNorm X +
            infNorm A := add_le_add hBhat le_rfl
  have hfactor₁ : 0 ≤ (1 + gamma fp n) * infNorm X :=
    mul_nonneg (by linarith) hX
  have hYterm :
      (1 + gamma fp n) * infNorm Yhat * infNorm X ≤
        (1 + gamma fp n) * (eta + mu) * infNorm X := by
    calc
      (1 + gamma fp n) * infNorm Yhat * infNorm X
          = ((1 + gamma fp n) * infNorm X) * infNorm Yhat := by
            ring
      _ ≤ ((1 + gamma fp n) * infNorm X) * (eta + mu) :=
            mul_le_mul_of_nonneg_left hYhat hfactor₁
      _ = (1 + gamma fp n) * (eta + mu) * infNorm X := by
            ring
  have hadd_source :
      infNorm (matAdd n Bhat A) ≤
        (1 + gamma fp n) * (eta + mu) * infNorm X + infNorm A :=
    le_trans hadd (add_le_add hYterm le_rfl)
  have hfactor₂ : 0 ≤ gamma fp n * infNorm X :=
    mul_nonneg hγ hX
  have hγterm :
      gamma fp n * infNorm Yhat * infNorm X ≤
        gamma fp n * (eta + mu) * infNorm X := by
    calc
      gamma fp n * infNorm Yhat * infNorm X
          = (gamma fp n * infNorm X) * infNorm Yhat := by
            ring
      _ ≤ (gamma fp n * infNorm X) * (eta + mu) :=
            mul_le_mul_of_nonneg_left hYhat hfactor₂
      _ = gamma fp n * (eta + mu) * infNorm X := by
            ring
  unfold matrixHornerP3StepInfErrorBudget
  exact add_le_add
    (mul_le_mul_of_nonneg_left hadd_source fp.u_nonneg)
    hγterm

theorem matrixHornerP3StepOneNormErrorBudget_le_acc_majorant
    (fp : FPModel) (n : ℕ)
    (X Yhat A : Fin n → Fin n → ℝ) (eta mu : ℝ)
    (hn : gammaValid fp n)
    (hYhat : oneNorm Yhat ≤ eta + mu) :
    matrixHornerP3StepOneNormErrorBudget fp n X Yhat A ≤
      fp.u * ((1 + gamma fp n) * (eta + mu) * oneNorm X +
          oneNorm A) +
        gamma fp n * (eta + mu) * oneNorm X := by
  let Bhat : Fin n → Fin n → ℝ := fl_matMul fp n n n Yhat X
  let B : Fin n → Fin n → ℝ := matMul n Yhat X
  have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have hX : 0 ≤ oneNorm X := oneNorm_nonneg X
  have hY : 0 ≤ oneNorm Yhat := oneNorm_nonneg Yhat
  have hsrc_nonneg : 0 ≤ eta + mu := le_trans hY hYhat
  have hBhat :
      oneNorm Bhat ≤ (1 + gamma fp n) * oneNorm Yhat * oneNorm X := by
    have htri := oneNorm_le_sub_add Bhat B
    have herr :
        oneNorm (fun i j => Bhat i j - B i j) ≤
          gamma fp n * oneNorm Yhat * oneNorm X := by
      simpa [Bhat, B] using
        fl_matMul_oneNorm_error_bound fp n Yhat X hn
    have hmul :
        oneNorm B ≤ oneNorm Yhat * oneNorm X := by
      simpa [B] using oneNorm_matMul_le Yhat X
    calc
      oneNorm Bhat
          ≤ oneNorm (fun i j => Bhat i j - B i j) + oneNorm B := htri
      _ ≤ gamma fp n * oneNorm Yhat * oneNorm X +
            oneNorm Yhat * oneNorm X := add_le_add herr hmul
      _ = (1 + gamma fp n) * oneNorm Yhat * oneNorm X := by
          ring
  have hadd :
      oneNorm (matAdd n Bhat A) ≤
        (1 + gamma fp n) * oneNorm Yhat * oneNorm X + oneNorm A := by
    calc
      oneNorm (matAdd n Bhat A)
          ≤ oneNorm Bhat + oneNorm A := by
            simpa [matAdd] using oneNorm_add_le Bhat A
      _ ≤ (1 + gamma fp n) * oneNorm Yhat * oneNorm X +
            oneNorm A := add_le_add hBhat le_rfl
  have hfactor₁ : 0 ≤ (1 + gamma fp n) * oneNorm X :=
    mul_nonneg (by linarith) hX
  have hYterm :
      (1 + gamma fp n) * oneNorm Yhat * oneNorm X ≤
        (1 + gamma fp n) * (eta + mu) * oneNorm X := by
    calc
      (1 + gamma fp n) * oneNorm Yhat * oneNorm X
          = ((1 + gamma fp n) * oneNorm X) * oneNorm Yhat := by
            ring
      _ ≤ ((1 + gamma fp n) * oneNorm X) * (eta + mu) :=
            mul_le_mul_of_nonneg_left hYhat hfactor₁
      _ = (1 + gamma fp n) * (eta + mu) * oneNorm X := by
            ring
  have hadd_source :
      oneNorm (matAdd n Bhat A) ≤
        (1 + gamma fp n) * (eta + mu) * oneNorm X + oneNorm A :=
    le_trans hadd (add_le_add hYterm le_rfl)
  have hfactor₂ : 0 ≤ gamma fp n * oneNorm X :=
    mul_nonneg hγ hX
  have hγterm :
      gamma fp n * oneNorm Yhat * oneNorm X ≤
        gamma fp n * (eta + mu) * oneNorm X := by
    calc
      gamma fp n * oneNorm Yhat * oneNorm X
          = (gamma fp n * oneNorm X) * oneNorm Yhat := by
            ring
      _ ≤ (gamma fp n * oneNorm X) * (eta + mu) :=
            mul_le_mul_of_nonneg_left hYhat hfactor₂
      _ = gamma fp n * (eta + mu) * oneNorm X := by
            ring
  unfold matrixHornerP3StepOneNormErrorBudget
  exact add_le_add
    (mul_le_mul_of_nonneg_left hadd_source fp.u_nonneg)
    hγterm

lemma matrixHornerP3Step_infNorm_lipschitz
    (n : ℕ) (hn : 0 < n)
    (X Y Z A : Fin n → Fin n → ℝ) :
    infNorm
        (fun i j =>
          matrixHornerP3Step n X Y A i j -
            matrixHornerP3Step n X Z A i j) ≤
      infNorm (fun i j => Y i j - Z i j) * infNorm X := by
  have hmat :
      (fun i j =>
          matrixHornerP3Step n X Y A i j -
            matrixHornerP3Step n X Z A i j) =
        matMul n (fun i j => Y i j - Z i j) X := by
    ext i j
    simp [matrixHornerP3Step, matAdd, matMul]
    calc
      (∑ k : Fin n, Y i k * X k j) - ∑ k : Fin n, Z i k * X k j
          = ∑ k : Fin n, (Y i k * X k j - Z i k * X k j) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ k : Fin n, (Y i k - Z i k) * X k j := by
            apply Finset.sum_congr rfl
            intro k _
            ring
  rw [hmat]
  exact infNorm_matMul_le hn (fun i j => Y i j - Z i j) X

lemma matrixHornerP3Step_oneNorm_lipschitz
    (n : ℕ)
    (X Y Z A : Fin n → Fin n → ℝ) :
    oneNorm
        (fun i j =>
          matrixHornerP3Step n X Y A i j -
            matrixHornerP3Step n X Z A i j) ≤
      oneNorm (fun i j => Y i j - Z i j) * oneNorm X := by
  have hmat :
      (fun i j =>
          matrixHornerP3Step n X Y A i j -
            matrixHornerP3Step n X Z A i j) =
        matMul n (fun i j => Y i j - Z i j) X := by
    ext i j
    simp [matrixHornerP3Step, matAdd, matMul]
    calc
      (∑ k : Fin n, Y i k * X k j) - ∑ k : Fin n, Z i k * X k j
          = ∑ k : Fin n, (Y i k * X k j - Z i k * X k j) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ k : Fin n, (Y i k - Z i k) * X k j := by
            apply Finset.sum_congr rfl
            intro k _
            ring
  rw [hmat]
  exact oneNorm_matMul_le (fun i j => Y i j - Z i j) X

/-- Recursive finite infinity-norm budget for a rounded matrix-Horner fold from
an already computed accumulator with current error budget `mu`. -/
noncomputable def matrixHornerP3ForwardInfErrorBudgetFrom
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ) :
    (Fin n → Fin n → ℝ) → ℝ →
      List (Fin n → Fin n → ℝ) → ℝ
  | _Yhat, mu, [] => mu
  | Yhat, mu, A :: rest =>
      let mu' :=
        matrixHornerP3StepInfErrorBudget fp n X Yhat A +
          mu * infNorm X
      matrixHornerP3ForwardInfErrorBudgetFrom fp n X
        (fl_matrixHornerP3Step fp n X Yhat A) mu' rest

/-- Top-level recursive finite infinity-norm budget for rounded matrix Horner.
The leading coefficient is used as the initial accumulator, so the initial
storage error is zero. -/
noncomputable def matrixHornerP3ForwardInfErrorBudget
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ) :
    List (Fin n → Fin n → ℝ) → ℝ
  | [] => 0
  | A :: rest =>
      matrixHornerP3ForwardInfErrorBudgetFrom fp n X A 0 rest

/-- Recursive finite one-norm budget for a rounded matrix-Horner fold from an
already computed accumulator with current error budget `mu`. -/
noncomputable def matrixHornerP3ForwardOneNormErrorBudgetFrom
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ) :
    (Fin n → Fin n → ℝ) → ℝ →
      List (Fin n → Fin n → ℝ) → ℝ
  | _Yhat, mu, [] => mu
  | Yhat, mu, A :: rest =>
      let mu' :=
        matrixHornerP3StepOneNormErrorBudget fp n X Yhat A +
          mu * oneNorm X
      matrixHornerP3ForwardOneNormErrorBudgetFrom fp n X
        (fl_matrixHornerP3Step fp n X Yhat A) mu' rest

/-- Top-level recursive finite one-norm budget for rounded matrix Horner. -/
noncomputable def matrixHornerP3ForwardOneNormErrorBudget
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ) :
    List (Fin n → Fin n → ℝ) → ℝ
  | [] => 0
  | A :: rest =>
      matrixHornerP3ForwardOneNormErrorBudgetFrom fp n X A 0 rest

theorem fl_matrixHornerP3Fold_infNorm_error_bound_from
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (hnpos : 0 < n) (hn : gammaValid fp n) :
    ∀ (rest : List (Fin n → Fin n → ℝ))
      (Yhat Y : Fin n → Fin n → ℝ) (mu : ℝ),
      0 ≤ mu →
      infNorm (fun i j => Yhat i j - Y i j) ≤ mu →
      infNorm
          (fun i j =>
            rest.foldl (fl_matrixHornerP3Step fp n X) Yhat i j -
              rest.foldl (matrixHornerP3Step n X) Y i j) ≤
        matrixHornerP3ForwardInfErrorBudgetFrom fp n X Yhat mu rest := by
  intro rest
  induction rest with
  | nil =>
      intro Yhat Y mu _hmu herr
      simpa [matrixHornerP3ForwardInfErrorBudgetFrom] using herr
  | cons A rest ih =>
      intro Yhat Y mu hmu herr
      let Yhat' := fl_matrixHornerP3Step fp n X Yhat A
      let Y' := matrixHornerP3Step n X Y A
      let mu' :=
        matrixHornerP3StepInfErrorBudget fp n X Yhat A +
          mu * infNorm X
      have hbudget_nonneg :
          0 ≤ matrixHornerP3StepInfErrorBudget fp n X Yhat A := by
        have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
        have hY : 0 ≤ infNorm Yhat := infNorm_nonneg Yhat
        have hX : 0 ≤ infNorm X := infNorm_nonneg X
        unfold matrixHornerP3StepInfErrorBudget
        exact add_nonneg
          (mul_nonneg fp.u_nonneg (infNorm_nonneg _))
          (mul_nonneg (mul_nonneg hγ hY) hX)
      have hmu' : 0 ≤ mu' := by
        have hX : 0 ≤ infNorm X := infNorm_nonneg X
        exact add_nonneg hbudget_nonneg (mul_nonneg hmu hX)
      have hstep :
          infNorm (fun i j => Yhat' i j - Y' i j) ≤ mu' := by
        let Elocal : Fin n → Fin n → ℝ :=
          fun i j =>
            fl_matrixHornerP3Step fp n X Yhat A i j -
              matrixHornerP3Step n X Yhat A i j
        let Eprop : Fin n → Fin n → ℝ :=
          fun i j =>
            matrixHornerP3Step n X Yhat A i j -
              matrixHornerP3Step n X Y A i j
        have hdecomp :
            (fun i j => Yhat' i j - Y' i j) =
              fun i j => Elocal i j + Eprop i j := by
          ext i j
          simp [Yhat', Y', Elocal, Eprop]
        have hlocal :
            infNorm Elocal ≤
              matrixHornerP3StepInfErrorBudget fp n X Yhat A := by
          simpa [Elocal] using
            fl_matrixHornerP3Step_infNorm_error_bound fp n X Yhat A hn
        have hprop :
            infNorm Eprop ≤ mu * infNorm X := by
          have hprop0 :
              infNorm Eprop ≤
                infNorm (fun i j => Yhat i j - Y i j) * infNorm X := by
            simpa [Eprop] using
              matrixHornerP3Step_infNorm_lipschitz n hnpos X Yhat Y A
          exact le_trans hprop0
            (mul_le_mul_of_nonneg_right herr (infNorm_nonneg X))
        calc
          infNorm (fun i j => Yhat' i j - Y' i j)
              = infNorm (fun i j => Elocal i j + Eprop i j) := by
                rw [hdecomp]
          _ ≤ infNorm Elocal + infNorm Eprop := infNorm_add_le Elocal Eprop
          _ ≤ matrixHornerP3StepInfErrorBudget fp n X Yhat A +
                mu * infNorm X := add_le_add hlocal hprop
          _ = mu' := rfl
      simpa [matrixHornerP3ForwardInfErrorBudgetFrom, Yhat', Y', mu'] using
        ih Yhat' Y' mu' hmu' hstep

theorem fl_matrixHornerP3Desc_infNorm_error_bound
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ))
    (hnpos : 0 < n) (hn : gammaValid fp n) :
    infNorm
        (fun i j =>
          fl_matrixHornerP3Desc fp n X coeffsDesc i j -
            matrixHornerP3Desc n X coeffsDesc i j) ≤
      matrixHornerP3ForwardInfErrorBudget fp n X coeffsDesc := by
  cases coeffsDesc with
  | nil =>
      have hzero :
          (fun i j =>
            fl_matrixHornerP3Desc fp n X [] i j -
              matrixHornerP3Desc n X [] i j) =
            zeroMatrix n := by
        ext i j
        simp [fl_matrixHornerP3Desc, matrixHornerP3Desc, zeroMatrix]
      rw [hzero, matrixHornerP3ForwardInfErrorBudget]
      exact le_of_eq (infNorm_zeroMatrix n)
  | cons A rest =>
      have hinit :
          infNorm (fun i j => A i j - A i j) ≤ 0 := by
        have hzero :
            (fun i j => A i j - A i j) = zeroMatrix n := by
          ext i j
          simp [zeroMatrix]
        rw [hzero, infNorm_zeroMatrix]
      simpa [fl_matrixHornerP3Desc, matrixHornerP3Desc,
        matrixHornerP3ForwardInfErrorBudget] using
        fl_matrixHornerP3Fold_infNorm_error_bound_from
          fp n X hnpos hn rest A A 0 (by norm_num) hinit

theorem fl_matrixHornerP3Fold_oneNorm_error_bound_from
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n) :
    ∀ (rest : List (Fin n → Fin n → ℝ))
      (Yhat Y : Fin n → Fin n → ℝ) (mu : ℝ),
      0 ≤ mu →
      oneNorm (fun i j => Yhat i j - Y i j) ≤ mu →
      oneNorm
          (fun i j =>
            rest.foldl (fl_matrixHornerP3Step fp n X) Yhat i j -
              rest.foldl (matrixHornerP3Step n X) Y i j) ≤
        matrixHornerP3ForwardOneNormErrorBudgetFrom fp n X Yhat mu rest := by
  intro rest
  induction rest with
  | nil =>
      intro Yhat Y mu _hmu herr
      simpa [matrixHornerP3ForwardOneNormErrorBudgetFrom] using herr
  | cons A rest ih =>
      intro Yhat Y mu hmu herr
      let Yhat' := fl_matrixHornerP3Step fp n X Yhat A
      let Y' := matrixHornerP3Step n X Y A
      let mu' :=
        matrixHornerP3StepOneNormErrorBudget fp n X Yhat A +
          mu * oneNorm X
      have hbudget_nonneg :
          0 ≤ matrixHornerP3StepOneNormErrorBudget fp n X Yhat A := by
        have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
        have hY : 0 ≤ oneNorm Yhat := oneNorm_nonneg Yhat
        have hX : 0 ≤ oneNorm X := oneNorm_nonneg X
        unfold matrixHornerP3StepOneNormErrorBudget
        exact add_nonneg
          (mul_nonneg fp.u_nonneg (oneNorm_nonneg _))
          (mul_nonneg (mul_nonneg hγ hY) hX)
      have hmu' : 0 ≤ mu' := by
        have hX : 0 ≤ oneNorm X := oneNorm_nonneg X
        exact add_nonneg hbudget_nonneg (mul_nonneg hmu hX)
      have hstep :
          oneNorm (fun i j => Yhat' i j - Y' i j) ≤ mu' := by
        let Elocal : Fin n → Fin n → ℝ :=
          fun i j =>
            fl_matrixHornerP3Step fp n X Yhat A i j -
              matrixHornerP3Step n X Yhat A i j
        let Eprop : Fin n → Fin n → ℝ :=
          fun i j =>
            matrixHornerP3Step n X Yhat A i j -
              matrixHornerP3Step n X Y A i j
        have hdecomp :
            (fun i j => Yhat' i j - Y' i j) =
              fun i j => Elocal i j + Eprop i j := by
          ext i j
          simp [Yhat', Y', Elocal, Eprop]
        have hlocal :
            oneNorm Elocal ≤
              matrixHornerP3StepOneNormErrorBudget fp n X Yhat A := by
          simpa [Elocal] using
            fl_matrixHornerP3Step_oneNorm_error_bound fp n X Yhat A hn
        have hprop :
            oneNorm Eprop ≤ mu * oneNorm X := by
          have hprop0 :
              oneNorm Eprop ≤
                oneNorm (fun i j => Yhat i j - Y i j) * oneNorm X := by
            simpa [Eprop] using
              matrixHornerP3Step_oneNorm_lipschitz n X Yhat Y A
          exact le_trans hprop0
            (mul_le_mul_of_nonneg_right herr (oneNorm_nonneg X))
        calc
          oneNorm (fun i j => Yhat' i j - Y' i j)
              = oneNorm (fun i j => Elocal i j + Eprop i j) := by
                rw [hdecomp]
          _ ≤ oneNorm Elocal + oneNorm Eprop := oneNorm_add_le Elocal Eprop
          _ ≤ matrixHornerP3StepOneNormErrorBudget fp n X Yhat A +
                mu * oneNorm X := add_le_add hlocal hprop
          _ = mu' := rfl
      simpa [matrixHornerP3ForwardOneNormErrorBudgetFrom, Yhat', Y', mu'] using
        ih Yhat' Y' mu' hmu' hstep

theorem fl_matrixHornerP3Desc_oneNorm_error_bound
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ))
    (hn : gammaValid fp n) :
    oneNorm
        (fun i j =>
          fl_matrixHornerP3Desc fp n X coeffsDesc i j -
            matrixHornerP3Desc n X coeffsDesc i j) ≤
      matrixHornerP3ForwardOneNormErrorBudget fp n X coeffsDesc := by
  cases coeffsDesc with
  | nil =>
      have hzero :
          (fun i j =>
            fl_matrixHornerP3Desc fp n X [] i j -
              matrixHornerP3Desc n X [] i j) =
            zeroMatrix n := by
        ext i j
        simp [fl_matrixHornerP3Desc, matrixHornerP3Desc, zeroMatrix]
      rw [hzero, matrixHornerP3ForwardOneNormErrorBudget]
      have hone_zero : oneNorm (zeroMatrix n) = 0 := by
        unfold oneNorm
        simpa [zeroMatrix] using infNorm_zeroMatrix n
      exact le_of_eq hone_zero
  | cons A rest =>
      have hinit :
          oneNorm (fun i j => A i j - A i j) ≤ 0 := by
        have hzero :
            (fun i j => A i j - A i j) = zeroMatrix n := by
          ext i j
          simp [zeroMatrix]
        rw [hzero]
        have hone_zero : oneNorm (zeroMatrix n) = 0 := by
          unfold oneNorm
          simpa [zeroMatrix] using infNorm_zeroMatrix n
        rw [hone_zero]
      simpa [fl_matrixHornerP3Desc, matrixHornerP3Desc,
        matrixHornerP3ForwardOneNormErrorBudget] using
        fl_matrixHornerP3Fold_oneNorm_error_bound_from
          fp n X hn rest A A 0 (by norm_num) hinit

/-- Source-shaped local scalar infinity-norm budget for one rounded matrix
Horner step in Problem 5.6.  The parameter `eta` bounds the exact accumulator
and `mu` bounds the accumulated error, so the computed accumulator is charged
only through `eta + mu`. -/
noncomputable def matrixHornerP3ScalarInfStepBudget
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (eta mu : ℝ) (A : Fin n → Fin n → ℝ) : ℝ :=
  fp.u * ((1 + gamma fp n) * (eta + mu) * infNorm X + infNorm A) +
    gamma fp n * (eta + mu) * infNorm X

/-- Source-shaped local scalar one-norm budget for one rounded matrix Horner
step in Problem 5.6. -/
noncomputable def matrixHornerP3ScalarOneNormStepBudget
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (eta mu : ℝ) (A : Fin n → Fin n → ℝ) : ℝ :=
  fp.u * ((1 + gamma fp n) * (eta + mu) * oneNorm X + oneNorm A) +
    gamma fp n * (eta + mu) * oneNorm X

/-- Recursive source-shaped scalar infinity-norm budget for rounded matrix
Horner.  It follows only the scalar exact-accumulator majorant `eta` and scalar
error majorant `mu`, avoiding computed matrix norms in the recurrence. -/
noncomputable def matrixHornerP3ScalarInfForwardBudgetFrom
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ) :
    ℝ → ℝ → List (Fin n → Fin n → ℝ) → ℝ
  | _eta, mu, [] => mu
  | eta, mu, A :: rest =>
      let eta' := eta * infNorm X + infNorm A
      let mu' :=
        matrixHornerP3ScalarInfStepBudget fp n X eta mu A +
          mu * infNorm X
      matrixHornerP3ScalarInfForwardBudgetFrom fp n X eta' mu' rest

/-- Top-level source-shaped scalar infinity-norm budget for rounded matrix
Horner. -/
noncomputable def matrixHornerP3ScalarInfForwardBudget
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ) :
    List (Fin n → Fin n → ℝ) → ℝ
  | [] => 0
  | A :: rest =>
      matrixHornerP3ScalarInfForwardBudgetFrom fp n X (infNorm A) 0 rest

/-- Recursive source-shaped scalar one-norm budget for rounded matrix Horner. -/
noncomputable def matrixHornerP3ScalarOneNormForwardBudgetFrom
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ) :
    ℝ → ℝ → List (Fin n → Fin n → ℝ) → ℝ
  | _eta, mu, [] => mu
  | eta, mu, A :: rest =>
      let eta' := eta * oneNorm X + oneNorm A
      let mu' :=
        matrixHornerP3ScalarOneNormStepBudget fp n X eta mu A +
          mu * oneNorm X
      matrixHornerP3ScalarOneNormForwardBudgetFrom fp n X eta' mu' rest

/-- Top-level source-shaped scalar one-norm budget for rounded matrix Horner. -/
noncomputable def matrixHornerP3ScalarOneNormForwardBudget
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ) :
    List (Fin n → Fin n → ℝ) → ℝ
  | [] => 0
  | A :: rest =>
      matrixHornerP3ScalarOneNormForwardBudgetFrom fp n X (oneNorm A) 0 rest

theorem matrixHornerP3ForwardInfErrorBudgetFrom_le_scalar
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (hnpos : 0 < n) (hn : gammaValid fp n) :
    ∀ (rest : List (Fin n → Fin n → ℝ))
      (Yhat Y : Fin n → Fin n → ℝ) (eta mu muSrc : ℝ),
      0 ≤ mu →
      0 ≤ muSrc →
      0 ≤ eta →
      mu ≤ muSrc →
      infNorm (fun i j => Yhat i j - Y i j) ≤ mu →
      infNorm Y ≤ eta →
      matrixHornerP3ForwardInfErrorBudgetFrom fp n X Yhat mu rest ≤
        matrixHornerP3ScalarInfForwardBudgetFrom fp n X eta muSrc rest := by
  intro rest
  induction rest with
  | nil =>
      intro Yhat Y eta mu muSrc _hmu _hmuSrc _heta hle _herr _hY
      simpa [matrixHornerP3ForwardInfErrorBudgetFrom,
        matrixHornerP3ScalarInfForwardBudgetFrom] using hle
  | cons A rest ih =>
      intro Yhat Y eta mu muSrc hmu hmuSrc heta hle herr hY
      let Yhat' := fl_matrixHornerP3Step fp n X Yhat A
      let Y' := matrixHornerP3Step n X Y A
      let localBudget := matrixHornerP3StepInfErrorBudget fp n X Yhat A
      let mu' := localBudget + mu * infNorm X
      let eta' := eta * infNorm X + infNorm A
      let sourceStep :=
        matrixHornerP3ScalarInfStepBudget fp n X eta muSrc A
      let muSrc' := sourceStep + muSrc * infNorm X
      have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
      have hX : 0 ≤ infNorm X := infNorm_nonneg X
      have hYhat_norm : infNorm Yhat ≤ eta + muSrc := by
        calc
          infNorm Yhat
              ≤ infNorm (fun i j => Yhat i j - Y i j) + infNorm Y :=
                infNorm_le_sub_add Yhat Y
          _ ≤ mu + eta := add_le_add herr hY
          _ ≤ muSrc + eta := add_le_add hle le_rfl
          _ = eta + muSrc := by ring
      have hlocal_le : localBudget ≤ sourceStep := by
        simpa [localBudget, sourceStep, matrixHornerP3ScalarInfStepBudget] using
          matrixHornerP3StepInfErrorBudget_le_acc_majorant
            fp n X Yhat A eta muSrc hnpos hn hYhat_norm
      have hlocal_nonneg : 0 ≤ localBudget := by
        have hYhat_nonneg : 0 ≤ infNorm Yhat := infNorm_nonneg Yhat
        unfold localBudget matrixHornerP3StepInfErrorBudget
        exact add_nonneg
          (mul_nonneg fp.u_nonneg (infNorm_nonneg _))
          (mul_nonneg (mul_nonneg hγ hYhat_nonneg) hX)
      have hmu' : 0 ≤ mu' := by
        exact add_nonneg hlocal_nonneg (mul_nonneg hmu hX)
      have hsourceStep_nonneg : 0 ≤ sourceStep := by
        have hsum : 0 ≤ eta + muSrc := add_nonneg heta hmuSrc
        have honeγ : 0 ≤ 1 + gamma fp n := by linarith
        have hinside :
            0 ≤ (1 + gamma fp n) * (eta + muSrc) * infNorm X +
              infNorm A := by
          exact add_nonneg
            (mul_nonneg (mul_nonneg honeγ hsum) hX)
            (infNorm_nonneg A)
        have htail :
            0 ≤ gamma fp n * (eta + muSrc) * infNorm X :=
          mul_nonneg (mul_nonneg hγ hsum) hX
        simpa [sourceStep, matrixHornerP3ScalarInfStepBudget] using
          add_nonneg (mul_nonneg fp.u_nonneg hinside) htail
      have hmuSrc' : 0 ≤ muSrc' := by
        exact add_nonneg hsourceStep_nonneg (mul_nonneg hmuSrc hX)
      have hmu'_le : mu' ≤ muSrc' := by
        have hprop : mu * infNorm X ≤ muSrc * infNorm X :=
          mul_le_mul_of_nonneg_right hle hX
        calc
          mu' = localBudget + mu * infNorm X := rfl
          _ ≤ sourceStep + muSrc * infNorm X :=
              add_le_add hlocal_le hprop
          _ = muSrc' := rfl
      have heta' : 0 ≤ eta' := by
        exact add_nonneg (mul_nonneg heta hX) (infNorm_nonneg A)
      have herr' :
          infNorm (fun i j => Yhat' i j - Y' i j) ≤ mu' := by
        have h :=
          fl_matrixHornerP3Fold_infNorm_error_bound_from
            fp n X hnpos hn [A] Yhat Y mu hmu herr
        simpa [Yhat', Y', mu', localBudget,
          matrixHornerP3ForwardInfErrorBudgetFrom] using h
      have hY' : infNorm Y' ≤ eta' := by
        have hstep :
            infNorm Y' ≤ infNorm Y * infNorm X + infNorm A := by
          have hmul :
              infNorm (matMul n Y X) ≤ infNorm Y * infNorm X := by
            simpa using infNorm_matMul_le hnpos Y X
          have hadd :
              infNorm (matrixHornerP3Step n X Y A) ≤
                infNorm (matMul n Y X) + infNorm A := by
            simpa [matrixHornerP3Step, matAdd] using
              infNorm_add_le (matMul n Y X) A
          calc
            infNorm Y'
                ≤ infNorm (matMul n Y X) + infNorm A := by
                  simpa [Y'] using hadd
            _ ≤ infNorm Y * infNorm X + infNorm A :=
                add_le_add hmul le_rfl
        calc
          infNorm Y'
              ≤ infNorm Y * infNorm X + infNorm A := hstep
          _ ≤ eta * infNorm X + infNorm A :=
              add_le_add (mul_le_mul_of_nonneg_right hY hX) le_rfl
          _ = eta' := rfl
      have hrec :=
        ih Yhat' Y' eta' mu' muSrc'
          hmu' hmuSrc' heta' hmu'_le herr' hY'
      simpa [matrixHornerP3ForwardInfErrorBudgetFrom,
        matrixHornerP3ScalarInfForwardBudgetFrom, Yhat', mu', eta',
        sourceStep, muSrc', localBudget] using hrec

theorem matrixHornerP3ForwardOneNormErrorBudgetFrom_le_scalar
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n) :
    ∀ (rest : List (Fin n → Fin n → ℝ))
      (Yhat Y : Fin n → Fin n → ℝ) (eta mu muSrc : ℝ),
      0 ≤ mu →
      0 ≤ muSrc →
      0 ≤ eta →
      mu ≤ muSrc →
      oneNorm (fun i j => Yhat i j - Y i j) ≤ mu →
      oneNorm Y ≤ eta →
      matrixHornerP3ForwardOneNormErrorBudgetFrom fp n X Yhat mu rest ≤
        matrixHornerP3ScalarOneNormForwardBudgetFrom fp n X eta muSrc rest := by
  intro rest
  induction rest with
  | nil =>
      intro Yhat Y eta mu muSrc _hmu _hmuSrc _heta hle _herr _hY
      simpa [matrixHornerP3ForwardOneNormErrorBudgetFrom,
        matrixHornerP3ScalarOneNormForwardBudgetFrom] using hle
  | cons A rest ih =>
      intro Yhat Y eta mu muSrc hmu hmuSrc heta hle herr hY
      let Yhat' := fl_matrixHornerP3Step fp n X Yhat A
      let Y' := matrixHornerP3Step n X Y A
      let localBudget := matrixHornerP3StepOneNormErrorBudget fp n X Yhat A
      let mu' := localBudget + mu * oneNorm X
      let eta' := eta * oneNorm X + oneNorm A
      let sourceStep :=
        matrixHornerP3ScalarOneNormStepBudget fp n X eta muSrc A
      let muSrc' := sourceStep + muSrc * oneNorm X
      have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
      have hX : 0 ≤ oneNorm X := oneNorm_nonneg X
      have hYhat_norm : oneNorm Yhat ≤ eta + muSrc := by
        calc
          oneNorm Yhat
              ≤ oneNorm (fun i j => Yhat i j - Y i j) + oneNorm Y :=
                oneNorm_le_sub_add Yhat Y
          _ ≤ mu + eta := add_le_add herr hY
          _ ≤ muSrc + eta := add_le_add hle le_rfl
          _ = eta + muSrc := by ring
      have hlocal_le : localBudget ≤ sourceStep := by
        simpa [localBudget, sourceStep, matrixHornerP3ScalarOneNormStepBudget] using
          matrixHornerP3StepOneNormErrorBudget_le_acc_majorant
            fp n X Yhat A eta muSrc hn hYhat_norm
      have hlocal_nonneg : 0 ≤ localBudget := by
        have hYhat_nonneg : 0 ≤ oneNorm Yhat := oneNorm_nonneg Yhat
        unfold localBudget matrixHornerP3StepOneNormErrorBudget
        exact add_nonneg
          (mul_nonneg fp.u_nonneg (oneNorm_nonneg _))
          (mul_nonneg (mul_nonneg hγ hYhat_nonneg) hX)
      have hmu' : 0 ≤ mu' := by
        exact add_nonneg hlocal_nonneg (mul_nonneg hmu hX)
      have hsourceStep_nonneg : 0 ≤ sourceStep := by
        have hsum : 0 ≤ eta + muSrc := add_nonneg heta hmuSrc
        have honeγ : 0 ≤ 1 + gamma fp n := by linarith
        have hinside :
            0 ≤ (1 + gamma fp n) * (eta + muSrc) * oneNorm X +
              oneNorm A := by
          exact add_nonneg
            (mul_nonneg (mul_nonneg honeγ hsum) hX)
            (oneNorm_nonneg A)
        have htail :
            0 ≤ gamma fp n * (eta + muSrc) * oneNorm X :=
          mul_nonneg (mul_nonneg hγ hsum) hX
        simpa [sourceStep, matrixHornerP3ScalarOneNormStepBudget] using
          add_nonneg (mul_nonneg fp.u_nonneg hinside) htail
      have hmuSrc' : 0 ≤ muSrc' := by
        exact add_nonneg hsourceStep_nonneg (mul_nonneg hmuSrc hX)
      have hmu'_le : mu' ≤ muSrc' := by
        have hprop : mu * oneNorm X ≤ muSrc * oneNorm X :=
          mul_le_mul_of_nonneg_right hle hX
        calc
          mu' = localBudget + mu * oneNorm X := rfl
          _ ≤ sourceStep + muSrc * oneNorm X :=
              add_le_add hlocal_le hprop
          _ = muSrc' := rfl
      have heta' : 0 ≤ eta' := by
        exact add_nonneg (mul_nonneg heta hX) (oneNorm_nonneg A)
      have herr' :
          oneNorm (fun i j => Yhat' i j - Y' i j) ≤ mu' := by
        have h :=
          fl_matrixHornerP3Fold_oneNorm_error_bound_from
            fp n X hn [A] Yhat Y mu hmu herr
        simpa [Yhat', Y', mu', localBudget,
          matrixHornerP3ForwardOneNormErrorBudgetFrom] using h
      have hY' : oneNorm Y' ≤ eta' := by
        have hstep :
            oneNorm Y' ≤ oneNorm Y * oneNorm X + oneNorm A := by
          have hmul :
              oneNorm (matMul n Y X) ≤ oneNorm Y * oneNorm X := by
            simpa using oneNorm_matMul_le Y X
          have hadd :
              oneNorm (matrixHornerP3Step n X Y A) ≤
                oneNorm (matMul n Y X) + oneNorm A := by
            simpa [matrixHornerP3Step, matAdd] using
              oneNorm_add_le (matMul n Y X) A
          calc
            oneNorm Y'
                ≤ oneNorm (matMul n Y X) + oneNorm A := by
                  simpa [Y'] using hadd
            _ ≤ oneNorm Y * oneNorm X + oneNorm A :=
                add_le_add hmul le_rfl
        calc
          oneNorm Y'
              ≤ oneNorm Y * oneNorm X + oneNorm A := hstep
          _ ≤ eta * oneNorm X + oneNorm A :=
              add_le_add (mul_le_mul_of_nonneg_right hY hX) le_rfl
          _ = eta' := rfl
      have hrec :=
        ih Yhat' Y' eta' mu' muSrc'
          hmu' hmuSrc' heta' hmu'_le herr' hY'
      simpa [matrixHornerP3ForwardOneNormErrorBudgetFrom,
        matrixHornerP3ScalarOneNormForwardBudgetFrom, Yhat', mu', eta',
        sourceStep, muSrc', localBudget] using hrec

theorem matrixHornerP3ForwardInfErrorBudget_le_scalar
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ))
    (hnpos : 0 < n) (hn : gammaValid fp n) :
    matrixHornerP3ForwardInfErrorBudget fp n X coeffsDesc ≤
      matrixHornerP3ScalarInfForwardBudget fp n X coeffsDesc := by
  cases coeffsDesc with
  | nil =>
      simp [matrixHornerP3ForwardInfErrorBudget,
        matrixHornerP3ScalarInfForwardBudget]
  | cons A rest =>
      have hinit :
          infNorm (fun i j => A i j - A i j) ≤ 0 := by
        have hzero :
            (fun i j => A i j - A i j) = zeroMatrix n := by
          ext i j
          simp [zeroMatrix]
        rw [hzero, infNorm_zeroMatrix]
      simpa [matrixHornerP3ForwardInfErrorBudget,
        matrixHornerP3ScalarInfForwardBudget] using
        matrixHornerP3ForwardInfErrorBudgetFrom_le_scalar
          fp n X hnpos hn rest A A (infNorm A) 0 0
          (by norm_num) (by norm_num) (infNorm_nonneg A)
          (by norm_num) hinit le_rfl

theorem matrixHornerP3ForwardOneNormErrorBudget_le_scalar
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ))
    (hn : gammaValid fp n) :
    matrixHornerP3ForwardOneNormErrorBudget fp n X coeffsDesc ≤
      matrixHornerP3ScalarOneNormForwardBudget fp n X coeffsDesc := by
  cases coeffsDesc with
  | nil =>
      simp [matrixHornerP3ForwardOneNormErrorBudget,
        matrixHornerP3ScalarOneNormForwardBudget]
  | cons A rest =>
      have hinit :
          oneNorm (fun i j => A i j - A i j) ≤ 0 := by
        have hzero :
            (fun i j => A i j - A i j) = zeroMatrix n := by
          ext i j
          simp [zeroMatrix]
        rw [hzero]
        have hone_zero : oneNorm (zeroMatrix n) = 0 := by
          unfold oneNorm
          simpa [zeroMatrix] using infNorm_zeroMatrix n
        rw [hone_zero]
      simpa [matrixHornerP3ForwardOneNormErrorBudget,
        matrixHornerP3ScalarOneNormForwardBudget] using
        matrixHornerP3ForwardOneNormErrorBudgetFrom_le_scalar
          fp n X hn rest A A (oneNorm A) 0 0
          (by norm_num) (by norm_num) (oneNorm_nonneg A)
          (by norm_num) hinit le_rfl

/-- The exact scalar roundoff factor for the source-shaped matrix-Horner budget.
Its first-order part is `(n+1)u`, since `gamma fp n = n*u + O(u^2)`. -/
noncomputable def matrixHornerP3ScalarRoundoffFactor
    (fp : FPModel) (n : ℕ) : ℝ :=
  fp.u * (1 + gamma fp n) + gamma fp n

/-- Higher-order remainder after extracting the first-order `(n+1)u` part from
the scalar roundoff factor used in the matrix-Horner source budget. -/
noncomputable def matrixHornerP3ScalarRoundoffFactorRemainder
    (fp : FPModel) (n : ℕ) : ℝ :=
  fp.u * gamma fp n +
    (((n : ℝ) * fp.u) ^ 2) / (1 - (n : ℝ) * fp.u)

theorem matrixHornerP3ScalarRoundoffFactor_eq_first_order_add_remainder
    (fp : FPModel) (n : ℕ) (hn : gammaValid fp n) :
    matrixHornerP3ScalarRoundoffFactor fp n =
      ((n : ℝ) + 1) * fp.u +
        matrixHornerP3ScalarRoundoffFactorRemainder fp n := by
  unfold matrixHornerP3ScalarRoundoffFactor
    matrixHornerP3ScalarRoundoffFactorRemainder
  rw [gamma_eq_linear_plus_quadratic_remainder fp n hn]
  ring

theorem matrixHornerP3ScalarRoundoffFactorRemainder_eq_zero_of_u_eq_zero
    (fp : FPModel) (n : ℕ) (hu : fp.u = 0) :
    matrixHornerP3ScalarRoundoffFactorRemainder fp n = 0 := by
  simp [matrixHornerP3ScalarRoundoffFactorRemainder, gamma, hu]

lemma matrixHornerP3ScalarRoundoffFactor_nonneg
    (fp : FPModel) (n : ℕ) (hn : gammaValid fp n) :
    0 ≤ matrixHornerP3ScalarRoundoffFactor fp n := by
  have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have honeγ : 0 ≤ 1 + gamma fp n := by linarith
  unfold matrixHornerP3ScalarRoundoffFactor
  exact add_nonneg (mul_nonneg fp.u_nonneg honeγ) hγ

lemma fp_u_le_matrixHornerP3ScalarRoundoffFactor
    (fp : FPModel) (n : ℕ) (hn : gammaValid fp n) :
    fp.u ≤ matrixHornerP3ScalarRoundoffFactor fp n := by
  have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have hprod : 0 ≤ fp.u * gamma fp n := mul_nonneg fp.u_nonneg hγ
  unfold matrixHornerP3ScalarRoundoffFactor
  nlinarith

theorem matrixHornerP3ScalarInfStepBudget_le_factor
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (eta mu : ℝ) (A : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n) :
    matrixHornerP3ScalarInfStepBudget fp n X eta mu A ≤
      matrixHornerP3ScalarRoundoffFactor fp n *
        ((eta + mu) * infNorm X + infNorm A) := by
  have hu_le :
      fp.u ≤ matrixHornerP3ScalarRoundoffFactor fp n :=
    fp_u_le_matrixHornerP3ScalarRoundoffFactor fp n hn
  have hA : 0 ≤ infNorm A := infNorm_nonneg A
  calc
    matrixHornerP3ScalarInfStepBudget fp n X eta mu A
        =
          matrixHornerP3ScalarRoundoffFactor fp n *
              ((eta + mu) * infNorm X) +
            fp.u * infNorm A := by
          unfold matrixHornerP3ScalarInfStepBudget
            matrixHornerP3ScalarRoundoffFactor
          ring
    _ ≤
          matrixHornerP3ScalarRoundoffFactor fp n *
              ((eta + mu) * infNorm X) +
            matrixHornerP3ScalarRoundoffFactor fp n * infNorm A :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hu_le hA)
    _ =
          matrixHornerP3ScalarRoundoffFactor fp n *
            ((eta + mu) * infNorm X + infNorm A) := by
        ring

theorem matrixHornerP3ScalarOneNormStepBudget_le_factor
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (eta mu : ℝ) (A : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n) :
    matrixHornerP3ScalarOneNormStepBudget fp n X eta mu A ≤
      matrixHornerP3ScalarRoundoffFactor fp n *
        ((eta + mu) * oneNorm X + oneNorm A) := by
  have hu_le :
      fp.u ≤ matrixHornerP3ScalarRoundoffFactor fp n :=
    fp_u_le_matrixHornerP3ScalarRoundoffFactor fp n hn
  have hA : 0 ≤ oneNorm A := oneNorm_nonneg A
  calc
    matrixHornerP3ScalarOneNormStepBudget fp n X eta mu A
        =
          matrixHornerP3ScalarRoundoffFactor fp n *
              ((eta + mu) * oneNorm X) +
            fp.u * oneNorm A := by
          unfold matrixHornerP3ScalarOneNormStepBudget
            matrixHornerP3ScalarRoundoffFactor
          ring
    _ ≤
          matrixHornerP3ScalarRoundoffFactor fp n *
              ((eta + mu) * oneNorm X) +
            matrixHornerP3ScalarRoundoffFactor fp n * oneNorm A :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hu_le hA)
    _ =
          matrixHornerP3ScalarRoundoffFactor fp n *
            ((eta + mu) * oneNorm X + oneNorm A) := by
        ring

theorem matrixHornerP3ScalarInfForwardBudgetFrom_le_geometric_majorant
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n) :
    ∀ (rest : List (Fin n → Fin n → ℝ)) (eta mu rho : ℝ),
      0 ≤ eta →
      0 ≤ mu →
      0 ≤ rho →
      mu ≤ rho * eta →
      matrixHornerP3ScalarInfForwardBudgetFrom fp n X eta mu rest ≤
        (((1 + matrixHornerP3ScalarRoundoffFactor fp n) ^ rest.length) *
            (1 + rho) - 1) *
          (eta * infNorm X ^ rest.length +
            matrixPolyP3InfNormMajorant n X rest) := by
  intro rest
  induction rest with
  | nil =>
      intro eta mu rho _heta _hmu _hrho hmu_le
      simpa [matrixHornerP3ScalarInfForwardBudgetFrom,
        matrixPolyP3InfNormMajorant, polyDesc] using hmu_le
  | cons A rest ih =>
      intro eta mu rho heta hmu hrho hmu_le
      let r := matrixHornerP3ScalarRoundoffFactor fp n
      let eta' := eta * infNorm X + infNorm A
      let step := matrixHornerP3ScalarInfStepBudget fp n X eta mu A
      let mu' := step + mu * infNorm X
      let rho' := (1 + r) * (1 + rho) - 1
      have hr : 0 ≤ r := by
        simpa [r] using matrixHornerP3ScalarRoundoffFactor_nonneg fp n hn
      have hX : 0 ≤ infNorm X := infNorm_nonneg X
      have hA : 0 ≤ infNorm A := infNorm_nonneg A
      have heta' : 0 ≤ eta' := by
        exact add_nonneg (mul_nonneg heta hX) hA
      have hstep_nonneg : 0 ≤ step := by
        have hsum : 0 ≤ eta + mu := add_nonneg heta hmu
        have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
        have honeγ : 0 ≤ 1 + gamma fp n := by linarith
        have hinside :
            0 ≤ (1 + gamma fp n) * (eta + mu) * infNorm X +
              infNorm A := by
          exact add_nonneg
            (mul_nonneg (mul_nonneg honeγ hsum) hX)
            hA
        have htail :
            0 ≤ gamma fp n * (eta + mu) * infNorm X :=
          mul_nonneg (mul_nonneg hγ hsum) hX
        simpa [step, matrixHornerP3ScalarInfStepBudget] using
          add_nonneg (mul_nonneg fp.u_nonneg hinside) htail
      have hmu' : 0 ≤ mu' := by
        exact add_nonneg hstep_nonneg (mul_nonneg hmu hX)
      have hstep_le :
          step ≤ r * ((eta + mu) * infNorm X + infNorm A) := by
        simpa [step, r] using
          matrixHornerP3ScalarInfStepBudget_le_factor
            fp n X eta mu A hn
      have hsum_le :
          (eta + mu) * infNorm X + infNorm A ≤
            (eta + rho * eta) * infNorm X + infNorm A := by
        have hbase : eta + mu ≤ eta + rho * eta :=
          add_le_add le_rfl hmu_le
        exact add_le_add (mul_le_mul_of_nonneg_right hbase hX) le_rfl
      have hstep_le_rho :
          step ≤ r * ((eta + rho * eta) * infNorm X + infNorm A) :=
        le_trans hstep_le (mul_le_mul_of_nonneg_left hsum_le hr)
      have hmu_x_le :
          mu * infNorm X ≤ rho * eta * infNorm X :=
        mul_le_mul_of_nonneg_right hmu_le hX
      have hr_le_rho' : r ≤ rho' := by
        have hprod : 0 ≤ r * rho := mul_nonneg hr hrho
        dsimp [rho']
        nlinarith
      have hrho' : 0 ≤ rho' := le_trans hr hr_le_rho'
      have hmu'_le : mu' ≤ rho' * eta' := by
        calc
          mu'
              = step + mu * infNorm X := rfl
          _ ≤
              r * ((eta + rho * eta) * infNorm X + infNorm A) +
                rho * eta * infNorm X :=
              add_le_add hstep_le_rho hmu_x_le
          _ =
              rho' * (eta * infNorm X) + r * infNorm A := by
              dsimp [rho']
              ring
          _ ≤ rho' * (eta * infNorm X) + rho' * infNorm A :=
              add_le_add le_rfl (mul_le_mul_of_nonneg_right hr_le_rho' hA)
          _ = rho' * eta' := by
              dsimp [eta']
              ring
      have hrec :=
        ih eta' mu' rho' heta' hmu' hrho' hmu'_le
      have hcoef :
          ((1 + matrixHornerP3ScalarRoundoffFactor fp n) ^ rest.length *
                (1 + rho') - 1) =
            ((1 + matrixHornerP3ScalarRoundoffFactor fp n) ^
                (rest.length + 1) * (1 + rho) - 1) := by
        dsimp [rho', r]
        rw [pow_succ]
        ring
      have harg :
          eta' * infNorm X ^ rest.length +
              matrixPolyP3InfNormMajorant n X rest =
            eta * infNorm X ^ (rest.length + 1) +
              matrixPolyP3InfNormMajorant n X (A :: rest) := by
        dsimp [eta']
        simp [matrixPolyP3InfNormMajorant, polyDesc]
        ring
      calc
        matrixHornerP3ScalarInfForwardBudgetFrom fp n X eta mu (A :: rest)
            =
              matrixHornerP3ScalarInfForwardBudgetFrom fp n X eta' mu' rest := by
            simp [matrixHornerP3ScalarInfForwardBudgetFrom, eta', mu', step]
        _ ≤
            ((1 + matrixHornerP3ScalarRoundoffFactor fp n) ^
                  rest.length * (1 + rho') - 1) *
              (eta' * infNorm X ^ rest.length +
                matrixPolyP3InfNormMajorant n X rest) := hrec
        _ =
            ((1 + matrixHornerP3ScalarRoundoffFactor fp n) ^
                  (A :: rest).length * (1 + rho) - 1) *
              (eta * infNorm X ^ (A :: rest).length +
                matrixPolyP3InfNormMajorant n X (A :: rest)) := by
            rw [List.length_cons, hcoef, harg]

theorem matrixHornerP3ScalarOneNormForwardBudgetFrom_le_geometric_majorant
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n) :
    ∀ (rest : List (Fin n → Fin n → ℝ)) (eta mu rho : ℝ),
      0 ≤ eta →
      0 ≤ mu →
      0 ≤ rho →
      mu ≤ rho * eta →
      matrixHornerP3ScalarOneNormForwardBudgetFrom fp n X eta mu rest ≤
        (((1 + matrixHornerP3ScalarRoundoffFactor fp n) ^ rest.length) *
            (1 + rho) - 1) *
          (eta * oneNorm X ^ rest.length +
            matrixPolyP3OneNormMajorant n X rest) := by
  intro rest
  induction rest with
  | nil =>
      intro eta mu rho _heta _hmu _hrho hmu_le
      simpa [matrixHornerP3ScalarOneNormForwardBudgetFrom,
        matrixPolyP3OneNormMajorant, polyDesc] using hmu_le
  | cons A rest ih =>
      intro eta mu rho heta hmu hrho hmu_le
      let r := matrixHornerP3ScalarRoundoffFactor fp n
      let eta' := eta * oneNorm X + oneNorm A
      let step := matrixHornerP3ScalarOneNormStepBudget fp n X eta mu A
      let mu' := step + mu * oneNorm X
      let rho' := (1 + r) * (1 + rho) - 1
      have hr : 0 ≤ r := by
        simpa [r] using matrixHornerP3ScalarRoundoffFactor_nonneg fp n hn
      have hX : 0 ≤ oneNorm X := oneNorm_nonneg X
      have hA : 0 ≤ oneNorm A := oneNorm_nonneg A
      have heta' : 0 ≤ eta' := by
        exact add_nonneg (mul_nonneg heta hX) hA
      have hstep_nonneg : 0 ≤ step := by
        have hsum : 0 ≤ eta + mu := add_nonneg heta hmu
        have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
        have honeγ : 0 ≤ 1 + gamma fp n := by linarith
        have hinside :
            0 ≤ (1 + gamma fp n) * (eta + mu) * oneNorm X +
              oneNorm A := by
          exact add_nonneg
            (mul_nonneg (mul_nonneg honeγ hsum) hX)
            hA
        have htail :
            0 ≤ gamma fp n * (eta + mu) * oneNorm X :=
          mul_nonneg (mul_nonneg hγ hsum) hX
        simpa [step, matrixHornerP3ScalarOneNormStepBudget] using
          add_nonneg (mul_nonneg fp.u_nonneg hinside) htail
      have hmu' : 0 ≤ mu' := by
        exact add_nonneg hstep_nonneg (mul_nonneg hmu hX)
      have hstep_le :
          step ≤ r * ((eta + mu) * oneNorm X + oneNorm A) := by
        simpa [step, r] using
          matrixHornerP3ScalarOneNormStepBudget_le_factor
            fp n X eta mu A hn
      have hsum_le :
          (eta + mu) * oneNorm X + oneNorm A ≤
            (eta + rho * eta) * oneNorm X + oneNorm A := by
        have hbase : eta + mu ≤ eta + rho * eta :=
          add_le_add le_rfl hmu_le
        exact add_le_add (mul_le_mul_of_nonneg_right hbase hX) le_rfl
      have hstep_le_rho :
          step ≤ r * ((eta + rho * eta) * oneNorm X + oneNorm A) :=
        le_trans hstep_le (mul_le_mul_of_nonneg_left hsum_le hr)
      have hmu_x_le :
          mu * oneNorm X ≤ rho * eta * oneNorm X :=
        mul_le_mul_of_nonneg_right hmu_le hX
      have hr_le_rho' : r ≤ rho' := by
        have hprod : 0 ≤ r * rho := mul_nonneg hr hrho
        dsimp [rho']
        nlinarith
      have hrho' : 0 ≤ rho' := le_trans hr hr_le_rho'
      have hmu'_le : mu' ≤ rho' * eta' := by
        calc
          mu'
              = step + mu * oneNorm X := rfl
          _ ≤
              r * ((eta + rho * eta) * oneNorm X + oneNorm A) +
                rho * eta * oneNorm X :=
              add_le_add hstep_le_rho hmu_x_le
          _ =
              rho' * (eta * oneNorm X) + r * oneNorm A := by
              dsimp [rho']
              ring
          _ ≤ rho' * (eta * oneNorm X) + rho' * oneNorm A :=
              add_le_add le_rfl (mul_le_mul_of_nonneg_right hr_le_rho' hA)
          _ = rho' * eta' := by
              dsimp [eta']
              ring
      have hrec :=
        ih eta' mu' rho' heta' hmu' hrho' hmu'_le
      have hcoef :
          ((1 + matrixHornerP3ScalarRoundoffFactor fp n) ^ rest.length *
                (1 + rho') - 1) =
            ((1 + matrixHornerP3ScalarRoundoffFactor fp n) ^
                (rest.length + 1) * (1 + rho) - 1) := by
        dsimp [rho', r]
        rw [pow_succ]
        ring
      have harg :
          eta' * oneNorm X ^ rest.length +
              matrixPolyP3OneNormMajorant n X rest =
            eta * oneNorm X ^ (rest.length + 1) +
              matrixPolyP3OneNormMajorant n X (A :: rest) := by
        dsimp [eta']
        simp [matrixPolyP3OneNormMajorant, polyDesc]
        ring
      calc
        matrixHornerP3ScalarOneNormForwardBudgetFrom fp n X eta mu (A :: rest)
            =
              matrixHornerP3ScalarOneNormForwardBudgetFrom fp n X eta' mu' rest := by
            simp [matrixHornerP3ScalarOneNormForwardBudgetFrom, eta', mu',
              step]
        _ ≤
            ((1 + matrixHornerP3ScalarRoundoffFactor fp n) ^
                  rest.length * (1 + rho') - 1) *
              (eta' * oneNorm X ^ rest.length +
                matrixPolyP3OneNormMajorant n X rest) := hrec
        _ =
            ((1 + matrixHornerP3ScalarRoundoffFactor fp n) ^
                  (A :: rest).length * (1 + rho) - 1) *
              (eta * oneNorm X ^ (A :: rest).length +
                matrixPolyP3OneNormMajorant n X (A :: rest)) := by
            rw [List.length_cons, hcoef, harg]

theorem matrixHornerP3ScalarInfForwardBudget_le_geometric_majorant
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ))
    (hn : gammaValid fp n) :
    matrixHornerP3ScalarInfForwardBudget fp n X coeffsDesc ≤
      (((1 + matrixHornerP3ScalarRoundoffFactor fp n) ^
          (coeffsDesc.length - 1)) - 1) *
        matrixPolyP3InfNormMajorant n X coeffsDesc := by
  cases coeffsDesc with
  | nil =>
      simp [matrixHornerP3ScalarInfForwardBudget,
        matrixPolyP3InfNormMajorant, polyDesc]
  | cons A rest =>
      have h :=
        matrixHornerP3ScalarInfForwardBudgetFrom_le_geometric_majorant
          fp n X hn rest (infNorm A) 0 0
          (infNorm_nonneg A) (by norm_num) (by norm_num) (by simp)
      simpa [matrixHornerP3ScalarInfForwardBudget,
        matrixPolyP3InfNormMajorant, polyDesc] using h

theorem matrixHornerP3ScalarOneNormForwardBudget_le_geometric_majorant
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ))
    (hn : gammaValid fp n) :
    matrixHornerP3ScalarOneNormForwardBudget fp n X coeffsDesc ≤
      (((1 + matrixHornerP3ScalarRoundoffFactor fp n) ^
          (coeffsDesc.length - 1)) - 1) *
        matrixPolyP3OneNormMajorant n X coeffsDesc := by
  cases coeffsDesc with
  | nil =>
      simp [matrixHornerP3ScalarOneNormForwardBudget,
        matrixPolyP3OneNormMajorant, polyDesc]
  | cons A rest =>
      have h :=
        matrixHornerP3ScalarOneNormForwardBudgetFrom_le_geometric_majorant
          fp n X hn rest (oneNorm A) 0 0
          (oneNorm_nonneg A) (by norm_num) (by norm_num) (by simp)
      simpa [matrixHornerP3ScalarOneNormForwardBudget,
        matrixPolyP3OneNormMajorant, polyDesc] using h

/-- Higher-order remainder after extracting the source first-order coefficient
`degree*(n+1)u` from the matrix-Horner geometric budget factor. -/
noncomputable def matrixHornerP3GeometricFirstOrderRemainder
    (fp : FPModel) (n degree : ℕ) : ℝ :=
  (degree : ℝ) * matrixHornerP3ScalarRoundoffFactorRemainder fp n +
    (((1 + matrixHornerP3ScalarRoundoffFactor fp n) ^ degree - 1) -
      (degree : ℝ) * matrixHornerP3ScalarRoundoffFactor fp n)

theorem matrixHornerP3GeometricFactor_eq_first_order_add_remainder
    (fp : FPModel) (n degree : ℕ) (hn : gammaValid fp n) :
    ((1 + matrixHornerP3ScalarRoundoffFactor fp n) ^ degree - 1) =
      (degree : ℝ) * (((n : ℝ) + 1) * fp.u) +
        matrixHornerP3GeometricFirstOrderRemainder fp n degree := by
  unfold matrixHornerP3GeometricFirstOrderRemainder
  rw [matrixHornerP3ScalarRoundoffFactor_eq_first_order_add_remainder
    fp n hn]
  ring

theorem matrixHornerP3GeometricFirstOrderRemainder_eq_zero_of_u_eq_zero
    (fp : FPModel) (n degree : ℕ) (hu : fp.u = 0) :
    matrixHornerP3GeometricFirstOrderRemainder fp n degree = 0 := by
  simp [matrixHornerP3GeometricFirstOrderRemainder,
    matrixHornerP3ScalarRoundoffFactorRemainder,
    matrixHornerP3ScalarRoundoffFactor, gamma, hu]

theorem fl_matrixHornerP3Fold_infNorm_le_acc_majorant_add_budget_from
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (rest : List (Fin n → Fin n → ℝ))
    (Yhat Y : Fin n → Fin n → ℝ) (mu : ℝ)
    (hnpos : 0 < n) (hn : gammaValid fp n)
    (hmu : 0 ≤ mu)
    (herr : infNorm (fun i j => Yhat i j - Y i j) ≤ mu) :
    infNorm (rest.foldl (fl_matrixHornerP3Step fp n X) Yhat) ≤
      infNorm Y * infNorm X ^ rest.length +
        matrixPolyP3InfNormMajorant n X rest +
        matrixHornerP3ForwardInfErrorBudgetFrom fp n X Yhat mu rest := by
  have htri :=
    infNorm_le_sub_add
      (rest.foldl (fl_matrixHornerP3Step fp n X) Yhat)
      (rest.foldl (matrixHornerP3Step n X) Y)
  have herr_fold :=
    fl_matrixHornerP3Fold_infNorm_error_bound_from
      fp n X hnpos hn rest Yhat Y mu hmu herr
  have hexact :=
    matrixHornerP3Fold_infNorm_le_acc_majorant n X Y rest hnpos
  calc
    infNorm (rest.foldl (fl_matrixHornerP3Step fp n X) Yhat)
        ≤
          infNorm
            (fun i j =>
              rest.foldl (fl_matrixHornerP3Step fp n X) Yhat i j -
                rest.foldl (matrixHornerP3Step n X) Y i j) +
            infNorm (rest.foldl (matrixHornerP3Step n X) Y) := htri
    _ ≤
          matrixHornerP3ForwardInfErrorBudgetFrom fp n X Yhat mu rest +
            (infNorm Y * infNorm X ^ rest.length +
              matrixPolyP3InfNormMajorant n X rest) :=
        add_le_add herr_fold hexact
    _ =
          infNorm Y * infNorm X ^ rest.length +
            matrixPolyP3InfNormMajorant n X rest +
            matrixHornerP3ForwardInfErrorBudgetFrom fp n X Yhat mu rest := by
        ring

theorem fl_matrixHornerP3Fold_oneNorm_le_acc_majorant_add_budget_from
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (rest : List (Fin n → Fin n → ℝ))
    (Yhat Y : Fin n → Fin n → ℝ) (mu : ℝ)
    (hn : gammaValid fp n)
    (hmu : 0 ≤ mu)
    (herr : oneNorm (fun i j => Yhat i j - Y i j) ≤ mu) :
    oneNorm (rest.foldl (fl_matrixHornerP3Step fp n X) Yhat) ≤
      oneNorm Y * oneNorm X ^ rest.length +
        matrixPolyP3OneNormMajorant n X rest +
        matrixHornerP3ForwardOneNormErrorBudgetFrom fp n X Yhat mu rest := by
  have htri :=
    oneNorm_le_sub_add
      (rest.foldl (fl_matrixHornerP3Step fp n X) Yhat)
      (rest.foldl (matrixHornerP3Step n X) Y)
  have herr_fold :=
    fl_matrixHornerP3Fold_oneNorm_error_bound_from
      fp n X hn rest Yhat Y mu hmu herr
  have hexact :=
    matrixHornerP3Fold_oneNorm_le_acc_majorant n X Y rest
  calc
    oneNorm (rest.foldl (fl_matrixHornerP3Step fp n X) Yhat)
        ≤
          oneNorm
            (fun i j =>
              rest.foldl (fl_matrixHornerP3Step fp n X) Yhat i j -
                rest.foldl (matrixHornerP3Step n X) Y i j) +
            oneNorm (rest.foldl (matrixHornerP3Step n X) Y) := htri
    _ ≤
          matrixHornerP3ForwardOneNormErrorBudgetFrom fp n X Yhat mu rest +
            (oneNorm Y * oneNorm X ^ rest.length +
              matrixPolyP3OneNormMajorant n X rest) :=
        add_le_add herr_fold hexact
    _ =
          oneNorm Y * oneNorm X ^ rest.length +
            matrixPolyP3OneNormMajorant n X rest +
            matrixHornerP3ForwardOneNormErrorBudgetFrom fp n X Yhat mu rest := by
        ring

theorem fl_matrixHornerP3Desc_infNorm_error_bound_to_matrixPolyP3Desc
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ))
    (hnpos : 0 < n) (hn : gammaValid fp n) :
    infNorm
        (fun i j =>
          fl_matrixHornerP3Desc fp n X coeffsDesc i j -
            matrixPolyP3Desc n X coeffsDesc i j) ≤
      matrixHornerP3ForwardInfErrorBudget fp n X coeffsDesc := by
  rw [← matrixHornerP3Desc_eq_matrixPolyP3Desc n X coeffsDesc]
  exact fl_matrixHornerP3Desc_infNorm_error_bound
    fp n X coeffsDesc hnpos hn

theorem fl_matrixHornerP3Desc_oneNorm_error_bound_to_matrixPolyP3Desc
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ))
    (hn : gammaValid fp n) :
    oneNorm
        (fun i j =>
          fl_matrixHornerP3Desc fp n X coeffsDesc i j -
            matrixPolyP3Desc n X coeffsDesc i j) ≤
      matrixHornerP3ForwardOneNormErrorBudget fp n X coeffsDesc := by
  rw [← matrixHornerP3Desc_eq_matrixPolyP3Desc n X coeffsDesc]
  exact fl_matrixHornerP3Desc_oneNorm_error_bound
    fp n X coeffsDesc hn

theorem fl_matrixHornerP3Desc_infNorm_le_majorant_add_budget
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ))
    (hnpos : 0 < n) (hn : gammaValid fp n) :
    infNorm (fl_matrixHornerP3Desc fp n X coeffsDesc) ≤
      matrixPolyP3InfNormMajorant n X coeffsDesc +
        matrixHornerP3ForwardInfErrorBudget fp n X coeffsDesc := by
  have htri :=
    infNorm_le_sub_add
      (fl_matrixHornerP3Desc fp n X coeffsDesc)
      (matrixHornerP3Desc n X coeffsDesc)
  have herr :=
    fl_matrixHornerP3Desc_infNorm_error_bound
      fp n X coeffsDesc hnpos hn
  have hexact :
      infNorm (matrixHornerP3Desc n X coeffsDesc) ≤
        matrixPolyP3InfNormMajorant n X coeffsDesc := by
    rw [matrixHornerP3Desc_eq_matrixPolyP3Desc n X coeffsDesc]
    exact matrixPolyP3Desc_infNorm_le_majorant n X coeffsDesc hnpos
  calc
    infNorm (fl_matrixHornerP3Desc fp n X coeffsDesc)
        ≤
          infNorm
            (fun i j =>
              fl_matrixHornerP3Desc fp n X coeffsDesc i j -
                matrixHornerP3Desc n X coeffsDesc i j) +
            infNorm (matrixHornerP3Desc n X coeffsDesc) := htri
    _ ≤
          matrixHornerP3ForwardInfErrorBudget fp n X coeffsDesc +
            matrixPolyP3InfNormMajorant n X coeffsDesc :=
        add_le_add herr hexact
    _ =
          matrixPolyP3InfNormMajorant n X coeffsDesc +
            matrixHornerP3ForwardInfErrorBudget fp n X coeffsDesc := by
        ring

theorem fl_matrixHornerP3Desc_oneNorm_le_majorant_add_budget
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ))
    (hn : gammaValid fp n) :
    oneNorm (fl_matrixHornerP3Desc fp n X coeffsDesc) ≤
      matrixPolyP3OneNormMajorant n X coeffsDesc +
        matrixHornerP3ForwardOneNormErrorBudget fp n X coeffsDesc := by
  have htri :=
    oneNorm_le_sub_add
      (fl_matrixHornerP3Desc fp n X coeffsDesc)
      (matrixHornerP3Desc n X coeffsDesc)
  have herr :=
    fl_matrixHornerP3Desc_oneNorm_error_bound
      fp n X coeffsDesc hn
  have hexact :
      oneNorm (matrixHornerP3Desc n X coeffsDesc) ≤
        matrixPolyP3OneNormMajorant n X coeffsDesc := by
    rw [matrixHornerP3Desc_eq_matrixPolyP3Desc n X coeffsDesc]
    exact matrixPolyP3Desc_oneNorm_le_majorant n X coeffsDesc
  calc
    oneNorm (fl_matrixHornerP3Desc fp n X coeffsDesc)
        ≤
          oneNorm
            (fun i j =>
              fl_matrixHornerP3Desc fp n X coeffsDesc i j -
                matrixHornerP3Desc n X coeffsDesc i j) +
            oneNorm (matrixHornerP3Desc n X coeffsDesc) := htri
    _ ≤
          matrixHornerP3ForwardOneNormErrorBudget fp n X coeffsDesc +
            matrixPolyP3OneNormMajorant n X coeffsDesc :=
        add_le_add herr hexact
    _ =
          matrixPolyP3OneNormMajorant n X coeffsDesc +
            matrixHornerP3ForwardOneNormErrorBudget fp n X coeffsDesc := by
        ring

theorem matrixPolynomialP3_horner_infNorm_error_bound_of_budget_le_majorant
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ))
    (C : ℝ) (hnpos : 0 < n) (hn : gammaValid fp n)
    (hbudget :
      matrixHornerP3ForwardInfErrorBudget fp n X coeffsDesc ≤
        C * matrixPolyP3InfNormMajorant n X coeffsDesc) :
    infNorm
        (fun i j =>
          fl_matrixHornerP3Desc fp n X coeffsDesc i j -
            matrixPolyP3Desc n X coeffsDesc i j) ≤
      C * matrixPolyP3InfNormMajorant n X coeffsDesc := by
  exact le_trans
    (fl_matrixHornerP3Desc_infNorm_error_bound_to_matrixPolyP3Desc
      fp n X coeffsDesc hnpos hn)
    hbudget

theorem matrixPolynomialP3_horner_oneNorm_error_bound_of_budget_le_majorant
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ))
    (C : ℝ) (hn : gammaValid fp n)
    (hbudget :
      matrixHornerP3ForwardOneNormErrorBudget fp n X coeffsDesc ≤
        C * matrixPolyP3OneNormMajorant n X coeffsDesc) :
    oneNorm
        (fun i j =>
          fl_matrixHornerP3Desc fp n X coeffsDesc i j -
            matrixPolyP3Desc n X coeffsDesc i j) ≤
      C * matrixPolyP3OneNormMajorant n X coeffsDesc := by
  exact le_trans
    (fl_matrixHornerP3Desc_oneNorm_error_bound_to_matrixPolyP3Desc
      fp n X coeffsDesc hn)
    hbudget

theorem matrixPolynomialP3_horner_infNorm_error_bound_of_scalar_budget_le_majorant
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ))
    (C : ℝ) (hnpos : 0 < n) (hn : gammaValid fp n)
    (hbudget :
      matrixHornerP3ScalarInfForwardBudget fp n X coeffsDesc ≤
        C * matrixPolyP3InfNormMajorant n X coeffsDesc) :
    infNorm
        (fun i j =>
          fl_matrixHornerP3Desc fp n X coeffsDesc i j -
            matrixPolyP3Desc n X coeffsDesc i j) ≤
      C * matrixPolyP3InfNormMajorant n X coeffsDesc := by
  exact
    matrixPolynomialP3_horner_infNorm_error_bound_of_budget_le_majorant
      fp n X coeffsDesc C hnpos hn
      (le_trans
        (matrixHornerP3ForwardInfErrorBudget_le_scalar
          fp n X coeffsDesc hnpos hn)
        hbudget)

theorem matrixPolynomialP3_horner_oneNorm_error_bound_of_scalar_budget_le_majorant
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ))
    (C : ℝ) (hn : gammaValid fp n)
    (hbudget :
      matrixHornerP3ScalarOneNormForwardBudget fp n X coeffsDesc ≤
        C * matrixPolyP3OneNormMajorant n X coeffsDesc) :
    oneNorm
        (fun i j =>
          fl_matrixHornerP3Desc fp n X coeffsDesc i j -
            matrixPolyP3Desc n X coeffsDesc i j) ≤
      C * matrixPolyP3OneNormMajorant n X coeffsDesc := by
  exact
    matrixPolynomialP3_horner_oneNorm_error_bound_of_budget_le_majorant
      fp n X coeffsDesc C hn
      (le_trans
        (matrixHornerP3ForwardOneNormErrorBudget_le_scalar
          fp n X coeffsDesc hn)
        hbudget)

theorem matrixPolynomialP3_horner_infNorm_error_bound_geometric
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ))
    (hnpos : 0 < n) (hn : gammaValid fp n) :
    infNorm
        (fun i j =>
          fl_matrixHornerP3Desc fp n X coeffsDesc i j -
            matrixPolyP3Desc n X coeffsDesc i j) ≤
      (((1 + matrixHornerP3ScalarRoundoffFactor fp n) ^
          (coeffsDesc.length - 1)) - 1) *
        matrixPolyP3InfNormMajorant n X coeffsDesc := by
  exact
    matrixPolynomialP3_horner_infNorm_error_bound_of_scalar_budget_le_majorant
      fp n X coeffsDesc
      (((1 + matrixHornerP3ScalarRoundoffFactor fp n) ^
          (coeffsDesc.length - 1)) - 1)
      hnpos hn
      (matrixHornerP3ScalarInfForwardBudget_le_geometric_majorant
        fp n X coeffsDesc hn)

theorem matrixPolynomialP3_horner_oneNorm_error_bound_geometric
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ))
    (hn : gammaValid fp n) :
    oneNorm
        (fun i j =>
          fl_matrixHornerP3Desc fp n X coeffsDesc i j -
            matrixPolyP3Desc n X coeffsDesc i j) ≤
      (((1 + matrixHornerP3ScalarRoundoffFactor fp n) ^
          (coeffsDesc.length - 1)) - 1) *
        matrixPolyP3OneNormMajorant n X coeffsDesc := by
  exact
    matrixPolynomialP3_horner_oneNorm_error_bound_of_scalar_budget_le_majorant
      fp n X coeffsDesc
      (((1 + matrixHornerP3ScalarRoundoffFactor fp n) ^
          (coeffsDesc.length - 1)) - 1)
      hn
      (matrixHornerP3ScalarOneNormForwardBudget_le_geometric_majorant
        fp n X coeffsDesc hn)

theorem matrixPolynomialP3_horner_infNorm_error_bound_first_order_remainder
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ))
    (hnpos : 0 < n) (hn : gammaValid fp n) :
    infNorm
        (fun i j =>
          fl_matrixHornerP3Desc fp n X coeffsDesc i j -
            matrixPolyP3Desc n X coeffsDesc i j) ≤
      (((coeffsDesc.length - 1 : ℕ) : ℝ) *
          (((n : ℝ) + 1) * fp.u) +
        matrixHornerP3GeometricFirstOrderRemainder
          fp n (coeffsDesc.length - 1)) *
        matrixPolyP3InfNormMajorant n X coeffsDesc := by
  have h :=
    matrixPolynomialP3_horner_infNorm_error_bound_geometric
      fp n X coeffsDesc hnpos hn
  rw [matrixHornerP3GeometricFactor_eq_first_order_add_remainder
    fp n (coeffsDesc.length - 1) hn] at h
  simpa using h

theorem matrixPolynomialP3_horner_oneNorm_error_bound_first_order_remainder
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ))
    (hn : gammaValid fp n) :
    oneNorm
        (fun i j =>
          fl_matrixHornerP3Desc fp n X coeffsDesc i j -
            matrixPolyP3Desc n X coeffsDesc i j) ≤
      (((coeffsDesc.length - 1 : ℕ) : ℝ) *
          (((n : ℝ) + 1) * fp.u) +
        matrixHornerP3GeometricFirstOrderRemainder
          fp n (coeffsDesc.length - 1)) *
        matrixPolyP3OneNormMajorant n X coeffsDesc := by
  have h :=
    matrixPolynomialP3_horner_oneNorm_error_bound_geometric
      fp n X coeffsDesc hn
  rw [matrixHornerP3GeometricFactor_eq_first_order_add_remainder
    fp n (coeffsDesc.length - 1) hn] at h
  simpa using h

end NumStability
