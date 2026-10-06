import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LinearSystems.LU.NonsymmetricPositiveDefinite.Basic
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.Rounding
import NumStability.Analysis.SubtractionFold
import NumStability.Analysis.Summation.ErrorBounds
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter09.Problems
import NumStability.Source.Higham.Chapter09.Section01
import NumStability.Source.Higham.Chapter09.Section02
import NumStability.Source.Higham.Chapter09.Section03
import NumStability.Source.Higham.Chapter09.Section04
import NumStability.Source.Higham.Chapter09.Section05
import NumStability.Source.Higham.Chapter09.Section06
import NumStability.Source.Higham.Chapter09.Section08
import NumStability.Source.Higham.Chapter09.Section10
import NumStability.Source.Higham.Chapter09.Section11
import NumStability.Source.Higham.Chapter10.Section02.ErrorAnalysis.Basic

/-!
# Chapter10 Section04 PositiveDefiniteSymmetricPart Endpoints

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapter10` by wave W03 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- **Equation (10.29)** setup: `A = A_S + A_K`, symmetric and skew-symmetric
parts. -/
theorem higham10_29_symmetric_skew_decomposition (n : ℕ)
    (A : Fin n → Fin n → ℝ) :
    ∀ i j : Fin n, A i j = symmetricPart n A i j + skewSymmetricPart n A i j :=
  symmetric_skew_decomposition n A

/-- **Section 10.4** equivalence: nonsymmetric positive definiteness is the
same as SPD of the symmetric part. -/
theorem higham10_29_nonsymPosDef_iff_symPartSPD (n : ℕ)
    (A : Fin n → Fin n → ℝ) :
    higham10_4_IsNonsymPosDef n A ↔ IsSymPosDef n (symmetricPart n A) :=
  nonsymPosDef_iff_symPartSPD n A

/-- **(10.29) GE recursion is well-founded for nonsymmetric-positive-definite
    matrices** (Higham §10.4): the LU-recursion Schur complement
    `luFirstSchurComplement A = D − c bᵀ/α` of a nonsym-PD matrix is again
    nonsym-PD.  This is exactly the class-closure `nonsym_pd_first_ge_schur`,
    now stated on the `GaussianElimination` scaffold's Schur step, so the
    unpivoted GE/LU recursion (`LUFactSpec.of_firstSchurComplement`) stays in
    the nonsym-PD class at every stage — the base for the (10.29) `‖|L||U|‖_F`
    stage induction. -/
theorem higham10_29_luFirstSchurComplement_isNonsymPosDef {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hA : higham10_4_IsNonsymPosDef (m + 1) A) :
    higham10_4_IsNonsymPosDef m (luFirstSchurComplement A) :=
  nonsym_pd_first_ge_schur hA

/-- **(10.29) symmetric part of the Schur complement** (Higham §10.4;
    oracle consult 4's `Ĥ = Z + kkᵀ/α`): the symmetric part of the LU
    Schur complement equals the Schur complement of the symmetric part
    (`Z`) plus a rank-one term in the skew off-diagonal `k = (b − c)/2`.
    This identifies the `Ĥ` matrix that the stage inequality
    `schur_gram_stage_le` inverts. -/
theorem higham10_29_symPart_luSchur_eq {m : ℕ}
    (S : Fin (m + 1) → Fin (m + 1) → ℝ) (i j : Fin m) :
    symmetricPart m (luFirstSchurComplement S) i j =
      (symmetricPart (m + 1) S i.succ j.succ -
        symmetricPart (m + 1) S i.succ 0 *
          symmetricPart (m + 1) S 0 j.succ / S 0 0) +
      ((S 0 i.succ - S i.succ 0) / 2) *
        ((S 0 j.succ - S j.succ 0) / 2) / S 0 0 := by
  simp only [symmetricPart, luFirstSchurComplement]
  ring

/-- **(10.29) parent action on a zero-padded vector** (Higham §10.4):
    `S·(0,y) = (bᵀy, Dy)` — applying the parent stage matrix `S` to the
    padded vector `(0,y)` gives the pair of the border inner product and
    the interior action, i.e. `Fin.cons (∑ b_j y_j) (Dy)`.  This is the
    `(β, v)` at which `schur_gram_stage_le` is evaluated. -/
theorem higham10_29_S_mulVec_cons0 {m : ℕ}
    (S : Fin (m + 1) → Fin (m + 1) → ℝ) (y : Fin m → ℝ) :
    matMulVec (m + 1) S (Fin.cons (0 : ℝ) y) =
      Fin.cons (∑ j : Fin m, S 0 j.succ * y j)
        (fun i => ∑ j : Fin m, S i.succ j.succ * y j) := by
  funext i
  refine Fin.cases ?_ (fun i' => ?_) i
  · -- index 0
    show matMulVec (m + 1) S (Fin.cons (0 : ℝ) y) 0 = _
    unfold matMulVec
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, mul_zero, zero_add]
  · -- index i'.succ
    show matMulVec (m + 1) S (Fin.cons (0 : ℝ) y) i'.succ = _
    unfold matMulVec
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, mul_zero, zero_add]

/-- **(10.29) Schur-complement action** (Higham §10.4): the LU Schur
    complement acts as `Ŝy = Dy − (c/α)·(bᵀy)`.  Since the free `f − k`
    of `schur_gram_stage_le` instantiates to `c = S_{·,0}`, this is
    exactly that lemma's left-hand vector at `β = bᵀy`, `v = Dy`. -/
theorem higham10_29_luSchur_mulVec {m : ℕ}
    (S : Fin (m + 1) → Fin (m + 1) → ℝ) (y : Fin m → ℝ) (i : Fin m) :
    matMulVec m (luFirstSchurComplement S) y i =
      (∑ j : Fin m, S i.succ j.succ * y j) -
        S i.succ 0 / S 0 0 * (∑ j : Fin m, S 0 j.succ * y j) := by
  unfold matMulVec luFirstSchurComplement
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Equation (10.29)** / Golub-Van Loan growth-bound interface for exact
LU factors of a nonsymmetric positive-definite matrix. -/
theorem higham10_29_nonsym_pd_lu_growth_bound (n : ℕ) (hn : 0 < n)
    (A L U : Fin n → Fin n → ℝ)
    (hPD : higham10_4_IsNonsymPosDef n A)
    (hLU : LUFactSpec n A L U)
    (κ_AS : ℝ) (hκ : 0 ≤ κ_AS)
    (hbound : frobNormSq (fun i j => ∑ k : Fin n, |L i k| * |U k j|) ≤
      ↑n * κ_AS * frobNormSq A) :
    frobNormSq (fun i j => ∑ k : Fin n, |L i k| * |U k j|) ≤
      ↑n * κ_AS * frobNormSq A :=
  nonsym_pd_lu_growth_bound n hn A L U hPD hLU κ_AS hκ hbound

end NumStability
