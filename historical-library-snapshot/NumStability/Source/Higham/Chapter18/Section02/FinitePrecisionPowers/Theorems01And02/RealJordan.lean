import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.MatrixPowers.ComputedIteration.Model
import NumStability.Analysis.LinearOperators.MatrixPowers.JordanScaling.RealJordan
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter18.Section02.FinitePrecisionPowers.Theorems01And02.RealCases

/-!
# Source.Higham.Chapter18.Section02.FinitePrecisionPowers.Theorems01And02.RealJordan

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

-- Algorithms/MatrixPowersJordan.lean
--
-- Higham Chapter 18: Error analysis of matrix powers — the defective
-- real-spectrum case of Theorem 18.1 (Higham–Knight).
--
-- Discharges `JordanFormSpec.similarity_absorbs` for real Jordan-form data
-- with block size t ≥ 2 via the δ-scaling construction of the book's proof
-- (Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §18.2,
-- pp. 347–348): S = X·D with D = diag(p_i), p_i = β^(run length at i),
-- β = (1−ρ)(t−1)/t, together with the (1+1/m)^m < e < 4 optimisation that
-- turns the printed condition 4t·η·κ∞(X)·‖A‖∞ < (1−ρ)^t into a per-step
-- contraction ‖S⁻¹(A+ΔA)S‖∞ ≤ q < 1.












namespace NumStability

open scoped BigOperators

-- ============================================================
-- Scalar preliminaries: the (1 + 1/m)^m < e < 4 optimisation
-- ============================================================






















































-- ============================================================
-- The scaling margin β = (1−ρ)(t−1)/t of the δ-scaling construction
-- ============================================================








































































-- ============================================================
-- Diagonal scaling matrices: inverse, entries, norms
-- ============================================================



































-- ============================================================
-- The scaled bidiagonal row-sum bound ‖D⁻¹ J D‖∞ ≤ ρ + β
-- ============================================================






































































































-- ============================================================
-- Run lengths of superdiagonal 1-chains and the scaling vector
-- ============================================================
























































-- ============================================================
-- Theorem 18.1: discharged t ≥ 2 construction (real Jordan data)
-- ============================================================









































































































































































































-- ============================================================
-- Theorem 18.1: axiom-free end-to-end forms (real Jordan data)
-- ============================================================

/-- **Axiom-free real-spectrum Jordan case of Theorem 18.1** (limit form,
    abstract error model) — Higham, Accuracy and Stability of Numerical
    Algorithms, 2nd ed., §18.2, Theorem 18.1 (pp. 347–348).

    If `X⁻¹AX = J` is upper bidiagonal with `|J_{ii}| ≤ ρ < 1`, superdiagonal
    entries of modulus ≤ 1, every run of consecutive nonzero superdiagonal
    entries of length ≤ `t − 1` (max Jordan block size ≤ `t`, via
    `jordanRunLength`), and the Higham–Knight condition (18.13)
    `4t·c·κ∞(X)·‖A‖∞ < (1−ρ)^t` holds, then any computed-power sequence with
    per-step componentwise budget `c` satisfies `‖v_m‖∞ → 0`.

    No `similarity_absorbs` assumption: `t = 1` dispatches to the diagonal
    construction (`JordanFormSpec.ofRealDiagonal`) and `t ≥ 2` to the
    δ-scaling construction (`JordanFormSpec.ofRealJordan` with the scaling
    vector from `exists_jordan_scaling_vector`).  Honest scope: real-spectrum
    Jordan data; the complex/defective-over-ℂ case is not covered. -/
theorem higham_18_1_real_jordan_tendsto (n : ℕ) (hn : 0 < n)
    (A X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv)
    (hsim : matMul n X_inv (matMul n A X) = J)
    (hshape : ∀ i j : Fin n, (j : ℕ) ≠ (i : ℕ) → (j : ℕ) ≠ (i : ℕ) + 1 → J i j = 0)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hdiagbd : ∀ i, |J i i| ≤ ρ)
    (hsup : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → |J i j| ≤ 1)
    (t : ℕ) (ht1 : 1 ≤ t)
    (hrun : ∀ k, jordanRunLength n J k ≤ t - 1)
    (v : ℕ → (Fin n → ℝ)) (c : ℝ) (hc : 0 ≤ c)
    (hComp : ComputedMatPowVec n A v c)
    (hCond : 4 * (t : ℝ) * c * (infNorm X * infNorm X_inv) * infNorm A
      < (1 - ρ) ^ t) :
    Filter.Tendsto (fun m => infNormVec (v m)) Filter.atTop (nhds 0) := by
  rcases Nat.lt_or_ge t 2 with ht | ht2
  · -- t = 1: the run bound forces J diagonal; use the diagonal construction.
    have ht1' : t = 1 := by omega
    subst ht1'
    have hdiag : ∀ i j : Fin n, i ≠ j → J i j = 0 := by
      intro i j hij
      by_cases hj : (j : ℕ) = (i : ℕ) + 1
      · by_contra hJ
        have hlt : (i : ℕ) + 1 < n := by
          have hjn := j.isLt
          omega
        have hieq : (⟨(i : ℕ), Nat.lt_of_succ_lt hlt⟩ : Fin n) = i :=
          Fin.eq_of_val_eq rfl
        have hjeq : (⟨(i : ℕ) + 1, hlt⟩ : Fin n) = j :=
          Fin.eq_of_val_eq hj.symm
        have hJ' : J ⟨(i : ℕ), Nat.lt_of_succ_lt hlt⟩
            ⟨(i : ℕ) + 1, hlt⟩ ≠ 0 := by
          rw [hieq, hjeq]
          exact hJ
        have hstep := jordanRunLength_succ n J (i : ℕ) hlt hJ'
        have hbound := hrun ((i : ℕ) + 1)
        omega
      · apply hshape i j _ hj
        exact fun h => hij (Fin.eq_of_val_eq h.symm)
    have hCond' : 4 * c * (infNorm X * infNorm X_inv) * infNorm A < 1 - ρ := by
      have h := hCond
      rw [pow_one, Nat.cast_one] at h
      have hre : 4 * (1 : ℝ) * c * (infNorm X * infNorm X_inv) * infNorm A
          = 4 * c * (infNorm X * infNorm X_inv) * infNorm A := by ring
      rw [hre] at h
      exact h
    exact higham_18_1_real_diagonalizable_tendsto n hn A X X_inv J hXr hsim
      hdiag ρ hρ0 hρ1 hdiagbd v c hc hComp hCond'
  · -- t ≥ 2: build the scaling vector and the δ-scaled Jordan spec.
    have hβpos : 0 < jordanBeta ρ t := jordanBeta_pos ρ t hρ1 ht2
    have hβlt : jordanBeta ρ t < 1 := jordanBeta_lt_one ρ t hρ0 ht2
    obtain ⟨p, hp0, hp1, hp2, hpstep⟩ :=
      exists_jordan_scaling_vector n J t (jordanBeta ρ t) hβpos hβlt.le hrun
    obtain ⟨C, q, hC, hq0, hq1, hbound⟩ :=
      higham_knight_18_1 n hn A X X_inv
        (JordanFormSpec.ofRealJordan n hn A X X_inv J hXr hsim hshape
          ρ hρ0 hρ1 hdiagbd hsup t ht2 p hp0 hp1 hp2 hpstep)
        v c hc hComp hCond
    exact computedMatPow_tendsto_zero_of_geometric n v C q hq0 hq1 hbound

/-- **Axiom-free real-spectrum Jordan case of Theorem 18.1 for the actual
    floating-point iteration** — Higham, Accuracy and Stability of Numerical
    Algorithms, 2nd ed., §18.2, Theorem 18.1 (pp. 347–348).

    With `X⁻¹AX = J` upper bidiagonal (`|J_{ii}| ≤ ρ < 1`, superdiagonal
    of modulus ≤ 1, runs of nonzero superdiagonal entries ≤ `t − 1`) and the
    printed condition `4t·γ_{n+2}·κ∞(X)·‖A‖∞ < (1−ρ)^t`, the computed vectors
    `fl(Aᵐ v₀)` (repeated `fl_matVec`) satisfy `‖fl(Aᵐ v₀)‖∞ → 0`.
    Fully end-to-end: concrete algorithm, concrete rounding model, no assumed
    construction.  Honest scope: real-spectrum Jordan data;
    complex/defective-over-ℂ case not covered. -/
theorem higham_18_1_real_jordan_fl_tendsto (fp : FPModel) (n : ℕ) (hn : 0 < n)
    (A X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv)
    (hsim : matMul n X_inv (matMul n A X) = J)
    (hshape : ∀ i j : Fin n, (j : ℕ) ≠ (i : ℕ) → (j : ℕ) ≠ (i : ℕ) + 1 → J i j = 0)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hdiagbd : ∀ i, |J i i| ≤ ρ)
    (hsup : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → |J i j| ≤ 1)
    (t : ℕ) (ht1 : 1 ≤ t)
    (hrun : ∀ k, jordanRunLength n J k ≤ t - 1)
    (v0 : Fin n → ℝ) (hval : gammaValid fp (n + 2))
    (hCond : 4 * (t : ℝ) * gamma fp (n + 2) *
      (infNorm X * infNorm X_inv) * infNorm A < (1 - ρ) ^ t) :
    Filter.Tendsto
      (fun m => infNormVec (fl_matPowVecSeq fp n A v0 m))
      Filter.atTop (nhds 0) :=
  higham_18_1_real_jordan_tendsto n hn A X X_inv J hXr hsim hshape
    ρ hρ0 hρ1 hdiagbd hsup t ht1 hrun (fl_matPowVecSeq fp n A v0)
    (gamma fp (n + 2)) (gamma_nonneg fp hval)
    (computedMatPowVec_fl_matVec_gamma_add_two fp n A v0 hval) hCond

-- ============================================================
-- §18.1  Exact arithmetic: eq (18.5) alternative form, real Jordan case
-- ============================================================









































































































end NumStability
