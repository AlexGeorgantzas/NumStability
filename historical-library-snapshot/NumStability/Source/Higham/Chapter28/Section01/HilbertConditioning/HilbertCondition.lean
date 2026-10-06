import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import NumStability.Algorithms.LinearSystems.QR.HouseholderReflector
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Analysis.Conditioning.LinearSystems.PerronFrobenius
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.PerturbationTheory
import NumStability.Analysis.TestMatrices.Hilbert.Basic
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
import NumStability.Source.Higham.Chapter28.Equation01.HilbertInverse.Basic
import NumStability.Source.Higham.Chapter28.Equation01.HilbertInverse.Exact
import NumStability.Source.Higham.Chapter28.Equation04.HilbertCholeskyInverse.Basic
import NumStability.Source.Higham.Chapter28.Section04.Pascal.PascalCondition

/-!
# Chapter28 Section01 HilbertConditioning HilbertCondition

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28HilbertCondition` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

noncomputable section

namespace NumStability

open Filter Asymptotics Finset

open scoped Topology BigOperators

noncomputable def hilbertCentralDelannoy (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ) ^ 2 * 2 ^ k

theorem hilbertCentralDelannoy_sum_model (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℝ) * (Real.sqrt 2 : ℝ) ^ k =
      (1 + Real.sqrt 2) ^ n := by
  conv_rhs => rw [add_comm]
  rw [add_pow (Real.sqrt 2) 1 n]
  apply Finset.sum_congr rfl
  intro k hk
  simp [mul_comm]

theorem hilbertCentralDelannoy_pos (n : ℕ) : 0 < hilbertCentralDelannoy n := by
  unfold hilbertCentralDelannoy
  have hmem : 0 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have hle := Finset.single_le_sum
    (s := Finset.range (n + 1))
    (f := fun k : ℕ => (Nat.choose n k : ℝ) ^ 2 * 2 ^ k)
    (a := 0) (fun k _ => by positivity) hmem
  norm_num at hle
  linarith

theorem choose_add_self_eq_sum_mul_choose (n i : ℕ) :
    Nat.choose (n + i) i =
      ∑ k ∈ Finset.range (i + 1), Nat.choose n k * Nat.choose i k := by
  rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro k hk
  have hki : k ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [Nat.choose_symm hki]

theorem sum_range_choose_mul_choose (n k : ℕ) :
    (∑ i ∈ Finset.range (n + 1), Nat.choose n i * Nat.choose i k) =
      Nat.choose n k * 2 ^ (n - k) := by
  by_cases hkn : k ≤ n
  · have hsplit : k ≤ n + 1 := by omega
    calc
      (∑ i ∈ Finset.range (n + 1), Nat.choose n i * Nat.choose i k) =
          ∑ i ∈ Finset.Ico k (n + 1), Nat.choose n i * Nat.choose i k := by
        rw [← Finset.sum_range_add_sum_Ico
          (fun i => Nat.choose n i * Nat.choose i k) hsplit]
        simp only [add_eq_right]
        apply Finset.sum_eq_zero
        intro i hi
        have hik : i < k := Finset.mem_range.mp hi
        simp [Nat.choose_eq_zero_of_lt hik]
      _ = ∑ j ∈ Finset.range (n + 1 - k),
          Nat.choose n (k + j) * Nat.choose (k + j) k := by
        rw [Finset.sum_Ico_eq_sum_range]
      _ = ∑ j ∈ Finset.range ((n - k) + 1),
          Nat.choose n k * Nat.choose (n - k) j := by
        have hrange : n + 1 - k = (n - k) + 1 := by omega
        rw [hrange]
        apply Finset.sum_congr rfl
        intro j hj
        simpa using
          (Nat.choose_mul (n := n) (k := k + j) (s := k)
            (by omega : k ≤ k + j))
      _ = Nat.choose n k * 2 ^ (n - k) := by
        rw [← Finset.mul_sum, Nat.sum_range_choose]
  · have hnk : n < k := Nat.lt_of_not_ge hkn
    rw [Nat.choose_eq_zero_of_lt hnk, zero_mul]
    apply Finset.sum_eq_zero
    intro i hi
    have hiN : i < n + 1 := Finset.mem_range.mp hi
    have hin : i ≤ n := by omega
    have hik : i < k := lt_of_le_of_lt hin hnk
    simp [Nat.choose_eq_zero_of_lt hik]

theorem hilbertCentralDelannoy_nat_identity (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1),
        Nat.choose n i * Nat.choose (n + i) i) =
      ∑ k ∈ Finset.range (n + 1), (Nat.choose n k) ^ 2 * 2 ^ k := by
  calc
    (∑ i ∈ Finset.range (n + 1),
        Nat.choose n i * Nat.choose (n + i) i) =
        ∑ i ∈ Finset.range (n + 1),
          ∑ k ∈ Finset.range (i + 1),
            Nat.choose n i * (Nat.choose n k * Nat.choose i k) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [choose_add_self_eq_sum_mul_choose, Finset.mul_sum]
    _ = ∑ i ∈ Finset.range (n + 1),
          ∑ k ∈ Finset.range (n + 1),
            Nat.choose n i * (Nat.choose n k * Nat.choose i k) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hin : i ≤ n := by
        have := Finset.mem_range.mp hi
        omega
      rw [← Finset.sum_range_add_sum_Ico
        (fun k => Nat.choose n i * (Nat.choose n k * Nat.choose i k))
        (show i + 1 ≤ n + 1 by omega)]
      have hzero :
          (∑ k ∈ Finset.Ico (i + 1) (n + 1),
            Nat.choose n i * (Nat.choose n k * Nat.choose i k)) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        have hik : i < k := by
          have := (Finset.mem_Ico.mp hk).1
          omega
        simp [Nat.choose_eq_zero_of_lt hik]
      rw [hzero, add_zero]
    _ = ∑ k ∈ Finset.range (n + 1),
          ∑ i ∈ Finset.range (n + 1),
            Nat.choose n i * (Nat.choose n k * Nat.choose i k) := by
      rw [Finset.sum_comm]
    _ = ∑ k ∈ Finset.range (n + 1),
          Nat.choose n k *
            (∑ i ∈ Finset.range (n + 1), Nat.choose n i * Nat.choose i k) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = ∑ k ∈ Finset.range (n + 1),
          (Nat.choose n k) ^ 2 * 2 ^ (n - k) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [sum_range_choose_mul_choose]
      ring
    _ = ∑ k ∈ Finset.range (n + 1),
          (Nat.choose n k) ^ 2 * 2 ^ k := by
      symm
      calc
        (∑ k ∈ Finset.range (n + 1), (Nat.choose n k) ^ 2 * 2 ^ k) =
            ∑ k ∈ Finset.range (n + 1),
              (Nat.choose n (n + 1 - 1 - k)) ^ 2 *
                2 ^ (n + 1 - 1 - k) := by
          symm
          exact Finset.sum_range_reflect
            (fun k => (Nat.choose n k) ^ 2 * 2 ^ k) (n + 1)
        _ = ∑ k ∈ Finset.range (n + 1),
              (Nat.choose n k) ^ 2 * 2 ^ (n - k) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hkn : k ≤ n := by
            have := Finset.mem_range.mp hk
            omega
          have harith : n + 1 - 1 - k = n - k := by omega
          rw [harith, Nat.choose_symm hkn]

theorem hilbertCentralDelannoy_eq_original (n : ℕ) :
    hilbertCentralDelannoy n =
      ∑ i ∈ Finset.range (n + 1),
        (Nat.choose n i : ℝ) * Nat.choose (n + i) i := by
  unfold hilbertCentralDelannoy
  norm_cast
  exact (hilbertCentralDelannoy_nat_identity n).symm

noncomputable def hilbertDelannoyTerm (n i : ℕ) : ℝ :=
  Nat.choose n i * Nat.choose (n + i) i

theorem hilbertInverseTelescoper_diag_eq_delannoyTerm
    (n i : ℕ) (hin : i < n) :
    hilbertInverseTelescoper i i n =
      ((n - i : ℕ) : ℝ) ^ 2 * hilbertDelannoyTerm n i ^ 2 /
        (2 * i + 1 : ℕ) := by
  simp only [hilbertInverseTelescoper, hin, if_pos, hilbertDelannoyTerm]
  rw [Nat.cast_choose ℝ (le_of_lt hin),
    Nat.cast_choose ℝ (show i ≤ n + i by omega)]
  have hni : n - i ≠ 0 := by omega
  have hfact : ∀ m : ℕ, (Nat.factorial m : ℝ) ≠ 0 := by
    intro m
    exact_mod_cast Nat.factorial_ne_zero m
  have hsub : n - i = (n - (i + 1)) + 1 := by omega
  rw [hsub, Nat.factorial_succ]
  simp only [Nat.add_sub_cancel_right]
  push_cast
  field_simp [hfact, hni]
  ring

theorem hilbertInverseFormula_diag_eq_telescoper
    {n : ℕ} (i : Fin n) :
    hilbertInverseFormula n i i =
      hilbertInverseTelescoper i.val i.val n := by
  rw [hilbertInverseFormula_apply]
  have hsign : (-1 : ℝ) ^ (i.val + i.val) = 1 := by
    exact Even.neg_one_pow (Even.add_self i.val)
  rw [hilbertInverseTelescoper_eq_formula_abs
    i.val i.val n le_rfl i.isLt]
  unfold hilbertInverseEntry
  rw [hsign]
  ring

theorem hilbertDelannoyTerm_step (n i : ℕ) (hin : i < n) :
    ((n - i : ℕ) : ℝ) * hilbertDelannoyTerm n i =
      ((n + i : ℕ) : ℝ) * hilbertDelannoyTerm (n - 1) i := by
  unfold hilbertDelannoyTerm
  rw [Nat.cast_choose ℝ (le_of_lt hin),
    Nat.cast_choose ℝ (show i ≤ n + i by omega),
    Nat.cast_choose ℝ (show i ≤ n - 1 by omega),
    Nat.cast_choose ℝ (show i ≤ n - 1 + i by omega)]
  have hn : n ≠ 0 := by omega
  have hni : n - i ≠ 0 := by omega
  have hfact : ∀ m : ℕ, (Nat.factorial m : ℝ) ≠ 0 := by
    intro m
    exact_mod_cast Nat.factorial_ne_zero m
  have hnfact : Nat.factorial n = n * Nat.factorial (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, Nat.factorial_succ]
    rw [show n - 1 + 1 = n by omega]
  have hnifact : Nat.factorial (n + i) =
      (n + i) * Nat.factorial (n - 1 + i) := by
    conv_lhs => rw [show n + i = (n - 1 + i) + 1 by omega,
      Nat.factorial_succ]
    rw [show n - 1 + i + 1 = n + i by omega]
  have hsub : n - i = (n - i - 1) + 1 := by omega
  rw [hnfact, hnifact, hsub, Nat.factorial_succ]
  simp only [Nat.add_sub_cancel_right]
  push_cast
  field_simp [hfact, hn, hni]
  rw [show n - 1 - i = n - i - 1 by omega, hnfact]
  push_cast
  ring

theorem hilbertInverseFormula_diag_lower_delannoy
    {n : ℕ} (i : Fin n) :
    hilbertDelannoyTerm (n - 1) i.val ^ 2 ≤
      hilbertInverseFormula n i i := by
  rw [hilbertInverseFormula_diag_eq_telescoper,
    hilbertInverseTelescoper_diag_eq_delannoyTerm n i.val i.isLt]
  rw [show ((n - i.val : ℕ) : ℝ) ^ 2 * hilbertDelannoyTerm n i.val ^ 2 =
      (((n - i.val : ℕ) : ℝ) * hilbertDelannoyTerm n i.val) ^ 2 by ring,
    hilbertDelannoyTerm_step n i.val i.isLt]
  have hden : (0 : ℝ) < (2 * i.val + 1 : ℕ) := by positivity
  apply (le_div_iff₀ hden).2
  have hfactor : ((2 * i.val + 1 : ℕ) : ℝ) ≤
      ((n + i.val : ℕ) : ℝ) ^ 2 := by
    push_cast
    have hnNat : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
    have hn : (1 : ℝ) ≤ n := by exact_mod_cast hnNat
    have hi0 : (0 : ℝ) ≤ i.val := by positivity
    nlinarith [sq_nonneg ((i.val : ℝ))]
  nlinarith [sq_nonneg (hilbertDelannoyTerm (n - 1) i.val)]

theorem hilbertInverseFormula_diag_upper_delannoy
    {n : ℕ} (i : Fin n) :
    hilbertInverseFormula n i i ≤
      (n : ℝ) ^ 2 * hilbertCentralDelannoy n ^ 2 := by
  rw [hilbertInverseFormula_diag_eq_telescoper,
    hilbertInverseTelescoper_diag_eq_delannoyTerm n i.val i.isLt]
  have hterm0 : 0 ≤ hilbertDelannoyTerm n i.val := by
    unfold hilbertDelannoyTerm
    positivity
  have hD0 : 0 ≤ hilbertCentralDelannoy n :=
    (hilbertCentralDelannoy_pos n).le
  have htermD : hilbertDelannoyTerm n i.val ≤ hilbertCentralDelannoy n := by
    rw [hilbertCentralDelannoy_eq_original]
    unfold hilbertDelannoyTerm
    apply Finset.single_le_sum
      (s := Finset.range (n + 1))
      (f := fun k : ℕ => (Nat.choose n k : ℝ) * Nat.choose (n + k) k)
      (a := i.val)
    · intro k hk
      positivity
    · exact Finset.mem_range.mpr (by omega)
  have hsub : (((n - i.val : ℕ) : ℝ)) ≤ n := by
    exact_mod_cast Nat.sub_le n i.val
  have hnum0 : 0 ≤
      ((n - i.val : ℕ) : ℝ) ^ 2 * hilbertDelannoyTerm n i.val ^ 2 := by
    positivity
  have hden : (1 : ℝ) ≤ (2 * i.val + 1 : ℕ) := by
    exact_mod_cast (show 1 ≤ 2 * i.val + 1 by omega)
  calc
    ((n - i.val : ℕ) : ℝ) ^ 2 * hilbertDelannoyTerm n i.val ^ 2 /
        (2 * i.val + 1 : ℕ) ≤
        ((n - i.val : ℕ) : ℝ) ^ 2 * hilbertDelannoyTerm n i.val ^ 2 :=
      div_le_self hnum0 hden
    _ ≤ (n : ℝ) ^ 2 * hilbertCentralDelannoy n ^ 2 := by
      gcongr

theorem hilbertInverseFormula_abs_entry_upper_delannoy
    {n : ℕ} (i j : Fin n) :
    |hilbertInverseFormula n i j| ≤
      (n : ℝ) ^ 2 * hilbertCentralDelannoy n ^ 2 := by
  let R := hilbertCholeskyFactorInverse n
  let B : ℝ := (n : ℝ) ^ 2 * hilbertCentralDelannoy n ^ 2
  have hrepr (a b : Fin n) :
      hilbertInverseFormula n a b = ∑ k : Fin n, R a k * R b k := by
    rw [← factorInverseGram_eq_hilbertInverseFormula]
    simp [R, Matrix.mul_apply, Matrix.transpose_apply]
  have hnormsq (a : Fin n) :
      vecNorm2 (fun k : Fin n => R a k) ^ 2 = hilbertInverseFormula n a a := by
    rw [vecNorm2_sq, hrepr]
    simp [vecNorm2Sq, pow_two]
  have hi := hilbertInverseFormula_diag_upper_delannoy i
  have hj := hilbertInverseFormula_diag_upper_delannoy j
  change hilbertInverseFormula n i i ≤ B at hi
  change hilbertInverseFormula n j j ≤ B at hj
  calc
    |hilbertInverseFormula n i j| =
        |∑ k : Fin n, R i k * R j k| := by rw [hrepr]
    _ ≤ vecNorm2 (fun k : Fin n => R i k) *
          vecNorm2 (fun k : Fin n => R j k) :=
      abs_vecInnerProduct_le_vecNorm2_mul _ _
    _ ≤ B := by
      have hi0 := vecNorm2_nonneg (fun k : Fin n => R i k)
      have hj0 := vecNorm2_nonneg (fun k : Fin n => R j k)
      rw [← hnormsq i] at hi
      rw [← hnormsq j] at hj
      nlinarith [sq_nonneg
        (vecNorm2 (fun k : Fin n => R i k) -
          vecNorm2 (fun k : Fin n => R j k))]

theorem opNorm2_hilbertInverseFormula_upper_delannoy (n : ℕ) :
    opNorm2 (hilbertInverseFormula n) ≤
      (n : ℝ) ^ 3 * hilbertCentralDelannoy n ^ 2 := by
  let B : ℝ := (n : ℝ) ^ 2 * hilbertCentralDelannoy n ^ 2
  let C : RSqMat n := fun _ _ => B
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hfrob : frobNorm (hilbertInverseFormula n) ≤ frobNorm C := by
    apply frobNorm_le_of_entry_abs_le
    · intro i j
      exact hB
    · intro i j
      exact hilbertInverseFormula_abs_entry_upper_delannoy i j
  calc
    opNorm2 (hilbertInverseFormula n) ≤ frobNorm (hilbertInverseFormula n) :=
      opNorm2_le_frobNorm _
    _ ≤ frobNorm C := hfrob
    _ = (n : ℝ) * B := by
      simpa [C] using (frobNorm_const (n := n) hB)
    _ = (n : ℝ) ^ 3 * hilbertCentralDelannoy n ^ 2 := by
      dsimp [B]
      ring

theorem hilbertCentralDelannoy_sq_le_opNorm2_hilbertInverseFormula
    (n : ℕ) (hn : 0 < n) :
    hilbertCentralDelannoy (n - 1) ^ 2 ≤
      (n : ℝ) ^ 2 * opNorm2 (hilbertInverseFormula n) := by
  have hrange : n - 1 + 1 = n := by omega
  have hsum : hilbertCentralDelannoy (n - 1) =
      ∑ i ∈ Finset.range n, hilbertDelannoyTerm (n - 1) i := by
    rw [hilbertCentralDelannoy_eq_original, hrange]
    rfl
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := Finset.range n) (f := fun i : ℕ => hilbertDelannoyTerm (n - 1) i)
  have hsqsum :
      (∑ i ∈ Finset.range n, hilbertDelannoyTerm (n - 1) i ^ 2) ≤
        (n : ℝ) * opNorm2 (hilbertInverseFormula n) := by
    calc
      (∑ i ∈ Finset.range n, hilbertDelannoyTerm (n - 1) i ^ 2) ≤
          ∑ _i ∈ Finset.range n, opNorm2 (hilbertInverseFormula n) := by
        apply Finset.sum_le_sum
        intro i hi
        let fi : Fin n := ⟨i, Finset.mem_range.mp hi⟩
        have hdiag := hilbertInverseFormula_diag_lower_delannoy fi
        have hdiag0 : 0 ≤ hilbertInverseFormula n fi fi :=
          le_trans (sq_nonneg _) hdiag
        have hop := abs_matrix_entry_le_opNorm2
          (hilbertInverseFormula n) fi fi
        rw [abs_of_nonneg hdiag0] at hop
        exact hdiag.trans hop
      _ = (n : ℝ) * opNorm2 (hilbertInverseFormula n) := by
        simp [Finset.card_range]
  calc
    hilbertCentralDelannoy (n - 1) ^ 2 =
        (∑ i ∈ Finset.range n, hilbertDelannoyTerm (n - 1) i) ^ 2 := by
      rw [hsum]
    _ ≤ (n : ℝ) *
          (∑ i ∈ Finset.range n, hilbertDelannoyTerm (n - 1) i ^ 2) := by
      simpa [Finset.card_range] using hcs
    _ ≤ (n : ℝ) * ((n : ℝ) * opNorm2 (hilbertInverseFormula n)) := by
      exact mul_le_mul_of_nonneg_left hsqsum (by positivity)
    _ = (n : ℝ) ^ 2 * opNorm2 (hilbertInverseFormula n) := by ring

theorem one_le_opNorm2_hilbertMatrix_succ (n : ℕ) :
    1 ≤ opNorm2 (hilbertMatrix (n + 1)) := by
  have h := abs_matrix_entry_le_opNorm2
    (hilbertMatrix (n + 1)) (0 : Fin (n + 1)) (0 : Fin (n + 1))
  norm_num [hilbertMatrix] at h
  exact h

theorem opNorm2_hilbertMatrix_succ_le (n : ℕ) :
    opNorm2 (hilbertMatrix (n + 1)) ≤ (n + 1 : ℝ) := by
  let C : RSqMat (n + 1) := fun _ _ => 1
  have hentry : ∀ i j : Fin (n + 1), |hilbertMatrix (n + 1) i j| ≤ C i j := by
    intro i j
    dsimp [C]
    rw [abs_of_nonneg (by positivity)]
    exact (div_le_one (by positivity : (0 : ℝ) < (i.val + j.val + 1 : ℕ))).2
      (by exact_mod_cast (show 1 ≤ i.val + j.val + 1 by omega))
  have hfrob : frobNorm (hilbertMatrix (n + 1)) ≤ frobNorm C :=
    frobNorm_le_of_entry_abs_le _ C (by intro i j; positivity) hentry
  calc
    opNorm2 (hilbertMatrix (n + 1)) ≤ frobNorm (hilbertMatrix (n + 1)) :=
      opNorm2_le_frobNorm _
    _ ≤ frobNorm C := hfrob
    _ = (n + 1 : ℝ) := by
      simpa [C] using (frobNorm_const (n := n + 1) (show (0 : ℝ) ≤ 1 by norm_num))

end NumStability

end
