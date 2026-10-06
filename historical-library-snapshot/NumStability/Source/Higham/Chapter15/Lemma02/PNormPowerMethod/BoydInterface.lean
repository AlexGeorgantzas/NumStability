import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Sequences
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.NormEstimation.OneNorm.FiniteIndex.Basic
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Carrier.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Differentiation.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Differentiation.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.FixedPoints.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Duality.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Duality.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.Rectangular.PNormRectangular
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification
import NumStability.Source.Higham.Chapter15.Lemma02.PNormPowerMethod.PNormRectangular

/-!
# Chapter15 Lemma02 PNormPowerMethod BoydInterface

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapter15BoydBridges` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Ch15

open Filter Function Set

open scoped BigOperators Topology

/-- Consecutive monotonicity from rectangular Lemma 15.2 upgrades to
monotonicity of the complete estimate sequence. -/
theorem rect_gammaSeq_monotone {m n : ℕ} (P : RectPNormPair m n)
    (x0 : Fin n → ℝ) (hx0 : P.pIn x0 = 1) :
    Monotone (P.gammaSeq x0) :=
  monotone_nat_of_le_succ (P.gammaSeq_mono x0 hx0)

/-- For the concrete smooth rectangular power method, and away from the
impossible zero-`z` branch, Higham's scalar stopping test is equivalent to
the vector fixed-point equation `xnext x = x`. -/
theorem rect_general_stopsAt_iff_xnext_eq {m n : ℕ} (hn : 0 < n)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hxunit : realVecLpNorm p x = 1)
    (hz : (RectPNormPair.general hn hpq A).zof x ≠ 0) :
    (RectPNormPair.general hn hpq A).StopsAt x ↔
      (RectPNormPair.general hn hpq A).xnext x = x := by
  let P := RectPNormPair.general hn hpq A
  constructor
  · intro hstop
    have hchain := P.higham15_lemma15_2b_rectangular x hxunit
    have hdot := P.higham15_lemma15_2a_rectangular x
    have heq : realVecLpNorm q (P.zof x) =
        ∑ j : Fin n, x j * P.zof x j := by
      have hle : realVecLpNorm q (P.zof x) ≤
          ∑ j : Fin n, P.zof x j * x j := hstop
      have hge : (∑ j : Fin n, P.zof x j * x j) ≤
          realVecLpNorm q (P.zof x) := by
        rw [hdot]
        exact hchain.1
      rw [show (∑ j : Fin n, x j * P.zof x j) =
          ∑ j : Fin n, P.zof x j * x j by
        apply Finset.sum_congr rfl
        intro j _
        ring]
      exact le_antisymm hle hge
    have hxdual : x = realLpDual hpq.symm (P.zof x) :=
      realLpNormer_eq_dual hpq (P.zof x) x hz hxunit heq.symm
    change realLpDualUnit hn hpq.symm (P.zof x) = x
    rw [realLpDualUnit, if_neg hz]
    exact hxdual.symm
  · intro hfixed
    change realVecLpNorm q (P.zof x) ≤
      ∑ j : Fin n, P.zof x j * x j
    have hattain := realLpDualUnit_attains hn hpq.symm (P.zof x)
    change (∑ j : Fin n,
      realLpDualUnit hn hpq.symm (P.zof x) j * P.zof x j) =
        realVecLpNorm q (P.zof x) at hattain
    have hfixed' : realLpDualUnit hn hpq.symm (P.zof x) = x := hfixed
    rw [hfixed'] at hattain
    rw [← hattain]
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- For the actual smooth rectangular update, failure of the objective to
increase forces a fixed point.  This packages the strict part of Lemma 15.2
and the scalar-stop/fixed-point equivalence; it assumes neither convergence
nor attraction. -/
theorem rect_general_xnext_eq_of_objective_not_increased {m n : ℕ}
    (hn : 0 < n) {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hxunit : realVecLpNorm p x = 1)
    (hz : (RectPNormPair.general hn hpq A).zof x ≠ 0)
    (hback :
      realVecLpNorm p
          ((RectPNormPair.general hn hpq A).yof
            ((RectPNormPair.general hn hpq A).xnext x)) ≤
        realVecLpNorm p ((RectPNormPair.general hn hpq A).yof x)) :
    (RectPNormPair.general hn hpq A).xnext x = x := by
  let P := RectPNormPair.general hn hpq A
  apply (rect_general_stopsAt_iff_xnext_eq hn hpq A x hxunit hz).1
  change P.qIn (P.zof x) ≤ ∑ j : Fin n, P.zof x j * x j
  rw [P.higham15_lemma15_2a_rectangular x]
  exact (P.higham15_lemma15_2b_rectangular x hxunit).2.1.trans hback

theorem rect_general_zof_ne_zero_of_mem_boydCarrier {m n : ℕ}
    [Nontrivial (Fin n)] (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q) (A : Fin m → Fin n → ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    (hGram : Matrix.IsIrreducible
      (Matrix.of (rectGram A) : Matrix (Fin n) (Fin n) ℝ))
    {x : Fin n → ℝ} (hx : x ∈ boydNonnegativeUnitCarrier p) :
    (RectPNormPair.general hn hpq A).zof x ≠ 0 := by
  let P := RectPNormPair.general hn hpq A
  have hyne : P.yof x ≠ 0 :=
    rect_general_yof_ne_zero_of_mem_boydCarrier hn hpq A hA hGram hx
  have hynorm : 0 < realVecLpNorm p (P.yof x) :=
    realVecLpNorm_pos (le_of_lt hpq.lt) hyne
  intro hzero
  have hpair := P.higham15_lemma15_2a_rectangular x
  rw [hzero] at hpair
  simp at hpair
  exact (ne_of_gt hynorm) (by simpa [P] using hpair.symm)

theorem rect_general_xnext_mem_boydCarrier {m n : ℕ}
    [Nontrivial (Fin n)] (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q) (A : Fin m → Fin n → ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    (hGram : Matrix.IsIrreducible
      (Matrix.of (rectGram A) : Matrix (Fin n) (Fin n) ℝ))
    {x : Fin n → ℝ} (hx : x ∈ boydNonnegativeUnitCarrier p) :
    (RectPNormPair.general hn hpq A).xnext x ∈
      boydNonnegativeUnitCarrier p := by
  let P := RectPNormPair.general hn hpq A
  have hznonneg : ∀ j, 0 ≤ P.zof x j :=
    rect_general_zof_nonneg_of_mem_boydCarrier hn hpq A hA hGram hx
  have hzne : P.zof x ≠ 0 :=
    rect_general_zof_ne_zero_of_mem_boydCarrier hn hpq A hA hGram hx
  constructor
  · change ∀ j, 0 ≤ realLpDualUnit hn hpq.symm (P.zof x) j
    simpa [realLpDualUnit, hzne] using
      realLpDual_nonneg_of_nonneg hpq.symm (P.zof x) hzne hznonneg
  · exact P.dqIn_punit (P.zof x)

theorem rect_general_xnext_mapsTo_boydCarrier {m n : ℕ}
    [Nontrivial (Fin n)] (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q) (A : Fin m → Fin n → ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    (hGram : Matrix.IsIrreducible
      (Matrix.of (rectGram A) : Matrix (Fin n) (Fin n) ℝ)) :
    MapsTo (RectPNormPair.general hn hpq A).xnext
      (boydNonnegativeUnitCarrier p) (boydNonnegativeUnitCarrier p) := by
  intro x hx
  exact rect_general_xnext_mem_boydCarrier hn hpq A hA hGram hx

theorem continuousOn_rect_general_xnext_boydCarrier {m n : ℕ}
    [Nontrivial (Fin n)] (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q) (A : Fin m → Fin n → ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    (hGram : Matrix.IsIrreducible
      (Matrix.of (rectGram A) : Matrix (Fin n) (Fin n) ℝ)) :
    ContinuousOn (RectPNormPair.general hn hpq A).xnext
      (boydNonnegativeUnitCarrier p) := by
  intro x hx
  exact (continuousAt_rect_general_xnext hn hpq A
    (rect_general_yof_ne_zero_of_mem_boydCarrier hn hpq A hA hGram hx)
    (rect_general_zof_ne_zero_of_mem_boydCarrier
      hn hpq A hA hGram hx)).continuousWithinAt

/-- Under Boyd's printed matrix hypotheses, the actual objective has a
nonnegative unit maximizer, and every such compact-carrier maximizer is a
fixed point of the actual Algorithm 15.1 update.  This derives existence and
stationarity without assuming convergence, attraction, uniqueness, or
optimality relative to the repository's complex induced norm. -/
theorem exists_boydCarrier_maximizing_fixedPoint {m n : ℕ}
    [Nontrivial (Fin n)] (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q) (A : Fin m → Fin n → ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    (hGram : Matrix.IsIrreducible
      (Matrix.of (rectGram A) : Matrix (Fin n) (Fin n) ℝ)) :
    ∃ xbar : Fin n → ℝ,
      xbar ∈ boydNonnegativeUnitCarrier p ∧
      (RectPNormPair.general hn hpq A).xnext xbar = xbar ∧
      ∀ x ∈ boydNonnegativeUnitCarrier p,
        realVecLpNorm p ((RectPNormPair.general hn hpq A).yof x) ≤
          realVecLpNorm p ((RectPNormPair.general hn hpq A).yof xbar) := by
  let P := RectPNormPair.general hn hpq A
  let s := boydNonnegativeUnitCarrier (n := n) p
  let g : (Fin n → ℝ) → ℝ := fun x => realVecLpNorm p (P.yof x)
  have hs : IsCompact s := isCompact_boydNonnegativeUnitCarrier hpq
  have hsne : s.Nonempty :=
    boydNonnegativeUnitCarrier_nonempty hn (le_of_lt hpq.lt)
  have hg : Continuous g := by
    simpa [g, P] using continuous_rect_general_objective hn hpq A
  obtain ⟨xbar, hxbar, hmax⟩ := hs.exists_isMaxOn hsne hg.continuousOn
  have hxnext : P.xnext xbar ∈ s :=
    rect_general_xnext_mem_boydCarrier hn hpq A hA hGram hxbar
  have hback : g (P.xnext xbar) ≤ g xbar := hmax hxnext
  have hfixed : P.xnext xbar = xbar :=
    rect_general_xnext_eq_of_objective_not_increased hn hpq A xbar
      hxbar.2
      (rect_general_zof_ne_zero_of_mem_boydCarrier
        hn hpq A hA hGram hxbar)
      hback
  exact ⟨xbar, hxbar, hfixed, fun x hx => hmax hx⟩

theorem rectGram_mulVec_zero_at_zero_of_fixed {m n : ℕ}
    [Nontrivial (Fin n)] (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q) (A : Fin m → Fin n → ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    (hGram : Matrix.IsIrreducible
      (Matrix.of (rectGram A) : Matrix (Fin n) (Fin n) ℝ))
    {x : Fin n → ℝ} (hx : x ∈ boydNonnegativeUnitCarrier p)
    (hfixed : (RectPNormPair.general hn hpq A).xnext x = x)
    {j : Fin n} (hxj : x j = 0) :
    Matrix.mulVec
        (Matrix.of (rectGram A) : Matrix (Fin n) (Fin n) ℝ) x j = 0 := by
  let P := RectPNormPair.general hn hpq A
  have hyne : P.yof x ≠ 0 :=
    rect_general_yof_ne_zero_of_mem_boydCarrier hn hpq A hA hGram hx
  have hzne : P.zof x ≠ 0 :=
    rect_general_zof_ne_zero_of_mem_boydCarrier hn hpq A hA hGram hx
  have hynonneg : ∀ i, 0 ≤ P.yof x i := by
    intro i
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hA i k) (hx.1 k)
  have hdualnonneg : ∀ i, 0 ≤ realLpDual hpq (P.yof x) i :=
    realLpDual_nonneg_of_nonneg hpq (P.yof x) hyne hynonneg
  have hznonneg : ∀ k, 0 ≤ P.zof x k :=
    rect_general_zof_nonneg_of_mem_boydCarrier
      hn hpq A hA hGram hx
  have hzj : P.zof x j = 0 := by
    by_contra hzjne
    have hzpos : 0 < P.zof x j :=
      lt_of_le_of_ne (hznonneg j) (Ne.symm hzjne)
    have hxnextj : P.xnext x j = 0 := by rw [hfixed, hxj]
    have hgradpos : 0 < realLpGradient q (P.zof x) j :=
      realLpGradient_pos_of_pos_coord hpq.symm.lt (P.zof x) hzne j hzpos
    change realLpDualUnit hn hpq.symm (P.zof x) j = 0 at hxnextj
    rw [realLpDualUnit, if_neg hzne,
      realLpDual_eq_realLpGradient hpq.symm (P.zof x) hzne] at hxnextj
    exact (ne_of_gt hgradpos) hxnextj
  have htermzero : ∀ i : Fin m,
      A i j * realLpDual hpq (P.yof x) i = 0 := by
    have hsum : (∑ i : Fin m,
        A i j * realLpDual hpq (P.yof x) i) = 0 := by
      simpa [P, RectPNormPair.zof] using hzj
    exact fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg
        (s := Finset.univ)
        (fun r _ => mul_nonneg (hA r j) (hdualnonneg r))).mp hsum i
        (Finset.mem_univ i)
  have hytermzero : ∀ i : Fin m, A i j * P.yof x i = 0 := by
    intro i
    rcases (hynonneg i).eq_or_lt with hyzero | hypos
    · rw [hyzero.symm, mul_zero]
    · have hdualpos : 0 < realLpDual hpq (P.yof x) i := by
        rw [realLpDual_eq_realLpGradient hpq (P.yof x) hyne]
        exact realLpGradient_pos_of_pos_coord hpq.lt (P.yof x) hyne i hypos
      have haij : A i j = 0 := by
        rcases mul_eq_zero.mp (htermzero i) with h | h
        · exact h
        · exact (ne_of_gt hdualpos h).elim
      rw [haij, zero_mul]
  rw [rectGram_mulVec_eq_transpose_yof hn hpq A x j]
  exact Finset.sum_eq_zero fun i _ => hytermzero i

/-- Irreducibility rules out boundary fixed points of the actual smooth Boyd
update: every nonnegative unit fixed point is strictly positive. -/
theorem boydCarrier_fixedPoint_pos {m n : ℕ}
    [Nontrivial (Fin n)] (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q) (A : Fin m → Fin n → ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    (hGram : Matrix.IsIrreducible
      (Matrix.of (rectGram A) : Matrix (Fin n) (Fin n) ℝ))
    {x : Fin n → ℝ} (hx : x ∈ boydNonnegativeUnitCarrier p)
    (hfixed : (RectPNormPair.general hn hpq A).xnext x = x) :
    ∀ j, 0 < x j := by
  let M : Matrix (Fin n) (Fin n) ℝ := Matrix.of (rectGram A)
  have hMnonneg : ∀ i k, 0 ≤ M i k := hGram.1
  have hxne : x ≠ 0 :=
    boydCarrier_ne_zero (le_of_lt hpq.lt) hx
  obtain ⟨k0, hxk0_ne⟩ := Function.ne_iff.mp hxne
  have hxk0_pos : 0 < x k0 :=
    lt_of_le_of_ne (hx.1 k0) (Ne.symm hxk0_ne)
  have hrow_zero : ∀ i, x i = 0 → ∀ k, 0 < x k → M i k = 0 := by
    intro i hxi k hxk
    have hmulzero : Matrix.mulVec M x i = 0 := by
      exact rectGram_mulVec_zero_at_zero_of_fixed
        hn hpq A hA hGram hx hfixed hxi
    have htermzero : M i k * x k = 0 := by
      apply (Finset.sum_eq_zero_iff_of_nonneg
        (s := Finset.univ)
        (fun r _ => mul_nonneg (hMnonneg i r) (hx.1 r))).mp
      · simpa [Matrix.mulVec] using hmulzero
      · exact Finset.mem_univ k
    exact (mul_eq_zero.mp htermzero).resolve_right (ne_of_gt hxk)
  have hpow_zero : ∀ r : ℕ, ∀ i, x i = 0 →
      Matrix.mulVec (M ^ r) x i = 0 := by
    intro r
    induction r with
    | zero =>
        intro i hxi
        simpa [hxi]
    | succ r ihr =>
        intro i hxi
        rw [pow_succ']
        rw [← Matrix.mulVec_mulVec]
        unfold Matrix.mulVec
        apply Finset.sum_eq_zero
        intro k _hk
        change M i k * Matrix.mulVec (M ^ r) x k = 0
        by_cases hxk : x k = 0
        · rw [ihr k hxk, mul_zero]
        · have hxkpos : 0 < x k :=
            lt_of_le_of_ne (hx.1 k) (Ne.symm hxk)
          rw [hrow_zero i hxi k hxkpos, zero_mul]
  intro j
  by_contra hj
  have hxj : x j = 0 :=
    le_antisymm (not_lt.mp hj) (hx.1 j)
  have hexists : ∀ i k : Fin n, ∃ r > 0, 0 < (M ^ r) i k := by
    simpa [M] using
      (Matrix.isIrreducible_iff_exists_pow_pos hMnonneg).mp hGram
  obtain ⟨r, _hr, hentry⟩ := hexists j k0
  have hmulpos : 0 < Matrix.mulVec (M ^ r) x j := by
    unfold Matrix.mulVec
    apply Finset.sum_pos'
    · intro k _hk
      exact mul_nonneg (Matrix.pow_apply_nonneg hMnonneg r j k) (hx.1 k)
    · exact ⟨k0, Finset.mem_univ k0, mul_pos hentry hxk0_pos⟩
  rw [hpow_zero r j hxj] at hmulpos
  exact (lt_irrefl 0) hmulpos

/-- Source-derived nonlinear Perron existence/optimality package.  Under the
printed nonnegativity and irreducible-Gram hypotheses there is a strictly
positive nonnegative-unit fixed point whose objective is the exact induced
matrix norm.  No uniqueness or attraction is assumed here. -/
theorem exists_boydCarrier_positive_opP_fixedPoint {m n : ℕ}
    [Nontrivial (Fin n)] (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q) (A : Fin m → Fin n → ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    (hGram : Matrix.IsIrreducible
      (Matrix.of (rectGram A) : Matrix (Fin n) (Fin n) ℝ)) :
    ∃ xbar : Fin n → ℝ,
      xbar ∈ boydNonnegativeUnitCarrier p ∧
      (∀ j, 0 < xbar j) ∧
      (RectPNormPair.general hn hpq A).xnext xbar = xbar ∧
      realVecLpNorm p ((RectPNormPair.general hn hpq A).yof xbar) =
        (RectPNormPair.general hn hpq A).opP := by
  obtain ⟨xbar, hxbar, hfixed, hmax⟩ :=
    exists_boydCarrier_maximizing_fixedPoint hn hpq A hA hGram
  exact ⟨xbar, hxbar,
    boydCarrier_fixedPoint_pos hn hpq A hA hGram hxbar hfixed,
    hfixed, boydCarrier_maximum_eq_opP hn hpq A hA hxbar hmax⟩

end Ch15
end NumStability
