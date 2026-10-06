/-
Copyright (c) 2026. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.

# Higham Theorem 11.7: support-aware outer substitutions

The dense `fl_forwardSub` and `fl_backSub` kernels visit every structural zero
in a triangular row.  The abstract `FPModel` does not make `fl_sub a 0` exact,
so those dense sweeps honestly carry a `gamma n` budget even when the factor is
block bidiagonal.  This module implements the sparse computation that Higham's
tridiagonal analysis requires: each row visits only its two possible strict
lower-band predecessors.  Reversing the index order gives the matching upper
solve.

The local row is an actual rounded product/summation/division computation.  Its
backward error follows from Lemma 8.4 with at most three leaves (right-hand side
plus two products), yielding the dimension-independent componentwise budget
`gamma 3`.  A structural induction on `TriGrowthData` proves that the computed
`flMixedL` factor has precisely the required lower bandwidth two.
-/
import NumStability.Algorithms.Cholesky.BunchTridiagonalActualSolveCh11Closure
import NumStability.Algorithms.Summation.Tree.Chain
import NumStability.Algorithms.TriangularArbitraryOrder

open scoped BigOperators

namespace NumStability.Ch11Closure.SparseSolve

open NumStability
open NumStability.Ch11Closure
open NumStability.Ch11Closure.Mixed
open NumStability.Ch11Closure.Solve
open NumStability.Ch11Closure.TriGrowthInv
open NumStability.Ch11Closure.BunchTriActual
open NumStability.Ch11Closure.BunchTri

/-! ## A genuine bandwidth-two rounded triangular solve -/

/-- Support-aware forward substitution for a lower matrix of bandwidth two.
For row `i`, only columns `max (i-2) 0, ..., i-1` are evaluated.  The local
sum is an actual rounded chain tree and the final division is rounded. -/
noncomputable def flBand2ForwardSub (fp : FPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (b : Fin n → ℝ) (i : Fin n) : ℝ :=
  let m := min 2 i.val
  let a : Fin m → ℝ := fun t =>
    L i ⟨i.val - m + t.val, by omega⟩
  let x : Fin m → ℝ := fun t =>
    flBand2ForwardSub fp n L b ⟨i.val - m + t.val, by omega⟩
  let w : Fin (m + 1) → ℝ :=
    Fin.cases (b i) (fun t => -fp.fl_mul (a t) (x t))
  fp.fl_div ((SumTree.chainTreeSucc m).eval fp w) (L i i)
termination_by i.val
decreasing_by omega

theorem flBand2ForwardSub_eq (fp : FPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (b : Fin n → ℝ) (i : Fin n) :
    let m := min 2 i.val
    let a : Fin m → ℝ := fun t => L i ⟨i.val - m + t.val, by omega⟩
    let x : Fin m → ℝ := fun t =>
      flBand2ForwardSub fp n L b ⟨i.val - m + t.val, by omega⟩
    let w : Fin (m + 1) → ℝ :=
      Fin.cases (b i) (fun t => -fp.fl_mul (a t) (x t))
    flBand2ForwardSub fp n L b i =
      fp.fl_div ((SumTree.chainTreeSucc m).eval fp w) (L i i) := by
  rw [flBand2ForwardSub]

/-- One support-compressed row has a componentwise `gamma 3` backward error.
The right-hand side is unperturbed; the perturbations multiply only the
diagonal and the at-most-two visited matrix entries. -/
theorem flBand2ForwardSub_row_tight (fp : FPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hdiag : ∀ i, L i i ≠ 0)
    (hlower : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hband : ∀ i j : Fin n, j.val + 2 < i.val → L i j = 0)
    (hval3 : gammaValid fp 3) (i : Fin n) :
    ∃ φ : Fin n → ℝ,
      (∀ j, |φ j| ≤ gamma fp 3) ∧
      b i = ∑ j : Fin n,
        L i j * (1 + φ j) * flBand2ForwardSub fp n L b j := by
  let m := min 2 i.val
  have hm2 : m ≤ 2 := min_le_left _ _
  have hmle : m ≤ i.val := min_le_right _ _
  have hm1 : m + 1 ≤ 3 := by omega
  have hvalid : gammaValid fp (m + 1) := gammaValid_mono fp hm1 hval3
  let a : Fin m → ℝ := fun t => L i ⟨i.val - m + t.val, by omega⟩
  let x : Fin m → ℝ := fun t =>
    flBand2ForwardSub fp n L b ⟨i.val - m + t.val, by omega⟩
  let w : Fin (m + 1) → ℝ :=
    Fin.cases (b i) (fun t => -fp.fl_mul (a t) (x t))
  obtain ⟨θ, η, hθ, hη, heq⟩ :=
    higham8_4_anyOrder_mulSub_div fp (SumTree.chainTreeSucc m) hvalid
      (b i) (L i i) (hdiag i) a x
  have hxi : flBand2ForwardSub fp n L b i =
      fp.fl_div ((SumTree.chainTreeSucc m).eval fp w) (L i i) := by
    simpa [m, a, x, w] using flBand2ForwardSub_eq fp n L b i
  have hlocal :
      L i i * flBand2ForwardSub fp n L b i * (1 + θ) =
        b i - ∑ t : Fin m, a t * x t * (1 + η t) := by
    rw [hxi]
    simpa [w] using heq
  let φ : Fin n → ℝ := fun j =>
    if hdiag' : j.val = i.val then θ
    else if hwin : i.val - m ≤ j.val ∧ j.val < i.val then
      η ⟨j.val - (i.val - m), by omega⟩
    else 0
  refine ⟨φ, ?_, ?_⟩
  · intro j
    simp only [φ]
    split_ifs
    · exact hθ.trans (gamma_mono fp hm1 hval3)
    · exact (hη _).trans (gamma_mono fp hm1 hval3)
    · simpa using gamma_nonneg fp hval3
  · have hdiagφ : φ i = θ := by simp [φ]
    have hoffφ : ∀ t : Fin m,
        φ ⟨i.val - m + t.val, by omega⟩ = η t := by
      intro t
      simp only [φ]
      rw [dif_neg (by omega), dif_pos (by omega)]
      congr 1
      apply Fin.ext
      simp only [Fin.mk.injEq]
      omega
    have hsumOff :
        ∑ j ∈ (Finset.univ.erase i).filter
            (fun j : Fin n => i.val - m ≤ j.val ∧ j.val < i.val),
            L i j * (1 + φ j) * flBand2ForwardSub fp n L b j =
          ∑ t : Fin m, a t * x t * (1 + η t) := by
      symm
      apply Finset.sum_nbij
        (fun t : Fin m => (⟨i.val - m + t.val, by omega⟩ : Fin n))
      · intro t _
        simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
        exact ⟨by intro h; have := Fin.mk.inj h; omega, by omega⟩
      · intro t₁ _ t₂ _ h
        apply Fin.ext
        have := Fin.mk.inj h
        omega
      · intro j hj
        have hj' : j ≠ i ∧ i.val - m ≤ j.val ∧ j.val < i.val := by
          simpa using hj
        refine ⟨⟨j.val - (i.val - m), by omega⟩, Finset.mem_univ _, ?_⟩
        apply Fin.ext
        simp only [Fin.mk.injEq]
        omega
      · intro t _
        rw [hoffφ t]
        dsimp [a, x]
        ring
    have hsumZero :
        ∑ j ∈ (Finset.univ.erase i).filter
            (fun j : Fin n => ¬(i.val - m ≤ j.val ∧ j.val < i.val)),
            L i j * (1 + φ j) * flBand2ForwardSub fp n L b j = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true] at hj
      have hLzero : L i j = 0 := by
        by_cases hji : j.val < i.val
        · apply hband i j
          have hm_cases : m = i.val ∨ m = 2 := by
            simp only [m, min_def]
            split_ifs <;> omega
          rcases hm_cases with hm | hm <;> omega
        · have hij : i.val < j.val := by
            have hneqval : j.val ≠ i.val := by
              intro h
              exact hj.1 (Fin.ext h)
            omega
          exact hlower i j hij
      simp [hLzero]
    have hsumSplit :
        ∑ j ∈ Finset.univ.erase i,
            L i j * (1 + φ j) * flBand2ForwardSub fp n L b j =
          ∑ t : Fin m, a t * x t * (1 + η t) := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.erase i)
        (fun j : Fin n => i.val - m ≤ j.val ∧ j.val < i.val)]
      rw [hsumOff, hsumZero, add_zero]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    rw [hdiagφ, hsumSplit]
    dsimp [a, x] at hlocal ⊢
    linarith [hlocal]

/-- The actual support-aware forward solve has a dimension-independent
componentwise backward perturbation `|ΔL| ≤ gamma 3 |L|`. -/
theorem flBand2ForwardSub_backward_error (fp : FPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hdiag : ∀ i, L i i ≠ 0)
    (hlower : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hband : ∀ i j : Fin n, j.val + 2 < i.val → L i j = 0)
    (hval3 : gammaValid fp 3) :
    ∃ ΔL : Fin n → Fin n → ℝ,
      (∀ i j, |ΔL i j| ≤ gamma fp 3 * |L i j|) ∧
      ∀ i, ∑ j : Fin n,
        (L i j + ΔL i j) * flBand2ForwardSub fp n L b j = b i := by
  have hrow := fun i =>
    flBand2ForwardSub_row_tight fp n L b hdiag hlower hband hval3 i
  let φ : Fin n → Fin n → ℝ := fun i => Classical.choose (hrow i)
  have hφ : ∀ i j, |φ i j| ≤ gamma fp 3 := fun i j =>
    (Classical.choose_spec (hrow i)).1 j
  have heq : ∀ i, b i = ∑ j : Fin n,
      L i j * (1 + φ i j) * flBand2ForwardSub fp n L b j := fun i =>
    (Classical.choose_spec (hrow i)).2
  refine ⟨fun i j => L i j * φ i j, ?_, ?_⟩
  · intro i j
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hφ i j) (abs_nonneg _)
  · intro i
    rw [heq i]
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- Reversal of finite indices, packaged as an equivalence for reindexing the
back-substitution row sums. -/
def finRevEquiv (n : ℕ) : Fin n ≃ Fin n where
  toFun := Fin.rev
  invFun := Fin.rev
  left_inv := Fin.rev_rev
  right_inv := Fin.rev_rev

/-- Support-aware upper solve, implemented by reversing the bandwidth-two
forward solve. -/
noncomputable def flBand2BackSub (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (b : Fin n → ℝ) (i : Fin n) : ℝ :=
  flBand2ForwardSub fp n (fun r c => U r.rev c.rev) (fun r => b r.rev) i.rev

/-- The reversed actual solve has the same dimension-independent `gamma 3`
componentwise backward error. -/
theorem flBand2BackSub_backward_error (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hdiag : ∀ i, U i i ≠ 0)
    (hupper : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hband : ∀ i j : Fin n, i.val + 2 < j.val → U i j = 0)
    (hval3 : gammaValid fp 3) :
    ∃ ΔU : Fin n → Fin n → ℝ,
      (∀ i j, |ΔU i j| ≤ gamma fp 3 * |U i j|) ∧
      ∀ i, ∑ j : Fin n,
        (U i j + ΔU i j) * flBand2BackSub fp n U b j = b i := by
  let Lrev : Fin n → Fin n → ℝ := fun r c => U r.rev c.rev
  let brev : Fin n → ℝ := fun r => b r.rev
  have hdiagRev : ∀ i, Lrev i i ≠ 0 := by
    intro i
    simpa [Lrev] using hdiag i.rev
  have hlowerRev : ∀ i j : Fin n, i.val < j.val → Lrev i j = 0 := by
    intro i j hij
    apply hupper i.rev j.rev
    exact Fin.rev_lt_rev.mpr hij
  have hbandRev : ∀ i j : Fin n, j.val + 2 < i.val → Lrev i j = 0 := by
    intro i j hij
    apply hband i.rev j.rev
    simp only [Fin.val_rev]
    omega
  obtain ⟨ΔL, hΔL, heq⟩ :=
    flBand2ForwardSub_backward_error fp n Lrev brev
      hdiagRev hlowerRev hbandRev hval3
  refine ⟨fun i j => ΔL i.rev j.rev, ?_, ?_⟩
  · intro i j
    simpa [Lrev] using hΔL i.rev j.rev
  · intro i
    have hi := heq i.rev
    simp only [brev, Fin.rev_rev] at hi
    calc
      (∑ j : Fin n,
          (U i j + ΔL i.rev j.rev) * flBand2BackSub fp n U b j)
          = ∑ r : Fin n,
              (U i r.rev + ΔL i.rev r) *
                flBand2ForwardSub fp n Lrev brev r := by
              rw [← Equiv.sum_comp (finRevEquiv n)]
              apply Finset.sum_congr rfl
              intro j _
              simp [finRevEquiv, flBand2BackSub, Lrev, brev]
      _ = b i := by simpa [Lrev] using hi

/-! ## The computed tridiagonal Bunch factor really is bandwidth two -/

/-- Along a tridiagonal Algorithm 11.6 run, the computed mixed lower factor has
no entry more than two subdiagonals below the diagonal.  A 1x1 stage contributes
only the first trailing multiplier; a 2x2 stage contributes only the first
trailing row of two multipliers. -/
theorem flMixedL_bandwidth_two_of_TriGrowthData (fp : FPModel) (M0 : ℝ) :
    ∀ {n : ℕ} (s : PivotSchedule n) (A : Fin n → Fin n → ℝ),
      TriGrowthData fp M0 s A →
      ∀ i j : Fin n, j.val + 2 < i.val → flMixedL fp s A i j = 0 := by
  intro n s
  induction s with
  | nil =>
      intro A _ i
      exact Fin.elim0 i
  | consOne s ih =>
      intro A hdata I J
      rcases hdata with ⟨htri, hA00, _hchoice, htail⟩
      refine Fin.cases ?_ (fun i => ?_) I
      · intro hIJ
        simp only [Fin.val_zero] at hIJ
        omega
      ·
        refine Fin.cases ?_ (fun j => ?_) J
        · intro hIJ
          rw [flMixedL_consOne_s0]
          have hzero : A i.succ 0 = 0 := by
            apply htri.2
            right
            simp only [Fin.val_succ, Fin.val_zero] at hIJ ⊢
            omega
          rw [hzero, fl_div_zero_left fp _ hA00]
        · intro hIJ
          rw [flMixedL_consOne_ss]
          apply ih (flSchurCompl _ fp A) htail i j
          simp only [Fin.val_succ] at hIJ ⊢
          omega
  | consTwo s ih =>
      intro A hdata I J
      rcases hdata with ⟨htri, _hchoice, htail⟩
      refine Fin.cases ?_ (fun i1 => ?_) I
      · intro hIJ
        simp only [Fin.val_zero] at hIJ
        omega
      ·
        refine Fin.cases ?_ (fun i => ?_) i1
        · intro hIJ
          simp only [Fin.val_succ, Fin.val_zero] at hIJ
          omega
        ·
          refine Fin.cases ?_ (fun j1 => ?_) J
          · intro hIJ
            rw [flMixedL_consTwo_t0]
            exact (flMixedMult2_eq_zero_of_tridiag fp A htri i (by
              simp only [Fin.val_succ, Fin.val_zero] at hIJ
              omega)).1
          ·
            refine Fin.cases ?_ (fun j => ?_) j1
            · intro hIJ
              rw [flMixedL_consTwo_t1]
              exact (flMixedMult2_eq_zero_of_tridiag fp A htri i (by
                simp only [Fin.val_succ, Fin.val_zero] at hIJ
                omega)).2
            · intro hIJ
              rw [flMixedL_consTwo_tt]
              apply ih (flSchurCompl2 _ fp A) htail i j
              simp only [Fin.val_succ] at hIJ ⊢
              omega

/-- Actual support-aware forward substitution on the computed `flMixedL`
factor, with dimension-independent outer perturbation. -/
theorem flMixedL_band2_forward_backward_error (fp : FPModel) (hval3 : gammaValid fp 3)
    {n : ℕ} (M0 : ℝ) (s : PivotSchedule n) (A : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (hdata : TriGrowthData fp M0 s A) :
    ∃ ΔL : Fin n → Fin n → ℝ,
      (∀ i j, |ΔL i j| ≤ gamma fp 3 * |flMixedL fp s A i j|) ∧
      ∀ i, ∑ j : Fin n,
        (flMixedL fp s A i j + ΔL i j) *
          flBand2ForwardSub fp n (flMixedL fp s A) b j = b i := by
  apply flBand2ForwardSub_backward_error fp n (flMixedL fp s A) b
  · intro i
    rw [flMixedL_diag]
    exact one_ne_zero
  · exact fun i j hij => flMixedL_lower fp s A i j hij
  · exact flMixedL_bandwidth_two_of_TriGrowthData fp M0 s A hdata
  · exact hval3

/-- Actual support-aware back substitution on `flMixedL transpose`, with the
same dimension-independent outer perturbation. -/
theorem flMixedL_transpose_band2_back_backward_error
    (fp : FPModel) (hval3 : gammaValid fp 3)
    {n : ℕ} (M0 : ℝ) (s : PivotSchedule n) (A : Fin n → Fin n → ℝ)
    (w : Fin n → ℝ) (hdata : TriGrowthData fp M0 s A) :
    ∃ ΔU : Fin n → Fin n → ℝ,
      (∀ i j, |ΔU i j| ≤ gamma fp 3 * |flMixedL fp s A j i|) ∧
      ∀ i, ∑ j : Fin n,
        (flMixedL fp s A j i + ΔU i j) *
          flBand2BackSub fp n (fun r c => flMixedL fp s A c r) w j = w i := by
  apply flBand2BackSub_backward_error fp n
    (fun r c => flMixedL fp s A c r) w
  · intro i
    rw [flMixedL_diag]
    exact one_ne_zero
  · exact fun i j hji => flMixedL_lower fp s A j i hji
  · intro i j hij
    exact flMixedL_bandwidth_two_of_TriGrowthData fp M0 s A hdata j i hij
  · exact hval3

/-! ## Dimension-independent collapse of the actual three-stage solve -/

/-- The scalar coefficient multiplying `|Lhat||Dhat||Lhat^T|` for the
support-aware outer solves and the actual `36u` middle solve.  Unlike the dense
coefficient, this expression contains no matrix dimension. -/
noncomputable def bunchTriSparseSolveCoeff (fp : FPModel) : ℝ :=
  (2 * gamma fp 3 + gamma fp 3 ^ 2) +
    (1 + 2 * gamma fp 3 + gamma fp 3 ^ 2) * (36 * fp.u)

theorem bunchTriSparseSolveCoeff_nonneg (fp : FPModel)
    (hval3 : gammaValid fp 3) : 0 ≤ bunchTriSparseSolveCoeff fp := by
  unfold bunchTriSparseSolveCoeff
  have hg : 0 ≤ gamma fp 3 := gamma_nonneg fp hval3
  have hfirst : 0 ≤ 2 * gamma fp 3 + gamma fp 3 ^ 2 := by positivity
  have hsecond : 0 ≤ 1 + 2 * gamma fp 3 + gamma fp 3 ^ 2 := by
    nlinarith [sq_nonneg (1 + gamma fp 3)]
  exact add_nonneg hfirst
    (mul_nonneg hsecond (mul_nonneg (by norm_num) fp.u_nonneg))

/-- The full *actual* support-aware solve chain.  The schedule factor is solved
by the bandwidth-two forward kernel, each accepted 2x2 middle block by the
rounded GEPP producer, and the transpose factor by the reversed bandwidth-two
kernel.  The resulting perturbation of `Lhat Dhat Lhat^T` is bounded by a
dimension-independent coefficient times the absolute factor product. -/
theorem bunch_tridiagonal_sparse_actual_solve_chain
    (fp : FPModel) (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : ℝ) * fp.u ≤ 1 / 2)
    {n : ℕ} (s : PivotSchedule n) (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (M0 tau : ℝ) (hM0 : 0 < M0) (htau : 0 ≤ tau)
    (hslack : bunchTridiagonalAlpha * tau < M0)
    (htriData : TriGrowthData fp M0 s A)
    (hbounded : TriGrowthBounded fp M0 tau s A)
    (hmiddleNB : BunchMiddleSolveNoBreakdown fp s A) :
    ∃ w : Fin n → ℝ, ∃ ΔS : Fin n → Fin n → ℝ,
      (∀ i j : Fin n,
        |ΔS i j| ≤ bunchTriSparseSolveCoeff fp *
          higham11_4_bunchKaufmanProductEntry n
            (flMixedL fp s A) (flMixedD fp s A) i j) ∧
      (∀ i : Fin n,
        ∑ j : Fin n,
          ((∑ p : Fin n, ∑ q : Fin n,
              flMixedL fp s A i p * flMixedD fp s A p q *
                flMixedL fp s A j q) + ΔS i j) *
            flBand2BackSub fp n (fun r c => flMixedL fp s A c r) w j = b i) := by
  have hval3 : gammaValid fp 3 := gammaValid_mono fp (by omega) hval9
  let L : Fin n → Fin n → ℝ := flMixedL fp s A
  let D : Fin n → Fin n → ℝ := flMixedD fp s A
  let U : Fin n → Fin n → ℝ := fun r c => flMixedL fp s A c r
  let y : Fin n → ℝ := flBand2ForwardSub fp n L b
  obtain ⟨ΔL, hΔL, hforward⟩ :=
    flMixedL_band2_forward_backward_error fp hval3 M0 s A b htriData
  obtain ⟨w, ΔD, hΔD, hmiddle⟩ :=
    flMixedD_solve_of_bunch_actual fp hval9 hsmall9 M0 tau hM0 htau hslack
      s A y hbounded hmiddleNB
  obtain ⟨ΔU, hΔU, hback⟩ :=
    flMixedL_transpose_band2_back_backward_error fp hval3 M0 s A w htriData
  let BT : Fin n → Fin n → ℝ := fun i j => (36 * fp.u) * |D i j|
  let bound : Fin n → Fin n → ℝ :=
    higham11_15_aasenChainDeltaABound n (gamma fp 3) BT L D U
  have hBT : ∀ i j : Fin n, 0 ≤ BT i j := fun i j => by
    dsimp [BT]
    exact mul_nonneg (mul_nonneg (by norm_num) fp.u_nonneg) (abs_nonneg _)
  have hchainBound : ∀ i j : Fin n,
      |higham11_15_aasenChainDeltaA n L D U ΔL ΔD ΔU i j| ≤ bound i j :=
    higham11_15_aasenChainDeltaA_abs_bound_gamma n L D U ΔL ΔD ΔU BT
      (gamma fp 3) (gamma_nonneg fp hval3) hBT hΔL hΔD hΔU
  obtain ⟨ΔS, hΔS, hsource⟩ :=
    higham11_15_aasen_chain_source_backward_error_of_components
      n (fun i j => ∑ p : Fin n, ∑ q : Fin n, L i p * D p q * U q j)
      L D U ΔL ΔD ΔU b y w
      (flBand2BackSub fp n U w) bound
      (by intro i j; rfl) hforward hmiddle hback hchainBound
  refine ⟨w, ΔS, ?_, ?_⟩
  · intro i j
    have hs := hΔS i j
    have hs' : |ΔS i j| ≤
        higham11_15_aasenChainDeltaABound n (gamma fp 3)
          (fun p q => (36 * fp.u) * |D p q|) L D (fun r c => L c r) i j := by
      simpa [bound, BT, U] using hs
    rw [aasenChainDeltaABound_eq_coeff_mul_productEntry] at hs'
    simpa [L, D, bunchTriSparseSolveCoeff] using hs'
  · intro i
    simpa [L, D, U] using hsource i

/-- Sparse block-bidiagonal norm bridge: once the already-derived constant
factor-product growth bound is supplied, the actual solve-chain perturbation is
bounded by `C_sparse c0 M0`, with `C_sparse` independent of `n`. -/
theorem bunch_tridiagonal_sparse_actual_solve_chain_norm_bridge
    (fp : FPModel) (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : ℝ) * fp.u ≤ 1 / 2)
    {n : ℕ} (s : PivotSchedule n) (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (M0 tau c0 : ℝ) (hM0 : 0 < M0) (htau : 0 ≤ tau)
    (hslack : bunchTridiagonalAlpha * tau < M0)
    (htriData : TriGrowthData fp M0 s A)
    (hbounded : TriGrowthBounded fp M0 tau s A)
    (hmiddleNB : BunchMiddleSolveNoBreakdown fp s A)
    (hfactor : ∀ i j : Fin n,
      higham11_4_bunchKaufmanProductEntry n
        (flMixedL fp s A) (flMixedD fp s A) i j ≤ c0 * M0) :
    ∃ w : Fin n → ℝ, ∃ ΔS : Fin n → Fin n → ℝ,
      (∀ i j : Fin n,
        |ΔS i j| ≤ bunchTriSparseSolveCoeff fp * (c0 * M0)) ∧
      (∀ i : Fin n,
        ∑ j : Fin n,
          ((∑ p : Fin n, ∑ q : Fin n,
              flMixedL fp s A i p * flMixedD fp s A p q *
                flMixedL fp s A j q) + ΔS i j) *
            flBand2BackSub fp n (fun r c => flMixedL fp s A c r) w j = b i) := by
  obtain ⟨w, ΔS, hΔS, hsource⟩ :=
    bunch_tridiagonal_sparse_actual_solve_chain fp hval9 hsmall9 s A b
      M0 tau hM0 htau hslack htriData hbounded hmiddleNB
  refine ⟨w, ΔS, ?_, hsource⟩
  intro i j
  exact (hΔS i j).trans (mul_le_mul_of_nonneg_left (hfactor i j)
    (bunchTriSparseSolveCoeff_nonneg fp (gammaValid_mono fp (by omega) hval9)))

end NumStability.Ch11Closure.SparseSolve
