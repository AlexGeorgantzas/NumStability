-- Algorithms/HighamChapter15ConvergenceProse.lean
--
-- Higham, 2nd ed., Chapter 15, p. 291: precise convergence prose following
-- Lemma 15.2.  This module closes the scalar monotone-convergence statement,
-- compactness/subsequence statement, both square endpoint termination bounds,
-- a conditional stationary-limit bridge, and the qualified rank-one result;
-- it also exhibits the zero-start counterexample to the printed unqualified
-- rank-one wording.

import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Order.Fin.Basic
import NumStability.Algorithms.PNormPowerMethodGeneralP

namespace NumStability
namespace Ch15

open Filter Set
open scoped Topology BigOperators

namespace PNormPair

variable {n : ℕ} (P : PNormPair n)

/-- The estimates in Algorithm 15.1 are monotone as a function of the
iteration number, not merely pairwise ordered at consecutive iterations. -/
theorem gammaSeq_monotone (x0 : Fin n → ℝ) (hx0 : P.pN x0 = 1) :
    Monotone (P.gammaSeq x0) :=
  monotone_nat_of_le_succ (P.gammaSeq_mono x0 hx0)

/-- The range of the scalar estimates is bounded above by the induced
operator norm appearing in Algorithm 15.1. -/
theorem gammaSeq_bddAbove (x0 : Fin n → ℝ) (hx0 : P.pN x0 = 1) :
    BddAbove (Set.range (P.gammaSeq x0)) := by
  refine ⟨P.opP, ?_⟩
  rintro _ ⟨k, rfl⟩
  exact P.gammaSeq_le_opP x0 hx0 k

/-- **Higham p. 291, scalar convergence.**  The increasing estimates
`γₖ = ‖A xₖ‖ₚ` actually tend to their conditional supremum.  This is the
topological `Tendsto` theorem missing from the earlier pairwise bounds. -/
theorem gammaSeq_tendsto_ciSup (x0 : Fin n → ℝ) (hx0 : P.pN x0 = 1) :
    Tendsto (P.gammaSeq x0) atTop
      (𝓝 (⨆ k : ℕ, P.gammaSeq x0 k)) :=
  tendsto_atTop_ciSup (P.gammaSeq_monotone x0 hx0)
    (P.gammaSeq_bddAbove x0 hx0)

/-- Existence form of Higham's scalar-convergence sentence, including the
source bounds on the limiting estimate. -/
theorem exists_gammaSeq_limit (x0 : Fin n → ℝ) (hx0 : P.pN x0 = 1) :
    ∃ γ : ℝ,
      Tendsto (P.gammaSeq x0) atTop (𝓝 γ) ∧
        P.gammaSeq x0 0 ≤ γ ∧ γ ≤ P.opP := by
  let γ : ℝ := ⨆ k : ℕ, P.gammaSeq x0 k
  have hlim : Tendsto (P.gammaSeq x0) atTop (𝓝 γ) := by
    simpa [γ] using P.gammaSeq_tendsto_ciSup x0 hx0
  have hmem : γ ∈ Set.Icc (P.gammaSeq x0 0) P.opP :=
    isClosed_Icc.mem_of_tendsto hlim <|
      Eventually.of_forall fun k =>
        ⟨P.gammaSeq_ge_start x0 hx0 k, P.gammaSeq_le_opP x0 hx0 k⟩
  exact ⟨γ, hlim, hmem.1, hmem.2⟩

/-- **Higham p. 291, convergent subsequence.**  Whenever the unit sphere of
the selected finite-dimensional norm is compact, the unit iterates of
Algorithm 15.1 have a convergent subsequence whose limit is again unit.

Compactness is explicit because the abstract `PNormPair` interface records
only the algebraic duality facts used by Lemma 15.2; it does not assume that
its arbitrary real-valued functional induces the ambient topology. -/
theorem xseq_has_convergent_subsequence
    (x0 : Fin n → ℝ) (hx0 : P.pN x0 = 1)
    (hcompact : IsCompact {x : Fin n → ℝ | P.pN x = 1}) :
    ∃ xbar : Fin n → ℝ, P.pN xbar = 1 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (P.xseq x0 ∘ φ) atTop (𝓝 xbar) := by
  simpa only [Set.mem_setOf_eq] using
    hcompact.tendsto_subseq (fun k => P.xseq_punit x0 hx0 k)

/-- A convergent functional iteration has a fixed-point limit whenever its
update map is continuous at that limit.  This is the topological bridge used
in the stationary-limit audit below. -/
theorem xseq_limit_is_fixed_of_continuousAt
    (x0 xbar : Fin n → ℝ)
    (hlim : Tendsto (P.xseq x0) atTop (𝓝 xbar))
    (hcont : ContinuousAt P.xnext xbar) :
    P.xnext xbar = xbar := by
  have hnext : Tendsto (P.xnext ∘ P.xseq x0) atTop (𝓝 (P.xnext xbar)) :=
    hcont.tendsto.comp hlim
  have hshift : Tendsto (fun k => P.xseq x0 (k + 1)) atTop (𝓝 xbar) :=
    hlim.comp (tendsto_add_atTop_nat 1)
  have heq : (fun k => P.xseq x0 (k + 1)) = P.xnext ∘ P.xseq x0 := by
    funext k
    rfl
  rw [heq] at hshift
  exact tendsto_nhds_unique hnext hshift

end PNormPair

/-- Concrete Euclidean closure of Higham's convergent-subsequence sentence.
No compactness premise remains: the repository already proves compactness of
the finite-dimensional Euclidean unit sphere. -/
theorem xseq_two_has_convergent_subsequence {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (x0 : Fin n → ℝ) (hx0 : vecNorm2 x0 = 1) :
    ∃ xbar : Fin n → ℝ, vecNorm2 xbar = 1 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto ((pNormPair_two hn A).xseq x0 ∘ φ) atTop (𝓝 xbar) := by
  exact (pNormPair_two hn A).xseq_has_convergent_subsequence x0 hx0
    isCompact_vecNorm2_unit_sphere

/-! ## Conditional stationary-limit bridge (`p=2`) -/

lemma normalize2_eq_self_of_unit {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (hx : vecNorm2 x = 1) :
    normalize2 hn x = x := by
  have hxne : x ≠ 0 := by
    intro h
    subst x
    have hzero : vecNorm2 (0 : Fin n → ℝ) = 0 := by
      simpa using (vecNorm2_zero (n := n))
    rw [hzero] at hx
    norm_num at hx
  unfold normalize2
  rw [if_neg hxne]
  funext i
  simp [hx]

/-- A unit fixed point of the Euclidean power update satisfies the zero
gradient equation for Higham's quotient (15.3). -/
theorem eq15_3_gradient_two_eq_zero_of_fixed {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hx : vecNorm2 x = 1)
    (hfixed : (pNormPair_two hn A).xnext x = x) :
    eq15_3_gradient_two hn A x = 0 := by
  let P := pNormPair_two hn A
  let z := P.zof x
  let γ := vecNorm2 (P.yof x)
  have hfixed' : normalize2 hn z = x := by
    change normalize2 hn (P.zof x) = x at hfixed
    simpa [z] using hfixed
  have hzgamma : vecNorm2 z = γ := by
    calc
      vecNorm2 z = ∑ i : Fin n, normalize2 hn z i * z i :=
        (normalize2_attains hn z).symm
      _ = ∑ i : Fin n, z i * x i := by
        rw [← hfixed']
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ = γ := by
        simpa [P, z, γ] using P.lemma152a x
  have hnormx : normalize2 hn x = x := normalize2_eq_self_of_unit hn x hx
  have hkkt : z = fun i => γ * normalize2 hn x i := by
    by_cases hz : z = 0
    · have hzero : vecNorm2 (0 : Fin n → ℝ) = 0 := by
        simpa using (vecNorm2_zero (n := n))
      have hγ : γ = 0 := by
        rw [hz, hzero] at hzgamma
        exact hzgamma.symm
      rw [hz, hγ]
      funext i
      simp
    · have hznorm : vecNorm2 z ≠ 0 := ne_of_gt (vecNorm2_pos_of_ne z hz)
      have hrecover : z = fun i => vecNorm2 z * normalize2 hn z i := by
        funext i
        unfold normalize2
        rw [if_neg hz]
        field_simp [hznorm]
      rw [hrecover, hzgamma, hfixed', hnormx]
  funext i
  change P.zof x i / vecNorm2 x -
      (vecNorm2 (P.yof x) / vecNorm2 x ^ 2) * normalize2 hn x i = 0
  rw [hx]
  simp only [div_one, one_pow]
  change z i - γ * normalize2 hn x i = 0
  rw [hkkt]
  ring

/-- Source-faithful conditional core of the p. 291 stationary sentence for
the concrete smooth endpoint `p=2`: if the iterates converge, the update is
continuous at their limit, and `Ax̄ ≠ 0`, then the limit is a stationary point
of `F(x)=‖Ax‖₂/‖x‖₂` (its directional gradient is zero). -/
theorem xseq_two_limit_is_stationary_of_continuousAt {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (x0 xbar : Fin n → ℝ)
    (hx0 : vecNorm2 x0 = 1)
    (hlim : Tendsto ((pNormPair_two hn A).xseq x0) atTop (𝓝 xbar))
    (hcont : ContinuousAt (pNormPair_two hn A).xnext xbar)
    (hy : (pNormPair_two hn A).yof xbar ≠ 0) :
    HasDirectionalGradientAt (eq15_3_F_two hn A) 0 xbar := by
  let P := pNormPair_two hn A
  have hnormlim : Tendsto (fun k => vecNorm2 (P.xseq x0 k)) atTop
      (𝓝 (vecNorm2 xbar)) := continuous_vecNorm2.continuousAt.tendsto.comp hlim
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hseqnorm : (fun k => vecNorm2 (P.xseq x0 k)) = fun _ : ℕ => (1 : ℝ) := by
    funext k
    exact P.xseq_punit x0 hx0 k
  have hxbar : vecNorm2 xbar = 1 := by
    rw [hseqnorm] at hnormlim
    exact tendsto_nhds_unique hnormlim hone
  have hfixed : P.xnext xbar = xbar :=
    P.xseq_limit_is_fixed_of_continuousAt x0 xbar hlim hcont
  have hgradzero : eq15_3_gradient_two hn A xbar = 0 :=
    eq15_3_gradient_two_eq_zero_of_fixed hn A xbar hxbar hfixed
  have hxbarne : xbar ≠ 0 := by
    intro h
    subst xbar
    have hzero : vecNorm2 (0 : Fin n → ℝ) = 0 := by
      simpa using (vecNorm2_zero (n := n))
    rw [hzero] at hxbar
    norm_num at hxbar
  have hgrad := eq15_3_directional_two hn A xbar hxbarne hy
  rwa [hgradzero] at hgrad

/-! ## The finite endpoint argument (`p = 1`) -/

/-- Pigeonhole core of the endpoint termination argument: a process labelled
by only `n` vertices cannot strictly increase a real-valued vertex objective
on each of its first `n` transitions. -/
theorem exists_nonincreasing_step_of_fin_labels {n : ℕ}
    (label : ℕ → Fin n) (value : Fin n → ℝ) :
    ∃ k : ℕ, k < n ∧ value (label (k + 1)) ≤ value (label k) := by
  by_contra h
  simp only [not_exists, not_and, not_le] at h
  let f : Fin (n + 1) → ℝ := fun i => value (label i.1)
  have hf : StrictMono f := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    exact h i.1 i.2
  let labels : Fin (n + 1) → Fin n := fun i => label i.1
  have hinj : Function.Injective labels := by
    intro i j hij
    apply hf.injective
    exact congrArg value hij
  have hcard := Fintype.card_le_of_injective labels hinj
  simp only [Fintype.card_fin] at hcard
  omega

/-- The column objective visited by the concrete `p=1` power method. -/
noncomputable def oneColumnValue {n : ℕ}
    (A : Fin n → Fin n → ℝ) (j : Fin n) : ℝ :=
  oneNormVec (fun i => A i j)

/-- After a `p=1` update, the next scalar estimate is the 1-norm of the
selected column.  The sign of the extreme point disappears under the norm. -/
theorem gammaSeq_one_succ_eq_column {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (x0 : Fin n → ℝ) (k : ℕ) :
    (pNormPair_one hn A).gammaSeq x0 (k + 1) =
      oneColumnValue A
        (argmaxAbs hn ((pNormPair_one hn A).zof
          ((pNormPair_one hn A).xseq x0 k))) := by
  let P := pNormPair_one hn A
  let z := P.zof (P.xseq x0 k)
  let J := argmaxAbs hn z
  let s := signVec z J
  have hs : |s| = 1 := by
    simpa [s] using abs_signVec z J
  change oneNormVec (P.yof (P.xnext (P.xseq x0 k))) =
    oneNormVec (fun i => A i J)
  have hxnext : P.xnext (P.xseq x0 k) = fun j => s * basisVec J j := by
    rfl
  rw [hxnext]
  unfold PNormPair.yof oneNormVec
  apply Finset.sum_congr rfl
  intro i _hi
  change |∑ j : Fin n, A i j * (s * basisVec J j)| = |A i J|
  have hsum : (∑ j : Fin n, A i j * (s * basisVec J j)) = s * A i J := by
    simp only [basisVec]
    rw [show (∑ j : Fin n, A i j * (s * if j = J then 1 else 0)) =
        ∑ j : Fin n, if j = J then s * A i J else 0 by
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases hj : j = J
      · subst j
        simp
        ring
      · simp [hj]]
    simp
  rw [hsum, abs_mul, hs, one_mul]

/-- **Higham p. 291, finite endpoint termination for `p=1`.**  Among the
first `n+1` tests (indices `0,…,n`), at least one satisfies the convergence
test.  Equivalently, the concrete extreme-point implementation cannot make
more than `n` strict improvements before termination. -/
theorem pNormPair_one_terminates_by_n_plus_one {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (x0 : Fin n → ℝ)
    (hx0 : oneNormVec x0 = 1) :
    ∃ k : ℕ, k ≤ n ∧
      (pNormPair_one hn A).qN
          ((pNormPair_one hn A).zof
            ((pNormPair_one hn A).xseq x0 k)) ≤
        (pNormPair_one hn A).pN
          ((pNormPair_one hn A).yof
            ((pNormPair_one hn A).xseq x0 k)) := by
  let P := pNormPair_one hn A
  let label : ℕ → Fin n := fun k => argmaxAbs hn (P.zof (P.xseq x0 k))
  let value : Fin n → ℝ := oneColumnValue A
  obtain ⟨r, hrn, hrnoninc⟩ :=
    exists_nonincreasing_step_of_fin_labels label value
  by_cases htest : P.qN (P.zof (P.xseq x0 (r + 1))) ≤
      P.pN (P.yof (P.xseq x0 (r + 1)))
  · exact ⟨r + 1, by omega, htest⟩
  · have hstrict : P.gammaSeq x0 (r + 1) < P.gammaSeq x0 (r + 2) := by
      have hfirst : P.pN (P.yof (P.xseq x0 (r + 1))) <
          P.qN (P.zof (P.xseq x0 (r + 1))) :=
        (lemma152b_strict P (P.xseq x0 (r + 1))).mp htest
      have hunit : P.pN (P.xseq x0 (r + 1)) = 1 :=
        P.xseq_punit x0 hx0 (r + 1)
      have hsecond := (P.lemma152b (P.xseq x0 (r + 1)) hunit).2.1
      exact lt_of_lt_of_le hfirst (by simpa [PNormPair.gammaSeq, PNormPair.xseq] using hsecond)
    have hcol1 : P.gammaSeq x0 (r + 1) = value (label r) := by
      simpa [P, label, value] using gammaSeq_one_succ_eq_column hn A x0 r
    have hcol2 : P.gammaSeq x0 (r + 2) = value (label (r + 1)) := by
      simpa [P, label, value, Nat.add_assoc] using
        gammaSeq_one_succ_eq_column hn A x0 (r + 1)
    rw [hcol1, hcol2] at hstrict
    exact (not_lt_of_ge hrnoninc hstrict).elim

/-! ## The symmetric finite endpoint argument (`p = ∞`) -/

/-- The sign vector has infinity norm exactly one in positive dimension. -/
lemma sign_infNorm_eq_one {n : ℕ} (hn : 0 < n) (v : Fin n → ℝ) :
    infNormVec (signVec v) = 1 := by
  apply le_antisymm
  · exact sign_qunit_one v
  · have hcoord := abs_le_infNormVec (signVec v) (⟨0, hn⟩ : Fin n)
    rwa [abs_signVec] at hcoord

/-- Hölder's inequality for the endpoint pair `p=∞`, `q=1`. -/
lemma holder_inf {n : ℕ} (u v : Fin n → ℝ) :
    (∑ i : Fin n, u i * v i) ≤ oneNormVec u * infNormVec v := by
  calc
    (∑ i : Fin n, u i * v i)
        ≤ ∑ i : Fin n, |u i * v i| :=
          Finset.sum_le_sum (fun i _hi => le_abs_self (u i * v i))
    _ = ∑ i : Fin n, |u i| * |v i| := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [abs_mul]
    _ ≤ ∑ i : Fin n, |u i| * infNormVec v := by
      apply Finset.sum_le_sum
      intro i _hi
      exact mul_le_mul_of_nonneg_left (abs_le_infNormVec v i) (abs_nonneg _)
    _ = oneNormVec u * infNormVec v := by
      unfold oneNormVec
      rw [Finset.sum_mul]

/-- The concrete `p=∞`, `q=1` specialization of Algorithm 15.1.  Both dual
maps choose extreme points: `dualp(y)=±e_J` and `dualq(z)=sign(z)`. -/
noncomputable def pNormPair_inf {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) : PNormPair n where
  A := A
  pN := infNormVec
  qN := oneNormVec
  opP := infNorm A
  dp := dualq_one hn
  dq := signVec
  pN_nonneg := infNormVec_nonneg
  dp_attains := dualq_one_attains hn
  dp_qunit := fun v => le_of_eq (dualq_one_punit hn v)
  dq_attains := sign_attains_one
  dq_punit := sign_infNorm_eq_one hn
  holder := holder_inf
  op_bound := fun v => by
    simpa [PNormPair.yof, matMulVec] using infNormVec_matMulVec_le hn A v

/-- The row objective used in the `p=∞` endpoint pigeonhole argument. -/
noncomputable def infRowValue {n : ℕ}
    (A : Fin n → Fin n → ℝ) (i : Fin n) : ℝ :=
  oneNormVec (fun j => A i j)

/-- For `p=∞`, `z=Aᵀdualp(y)` has 1-norm equal to the 1-norm of the row
selected by the extreme dual vector `dualp(y)=±e_J`. -/
theorem qNorm_zof_inf_eq_row {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    (pNormPair_inf hn A).qN ((pNormPair_inf hn A).zof x) =
      infRowValue A
        (argmaxAbs hn ((pNormPair_inf hn A).yof x)) := by
  let P := pNormPair_inf hn A
  let y := P.yof x
  let J := argmaxAbs hn y
  let s := signVec y J
  have hs : |s| = 1 := by
    simpa [s] using abs_signVec y J
  change oneNormVec (P.zof x) = oneNormVec (fun j => A J j)
  have hz : P.zof x = fun j => s * A J j := by
    funext j
    change (∑ i : Fin n, A i j * (s * basisVec J i)) = s * A J j
    simp only [basisVec]
    rw [show (∑ i : Fin n, A i j * (s * if i = J then 1 else 0)) =
        ∑ i : Fin n, if i = J then s * A J j else 0 by
      apply Finset.sum_congr rfl
      intro i _hi
      by_cases hi : i = J
      · subst i
        simp
        ring
      · simp [hi]]
    simp
  rw [hz]
  unfold oneNormVec
  apply Finset.sum_congr rfl
  intro j _hj
  rw [abs_mul, hs, one_mul]

/-- **Higham p. 291, finite endpoint termination for `p=∞` (square case).**
Among tests `0,…,n`, one succeeds.  The proof follows Higham's row-vertex
argument: off convergence, the 1-norms of successively selected rows strictly
increase, which cannot happen for `n+1` labels drawn from `n` rows.

The source introduces Algorithm 15.1 for `A : ℝ^{m×n}` but later says `n+1`
for both endpoints.  For rectangular `p=∞` the same argument counts the `m`
codomain vertices and gives `m+1`; the repository's `PNormPair` is square, so
the displayed `n+1` statement is literally valid here. -/
theorem pNormPair_inf_terminates_by_n_plus_one {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (x0 : Fin n → ℝ)
    (hx0 : infNormVec x0 = 1) :
    ∃ k : ℕ, k ≤ n ∧
      (pNormPair_inf hn A).qN
          ((pNormPair_inf hn A).zof
            ((pNormPair_inf hn A).xseq x0 k)) ≤
        (pNormPair_inf hn A).pN
          ((pNormPair_inf hn A).yof
            ((pNormPair_inf hn A).xseq x0 k)) := by
  let P := pNormPair_inf hn A
  let label : ℕ → Fin n := fun k =>
    argmaxAbs hn (P.yof (P.xseq x0 k))
  let value : Fin n → ℝ := infRowValue A
  obtain ⟨r, hrn, hrnoninc⟩ :=
    exists_nonincreasing_step_of_fin_labels label value
  by_cases htest0 : P.qN (P.zof (P.xseq x0 r)) ≤
      P.pN (P.yof (P.xseq x0 r))
  · exact ⟨r, by omega, htest0⟩
  by_cases htest1 : P.qN (P.zof (P.xseq x0 (r + 1))) ≤
      P.pN (P.yof (P.xseq x0 (r + 1)))
  · exact ⟨r + 1, by omega, htest1⟩
  · have hunit : P.pN (P.xseq x0 r) = 1 := P.xseq_punit x0 hx0 r
    have hmiddle := (P.lemma152b (P.xseq x0 r) hunit).2.1
    have hstrict1 : P.pN (P.yof (P.xseq x0 (r + 1))) <
        P.qN (P.zof (P.xseq x0 (r + 1))) :=
      (lemma152b_strict P (P.xseq x0 (r + 1))).mp htest1
    have hvalues : value (label r) < value (label (r + 1)) := by
      have hrow0 : P.qN (P.zof (P.xseq x0 r)) = value (label r) := by
        have hraw := qNorm_zof_inf_eq_row hn A (P.xseq x0 r)
        change P.qN (P.zof (P.xseq x0 r)) =
          infRowValue A (argmaxAbs hn (P.yof (P.xseq x0 r))) at hraw
        simpa [label, value] using hraw
      have hrow1 : P.qN (P.zof (P.xseq x0 (r + 1))) =
          value (label (r + 1)) := by
        have hraw := qNorm_zof_inf_eq_row hn A (P.xseq x0 (r + 1))
        change P.qN (P.zof (P.xseq x0 (r + 1))) =
          infRowValue A (argmaxAbs hn (P.yof (P.xseq x0 (r + 1)))) at hraw
        simpa [label, value] using hraw
      rw [← hrow0, ← hrow1]
      exact lt_of_le_of_lt
        (by simpa [PNormPair.xseq] using hmiddle) hstrict1
    exact (not_lt_of_ge hrnoninc hvalues).elim

/-! ## Rank-one matrices: qualified theorem and zero-start discrepancy -/

/-- Pairing a nonzero scalar multiple of `v` with its Euclidean normalized
dual has magnitude `‖v‖₂`.  This is the small algebraic fact behind the
rank-one two-step calculation. -/
lemma abs_dot_normalize2_smul {n : ℕ} (hn : 0 < n)
    (v : Fin n → ℝ) (c : ℝ) (hc : c ≠ 0) :
    |∑ i : Fin n, v i * normalize2 hn (fun j => c * v j) i| = vecNorm2 v := by
  let w : Fin n → ℝ := fun j => c * v j
  let d : Fin n → ℝ := normalize2 hn w
  have hattain : (∑ i : Fin n, d i * w i) = vecNorm2 w := by
    simpa [d] using normalize2_attains hn w
  have hscale : vecNorm2 w = |c| * vecNorm2 v := by
    simpa [w] using vecNorm2_smul c v
  have hrel : c * (∑ i : Fin n, v i * d i) = vecNorm2 w := by
    calc
      c * (∑ i : Fin n, v i * d i) = ∑ i : Fin n, d i * w i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        simp [w]
        ring
      _ = vecNorm2 w := hattain
  have habs := congrArg abs hrel
  rw [abs_mul, abs_of_nonneg (vecNorm2_nonneg w), hscale] at habs
  have hcpos : 0 < |c| := abs_pos.mpr hc
  nlinarith

/-- The exact Euclidean operator norm of a real rank-one matrix `u vᵀ`. -/
theorem opNorm2_rankOne_eq {n : ℕ} (hn : 0 < n)
    (u v : Fin n → ℝ) :
    opNorm2 (fun i j => u i * v j) = vecNorm2 u * vecNorm2 v := by
  let A : Fin n → Fin n → ℝ := fun i j => u i * v j
  have haction (x : Fin n → ℝ) :
      matMulVec n A x = fun i => (∑ j : Fin n, v j * x j) * u i := by
    funext i
    simp only [matMulVec, A]
    calc
      (∑ j : Fin n, u i * v j * x j) =
          u i * (∑ j : Fin n, v j * x j) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _hj
            ring
      _ = (∑ j : Fin n, v j * x j) * u i := by ring
  apply le_antisymm
  · apply opNorm2_le_of_unit_vecNorm2_bound A
      (mul_nonneg (vecNorm2_nonneg u) (vecNorm2_nonneg v))
    intro x hx
    rw [haction x, vecNorm2_smul]
    have hdot := abs_vecInnerProduct_le_vecNorm2_mul v x
    rw [hx, mul_one] at hdot
    have hmul := mul_le_mul_of_nonneg_right hdot (vecNorm2_nonneg u)
    nlinarith
  · let x : Fin n → ℝ := normalize2 hn v
    have hx : vecNorm2 x = 1 := normalize2_unit hn v
    have hdot : (∑ j : Fin n, v j * x j) = vecNorm2 v := by
      simpa [x, mul_comm] using normalize2_attains hn v
    have hop := opNorm2Le_opNorm2 A x
    rw [haction x, hdot, vecNorm2_smul,
      abs_of_nonneg (vecNorm2_nonneg v), hx, mul_one] at hop
    simpa [A, mul_comm] using hop

/-- **Qualified rank-one convergence statement.**  Let `A = u vᵀ`, with
`u ≠ 0`, and suppose the initial vector is not annihilated by the row
factor (`vᵀx₀ ≠ 0`).  Then the first updated iterate already attains
`γ₁ = ‖A‖₂ = ‖u‖₂‖v‖₂`, and the following test succeeds.  Thus, with Higham's
iteration count, the concrete `p=2` algorithm converges on its second step.

The non-annihilation premise is essential for a total implementation of
`dualp(0)`; the counterexample below shows why the printed "whatever `x₀`"
sentence is not valid uniformly over the allowed choice at zero. -/
theorem rankOne_two_converges_second_step_of_pairing_ne_zero {n : ℕ}
    (hn : 0 < n) (u v x0 : Fin n → ℝ)
    (hu : u ≠ 0)
    (hpair : (∑ j : Fin n, v j * x0 j) ≠ 0) :
    let A : Fin n → Fin n → ℝ := fun i j => u i * v j
    let P := pNormPair_two hn A
    P.gammaSeq x0 1 = opNorm2 A ∧
      P.gammaSeq x0 1 = vecNorm2 u * vecNorm2 v ∧
      P.qN (P.zof (P.xseq x0 1)) ≤ P.pN (P.yof (P.xseq x0 1)) := by
  let A : Fin n → Fin n → ℝ := fun i j => u i * v j
  let P := pNormPair_two hn A
  let c : ℝ := ∑ j : Fin n, v j * x0 j
  let d : Fin n → ℝ := normalize2 hn (fun i => c * u i)
  let a : ℝ := ∑ i : Fin n, u i * d i
  have hy0 : P.yof x0 = fun i => c * u i := by
    funext i
    change (∑ j : Fin n, (u i * v j) * x0 j) = c * u i
    dsimp [c]
    calc
      (∑ j : Fin n, u i * v j * x0 j) =
          u i * (∑ j : Fin n, v j * x0 j) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _hj
            ring
      _ = (∑ j : Fin n, v j * x0 j) * u i := by ring
  have haabs : |a| = vecNorm2 u := by
    simpa [a, d] using abs_dot_normalize2_smul hn u c hpair
  have hupos : 0 < vecNorm2 u := vecNorm2_pos_of_ne u hu
  have hane : a ≠ 0 := by
    intro ha
    rw [ha, abs_zero] at haabs
    linarith
  have hz0 : P.zof x0 = fun j => a * v j := by
    funext j
    change (∑ i : Fin n, (u i * v j) * normalize2 hn (P.yof x0) i) = a * v j
    rw [hy0]
    dsimp [a, d]
    calc
      (∑ i : Fin n, u i * v j * normalize2 hn (fun i => c * u i) i) =
          v j * (∑ i : Fin n, u i * normalize2 hn (fun i => c * u i) i) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _hi
            ring
      _ = (∑ i : Fin n, u i * normalize2 hn (fun i => c * u i) i) * v j := by
        ring
  have hx1 : P.xseq x0 1 = normalize2 hn (fun j => a * v j) := by
    change normalize2 hn (P.zof x0) = _
    rw [hz0]
  let b : ℝ := ∑ j : Fin n, v j * normalize2 hn (fun r => a * v r) j
  have hbabs : |b| = vecNorm2 v := by
    simpa [b] using abs_dot_normalize2_smul hn v a hane
  have hy1 : P.yof (P.xseq x0 1) = fun i => b * u i := by
    funext i
    change (∑ j : Fin n, (u i * v j) * P.xseq x0 1 j) = b * u i
    rw [hx1]
    dsimp [b]
    calc
      (∑ j : Fin n, u i * v j * normalize2 hn (fun j => a * v j) j) =
          u i * (∑ j : Fin n, v j * normalize2 hn (fun r => a * v r) j) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _hj
            ring
      _ = (∑ j : Fin n, v j * normalize2 hn (fun r => a * v r) j) * u i := by
        ring
  have hgamma : P.gammaSeq x0 1 = vecNorm2 u * vecNorm2 v := by
    change vecNorm2 (P.yof (P.xseq x0 1)) = _
    rw [hy1, vecNorm2_smul, hbabs]
    ring
  have hop : opNorm2 A = vecNorm2 u * vecNorm2 v :=
    opNorm2_rankOne_eq hn u v
  have hunit : P.pN (P.xseq x0 1) = 1 := by
    simpa [P] using P.dq_punit (P.zof x0)
  have hchain := P.lemma152b (P.xseq x0 1) hunit
  have htest : P.qN (P.zof (P.xseq x0 1)) ≤
      P.pN (P.yof (P.xseq x0 1)) := by
    calc
      P.qN (P.zof (P.xseq x0 1))
          ≤ P.pN (P.yof (P.xnext (P.xseq x0 1))) := hchain.2.1
      _ ≤ P.opP := hchain.2.2
      _ = P.pN (P.yof (P.xseq x0 1)) := by
        change opNorm2 A = P.gammaSeq x0 1
        rw [hop, hgamma]
  exact ⟨hgamma.trans hop.symm, hgamma, htest⟩

/-- Rank-one factors for the zero-start discrepancy in dimension two. -/
noncomputable def rankOneZeroStartFactor : Fin 2 → ℝ := basisVec (1 : Fin 2)

/-- The rank-one matrix `e₁e₁ᵀ` used to audit the printed "whatever `x₀`"
claim. -/
noncomputable def rankOneZeroStartMatrix : Fin 2 → Fin 2 → ℝ :=
  fun i j => rankOneZeroStartFactor i * rankOneZeroStartFactor j

/-- Initial vector `e₀`, annihilated by `e₁e₁ᵀ`. -/
noncomputable def rankOneZeroStartX : Fin 2 → ℝ := basisVec (0 : Fin 2)

lemma rankOneZeroStart_y_eq_zero :
    (pNormPair_two (by omega : 0 < 2) rankOneZeroStartMatrix).yof
      rankOneZeroStartX = 0 := by
  funext i
  fin_cases i <;>
    simp [PNormPair.yof, pNormPair_two, rankOneZeroStartMatrix,
      rankOneZeroStartFactor, rankOneZeroStartX, basisVec]

lemma rankOneZeroStart_z_eq_zero :
    (pNormPair_two (by omega : 0 < 2) rankOneZeroStartMatrix).zof
      rankOneZeroStartX = 0 := by
  funext j
  change (∑ i : Fin 2, rankOneZeroStartMatrix i j *
    normalize2 (by omega : 0 < 2)
      ((pNormPair_two (by omega : 0 < 2) rankOneZeroStartMatrix).yof
        rankOneZeroStartX) i) = 0
  rw [rankOneZeroStart_y_eq_zero]
  fin_cases j <;>
    simp [normalize2, e0Vec, rankOneZeroStartMatrix,
      rankOneZeroStartFactor, basisVec]

lemma rankOneZeroStart_xnext_fixed :
    (pNormPair_two (by omega : 0 < 2) rankOneZeroStartMatrix).xnext
      rankOneZeroStartX = rankOneZeroStartX := by
  change normalize2 (by omega : 0 < 2)
    ((pNormPair_two (by omega : 0 < 2) rankOneZeroStartMatrix).zof
      rankOneZeroStartX) = rankOneZeroStartX
  rw [rankOneZeroStart_z_eq_zero]
  funext i
  fin_cases i <;> simp [normalize2, e0Vec, rankOneZeroStartX, basisVec]

lemma rankOneZeroStart_xseq_fixed (k : ℕ) :
    (pNormPair_two (by omega : 0 < 2) rankOneZeroStartMatrix).xseq
      rankOneZeroStartX k = rankOneZeroStartX := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [PNormPair.xseq, ih]
      exact rankOneZeroStart_xnext_fixed

lemma rankOneZeroStart_gamma_eq_zero (k : ℕ) :
    (pNormPair_two (by omega : 0 < 2) rankOneZeroStartMatrix).gammaSeq
      rankOneZeroStartX k = 0 := by
  rw [PNormPair.gammaSeq, rankOneZeroStart_xseq_fixed]
  simp [PNormPair.yof, pNormPair_two, rankOneZeroStartMatrix,
    rankOneZeroStartFactor, rankOneZeroStartX, basisVec, vecNorm2, vecNorm2Sq]

lemma rankOneZeroStart_factor_norm_product :
    vecNorm2 rankOneZeroStartFactor * vecNorm2 rankOneZeroStartFactor = 1 := by
  norm_num [rankOneZeroStartFactor, basisVec, vecNorm2, vecNorm2Sq]

/-- **Source discrepancy, Higham p. 291.**  With the repository's valid
choice `dualp(0)=e₀`, the rank-one matrix `e₁e₁ᵀ` and start `x₀=e₀` remain
stuck at estimate zero.  Hence the unqualified printed claim that rank-one
matrices converge on the second step "whatever `x₀`" is false for the stated
set-valued dual convention. -/
theorem rankOne_second_step_whatever_x0_false :
    (pNormPair_two (by omega : 0 < 2) rankOneZeroStartMatrix).gammaSeq
        rankOneZeroStartX 1 ≠
      vecNorm2 rankOneZeroStartFactor * vecNorm2 rankOneZeroStartFactor := by
  rw [rankOneZeroStart_gamma_eq_zero, rankOneZeroStart_factor_norm_product]
  norm_num

/-- Audit-grade package for the rank-one source discrepancy.  The concrete
start is in Algorithm 15.1's unit-sphere domain, the displayed factor is
nonzero (so its outer product is genuinely rank one), and the first updated
estimate is not the exact operator norm. -/
theorem rankOne_second_step_whatever_x0_unit_opNorm_counterexample :
    vecNorm2 rankOneZeroStartX = 1 ∧
      rankOneZeroStartFactor ≠ 0 ∧
      (pNormPair_two (by omega : 0 < 2) rankOneZeroStartMatrix).gammaSeq
          rankOneZeroStartX 1 ≠ opNorm2 rankOneZeroStartMatrix := by
  constructor
  · norm_num [rankOneZeroStartX, basisVec, vecNorm2, vecNorm2Sq]
  constructor
  · intro hzero
    have hcoord := congrFun hzero (1 : Fin 2)
    norm_num [rankOneZeroStartFactor, basisVec] at hcoord
  · have hop :
        opNorm2 rankOneZeroStartMatrix =
          vecNorm2 rankOneZeroStartFactor *
            vecNorm2 rankOneZeroStartFactor := by
      simpa [rankOneZeroStartMatrix] using
        (opNorm2_rankOne_eq (by omega : 0 < 2)
          rankOneZeroStartFactor rankOneZeroStartFactor)
    rw [hop]
    exact rankOne_second_step_whatever_x0_false

end Ch15
end NumStability
