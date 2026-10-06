-- Algorithms/HighamChapter15BoydBridges.lean
--
-- Higham, 2nd ed., Chapter 15, p. 291: foundations for the two
-- convergence statements attributed there to Boyd (1974).
--
-- The chapter does not reproduce Boyd's definition of a "strong local
-- maximum" or either cited proof.  Accordingly, this file does not claim to
-- close those two citation-only rows.  It proves dependencies that do not
-- assume either desired conclusion:
--
-- * the canonical smooth l^p dual chosen earlier is the explicit gradient;
-- * the literal rectangular iteration preserves strict positivity under the
--   printed nonnegative/irreducible-Gram hypotheses;
-- * the printed hypotheses supply a compact invariant carrier, continuity of
--   the actual update (including boundary coordinates), and a strictly
--   positive fixed point attaining the exact induced norm;
-- * a derivative operator-norm bound below one constructs an explicit local
--   contraction radius and geometric error bound for the actual iteration;
-- * the sole remaining global Boyd foundation is uniqueness of that positive
--   normalized nonlinear fixed point; once supplied, compact strict-Lyapunov
--   dynamics yield global iterate and norm-estimate convergence.

import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Order.Compact
import NumStability.Algorithms.PNormPowerMethodRect
import NumStability.Algorithms.HighamChapter15ConvergenceProse

namespace NumStability
namespace Ch15

open Filter Function Set
open scoped BigOperators Topology

/-! ## The smooth dual is the explicit l^p gradient -/

/-- In the smooth range, the normalized dual selected by Holder attainment is
the explicit gradient of the finite-dimensional real `l^p` norm.  This
extracts an equality that was previously only used internally in the proof of
`realLpDual_hasDirectionalGradientAt`. -/
theorem realLpDual_eq_realLpGradient {n : ℕ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (x : Fin n → ℝ) (hx : x ≠ 0) :
    realLpDual hpq x = realLpGradient p x := by
  have hdual := realLpDual_hasDirectionalGradientAt hpq x hx
  have hgrad := realVecLpNorm_hasDirectionalGradientAt hpq.lt x hx
  funext i
  have hi := (hdual (basisVec i)).unique (hgrad (basisVec i))
  simpa [basisVec] using hi

/-- A positive coordinate of a nonzero vector gives a positive coordinate of
the explicit smooth `l^p` gradient. -/
theorem realLpGradient_pos_of_pos_coord {n : ℕ} {p : ℝ}
    (hp : 1 < p) (x : Fin n → ℝ) (hx : x ≠ 0) (i : Fin n)
    (hi : 0 < x i) :
    0 < realLpGradient p x i := by
  have hsum : 0 < realLpPowerSum p x := realLpPowerSum_pos hp hx
  have hsumPow : 0 < (realLpPowerSum p x) ^ (p⁻¹ - 1) :=
    Real.rpow_pos_of_pos hsum _
  have habs : 0 < |x i| := abs_pos.mpr (ne_of_gt hi)
  have hcoordPow : 0 < |x i| ^ (p - 2) :=
    Real.rpow_pos_of_pos habs _
  unfold realLpGradient
  exact mul_pos hsumPow (mul_pos hcoordPow hi)

/-- A nonnegative coordinate gives a nonnegative coordinate of the smooth
`l^p` gradient (away from the zero vector). -/
theorem realLpGradient_nonneg_of_nonneg_coord {n : ℕ} {p : ℝ}
    (hp : 1 < p) (x : Fin n → ℝ) (hx : x ≠ 0) (i : Fin n)
    (hi : 0 ≤ x i) :
    0 ≤ realLpGradient p x i := by
  rcases hi.eq_or_lt with hzero | hpos
  · have hxi : x i = 0 := hzero.symm
    simp [realLpGradient, hxi]
  · exact (realLpGradient_pos_of_pos_coord hp x hx i hpos).le

/-- The canonical normalized dual of a strictly positive vector is strictly
positive coordinatewise. -/
theorem realLpDual_pos_of_pos {n : ℕ} (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q) (x : Fin n → ℝ)
    (hxpos : ∀ i, 0 < x i) :
    ∀ i, 0 < realLpDual hpq x i := by
  have hx : x ≠ 0 := by
    intro hzero
    let i0 : Fin n := ⟨0, hn⟩
    have hi := congrFun hzero i0
    exact (ne_of_gt (hxpos i0)) (by simpa using hi)
  rw [realLpDual_eq_realLpGradient hpq x hx]
  intro i
  exact realLpGradient_pos_of_pos_coord hpq.lt x hx i (hxpos i)

/-- The smooth normalized dual of a nonzero nonnegative vector is
nonnegative coordinatewise. -/
theorem realLpDual_nonneg_of_nonneg {n : ℕ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (x : Fin n → ℝ) (hx : x ≠ 0)
    (hxnonneg : ∀ i, 0 ≤ x i) :
    ∀ i, 0 ≤ realLpDual hpq x i := by
  rw [realLpDual_eq_realLpGradient hpq x hx]
  intro i
  exact realLpGradient_nonneg_of_nonneg_coord hpq.lt x hx i (hxnonneg i)

/-- The total unit dual agrees with the smooth dual, and hence is positive,
away from zero. -/
theorem realLpDualUnit_pos_of_pos {n : ℕ} (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q) (x : Fin n → ℝ)
    (hxpos : ∀ i, 0 < x i) :
    ∀ i, 0 < realLpDualUnit hn hpq x i := by
  have hx : x ≠ 0 := by
    intro hzero
    let i0 : Fin n := ⟨0, hn⟩
    have hi := congrFun hzero i0
    exact (ne_of_gt (hxpos i0)) (by simpa using hi)
  simpa [realLpDualUnit, hx] using realLpDual_pos_of_pos hn hpq x hxpos

/-- Continuity of the concrete finite-dimensional real `l^p` norm in the
smooth range.  This is used below to make the Algorithm 15.1 objective an
actual Lyapunov function, rather than an abstract scalar interface. -/
theorem continuous_realVecLpNorm {n : ℕ} {p : ℝ} (hp : 0 < p) :
    Continuous (realVecLpNorm (n := n) p) := by
  rw [show realVecLpNorm (n := n) p =
      fun x : Fin n → ℝ => (∑ i : Fin n, |x i| ^ p) ^ p⁻¹ by
    funext x
    exact realVecLpNorm_eq_sum_rpow hp x]
  have hsum : Continuous (fun x : Fin n → ℝ =>
      ∑ i : Fin n, |x i| ^ p) := by
    apply continuous_finset_sum
    intro i _hi
    exact (continuous_apply i).abs.rpow_const (fun _ => Or.inr hp.le)
  exact hsum.rpow_const (fun _ => Or.inr (inv_nonneg.mpr hp.le))

/-! ## The raw positive start is normalized without losing positivity -/

/-- Real scalar homogeneity of the concrete finite-dimensional `l^p` norm. -/
theorem realVecLpNorm_smul_real {n : ℕ} {p : ℝ} (hp : 1 ≤ p)
    (c : ℝ) (x : Fin n → ℝ) :
    realVecLpNorm p (fun i => c * x i) = |c| * realVecLpNorm p x := by
  haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact hp⟩
  have h := (complexVecLpNorm_isComplexVectorNorm
    (n := n) (ENNReal.ofReal p)).smul (c : ℂ)
      (fun i : Fin n => (x i : ℂ))
  simpa [realVecLpNorm, complexVecSMul, Complex.norm_real,
    Real.norm_eq_abs] using h

/-- The literal initial normalization `x := x₀ / ‖x₀‖_p` in Algorithm
15.1. -/
noncomputable def realLpNormalizedStart {n : ℕ} (p : ℝ)
    (x0 : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (realVecLpNorm p x0)⁻¹ * x0 i

/-- A strictly positive raw start remains strictly positive after Algorithm
15.1's initial normalization. -/
theorem realLpNormalizedStart_pos {n : ℕ} (hn : 0 < n) {p : ℝ}
    (hp : 1 ≤ p) (x0 : Fin n → ℝ) (hx0 : ∀ i, 0 < x0 i) :
    ∀ i, 0 < realLpNormalizedStart p x0 i := by
  have hx0ne : x0 ≠ 0 := by
    intro hzero
    let i0 : Fin n := ⟨0, hn⟩
    have hi := congrFun hzero i0
    exact (ne_of_gt (hx0 i0)) (by simpa using hi)
  have hnorm : 0 < realVecLpNorm p x0 := realVecLpNorm_pos hp hx0ne
  intro i
  exact mul_pos (inv_pos.mpr hnorm) (hx0 i)

/-- The normalized positive start has exact unit `p`-norm. -/
theorem realLpNormalizedStart_norm_eq_one {n : ℕ} (hn : 0 < n) {p : ℝ}
    (hp : 1 ≤ p) (x0 : Fin n → ℝ) (hx0 : ∀ i, 0 < x0 i) :
    realVecLpNorm p (realLpNormalizedStart p x0) = 1 := by
  have hx0ne : x0 ≠ 0 := by
    intro hzero
    let i0 : Fin n := ⟨0, hn⟩
    have hi := congrFun hzero i0
    exact (ne_of_gt (hx0 i0)) (by simpa using hi)
  have hnorm : 0 < realVecLpNorm p x0 := realVecLpNorm_pos hp hx0ne
  rw [show realLpNormalizedStart p x0 =
      (fun i => (realVecLpNorm p x0)⁻¹ * x0 i) from rfl,
    realVecLpNorm_smul_real hp]
  rw [abs_of_pos (inv_pos.mpr hnorm)]
  exact inv_mul_cancel₀ (ne_of_gt hnorm)

/-! ## Rectangular scalar convergence at the source dimensions -/

/-- Consecutive monotonicity from rectangular Lemma 15.2 upgrades to
monotonicity of the complete estimate sequence. -/
theorem rect_gammaSeq_monotone {m n : ℕ} (P : RectPNormPair m n)
    (x0 : Fin n → ℝ) (hx0 : P.pIn x0 = 1) :
    Monotone (P.gammaSeq x0) :=
  monotone_nat_of_le_succ (P.gammaSeq_mono x0 hx0)

/-- The rectangular estimate sequence is bounded above by the induced
operator norm. -/
theorem rect_gammaSeq_bddAbove {m n : ℕ} (P : RectPNormPair m n)
    (x0 : Fin n → ℝ) (hx0 : P.pIn x0 = 1) :
    BddAbove (Set.range (P.gammaSeq x0)) := by
  refine ⟨P.opP, ?_⟩
  rintro _ ⟨k, rfl⟩
  exact P.gammaSeq_le_opP x0 hx0 k

/-- Higham p. 291's scalar-convergence sentence for the literal rectangular
Algorithm 15.1 trace. -/
theorem rect_gammaSeq_tendsto_ciSup {m n : ℕ} (P : RectPNormPair m n)
    (x0 : Fin n → ℝ) (hx0 : P.pIn x0 = 1) :
    Tendsto (P.gammaSeq x0) atTop (𝓝 (⨆ k : ℕ, P.gammaSeq x0 k)) :=
  tendsto_atTop_ciSup (rect_gammaSeq_monotone P x0 hx0)
    (rect_gammaSeq_bddAbove P x0 hx0)

/-! ## In the smooth range, the scalar test is exactly a fixed-point test -/

/-- Uniqueness of the Holder normer in the smooth range.  A unit `p`-norm
vector attaining the dual pairing against nonzero `z` is the canonical
normalized `q`-dual of `z`. -/
theorem realLpNormer_eq_dual {n : ℕ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (z x : Fin n → ℝ)
    (hz : z ≠ 0) (hxunit : realVecLpNorm p x = 1)
    (hattain : (∑ i : Fin n, x i * z i) = realVecLpNorm q z) :
    x = realLpDual hpq.symm z := by
  have hsub : IsSubgradient (realVecLpNorm q) z x := by
    intro v
    have hvnonneg : 0 ≤ realVecLpNorm q v := by
      haveI : Fact (1 ≤ ENNReal.ofReal q) := ⟨by
        rw [ENNReal.one_le_ofReal]
        exact le_of_lt hpq.symm.lt⟩
      exact (complexVecLpNorm_isComplexVectorNorm
        (n := n) (ENNReal.ofReal q)).nonneg _
    have hdot : (∑ i : Fin n, x i * v i) ≤ realVecLpNorm q v := by
      calc
        (∑ i : Fin n, x i * v i) ≤ |∑ i : Fin n, x i * v i| :=
          le_abs_self _
        _ ≤ realVecLpNorm p x * realVecLpNorm q v :=
          realVecLpNorm_holder hpq.symm x v
        _ = realVecLpNorm q v := by rw [hxunit, one_mul]
    calc
      realVecLpNorm q z + (∑ i : Fin n, x i * (v i - z i))
          = ∑ i : Fin n, x i * v i := by
            rw [← hattain]
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ ≤ realVecLpNorm q v := hdot
  exact unique_subgradient_of_directional_gradient
    (realVecLpNorm q) z (realLpDual hpq.symm z) x
    (realLpDual_hasDirectionalGradientAt hpq.symm z hz) hsub

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

/-! ## The printed nonnegative/irreducible hypotheses preserve positivity -/

/-- The `n × n` Gram matrix `Aᵀ A` for a literal rectangular real matrix. -/
noncomputable def rectGram {m n : ℕ} (A : Fin m → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun j k => ∑ i : Fin m, A i j * A i k

/-- Entrywise nonnegativity of `A` implies entrywise nonnegativity of its
Gram matrix. -/
theorem rectGram_nonneg {m n : ℕ} {A : Fin m → Fin n → ℝ}
    (hA : ∀ i j, 0 ≤ A i j) :
    ∀ j k, 0 ≤ rectGram A j k := by
  intro j k
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hA i j) (hA i k)

/-- For a nonnegative matrix in positive domain dimension, irreducibility of
`Aᵀ A` forces every column of `A` to contain a positive entry. -/
theorem exists_pos_in_column_of_rectGram_irreducible {m n : ℕ}
    [Nontrivial (Fin n)] {A : Fin m → Fin n → ℝ}
    (hA : ∀ i j, 0 ≤ A i j)
    (hGram : Matrix.IsIrreducible
      (Matrix.of (rectGram A) : Matrix (Fin n) (Fin n) ℝ)) :
    ∀ j, ∃ i, 0 < A i j := by
  intro j
  obtain ⟨k, hjk⟩ := hGram.exists_pos j
  change 0 < ∑ i : Fin m, A i j * A i k at hjk
  have hterms : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      0 ≤ A i j * A i k := fun i _ => mul_nonneg (hA i j) (hA i k)
  obtain ⟨i, _hi, hprod⟩ :=
    (Finset.sum_pos_iff_of_nonneg hterms).mp hjk
  refine ⟨i, ?_⟩
  nlinarith [hA i j, hA i k]

/-- A strictly positive input has a strictly positive image in every row that
contains a positive matrix entry. -/
theorem rectMatVec_pos_of_row_entry {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {x : Fin n → ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hx : ∀ j, 0 < x j)
    {i : Fin m} {j : Fin n} (hij : 0 < A i j) :
    0 < ∑ k : Fin n, A i k * x k := by
  apply (Finset.sum_pos_iff_of_nonneg
    (fun k _ => mul_nonneg (hA i k) (le_of_lt (hx k)))).2
  exact ⟨j, Finset.mem_univ j, mul_pos hij (hx j)⟩

/-- If every column of a nonnegative rectangular matrix has a positive entry,
one smooth general-`p` Algorithm 15.1 update maps positive vectors to positive
vectors.  This statement uses the actual `RectPNormPair.general` update, not a
separately postulated nonlinear map. -/
theorem rect_general_xnext_pos_of_pos_columns {m n : ℕ} (hn : 0 < n)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    (hcol : ∀ j, ∃ i, 0 < A i j)
    (x : Fin n → ℝ) (hx : ∀ j, 0 < x j) :
    ∀ j, 0 < (RectPNormPair.general hn hpq A).xnext x j := by
  let P := RectPNormPair.general hn hpq A
  have hypos_at_col : ∀ j : Fin n,
      ∃ i : Fin m, 0 < P.yof x i ∧ 0 < A i j := by
    intro j
    obtain ⟨i, hij⟩ := hcol j
    refine ⟨i, ?_, hij⟩
    change 0 < ∑ k : Fin n, A i k * x k
    exact rectMatVec_pos_of_row_entry hA hx hij
  have hypos_nonempty : P.yof x ≠ 0 := by
    obtain ⟨i, hi, _⟩ := hypos_at_col ⟨0, hn⟩
    intro hzero
    have hz := congrFun hzero i
    exact (ne_of_gt hi) (by simpa using hz)
  have hdualpos : ∀ i : Fin m, 0 < P.yof x i →
      0 < realLpDual hpq (P.yof x) i := by
    intro i hi
    rw [realLpDual_eq_realLpGradient hpq (P.yof x) hypos_nonempty]
    exact realLpGradient_pos_of_pos_coord hpq.lt (P.yof x)
      hypos_nonempty i hi
  have hynonneg : ∀ i : Fin m, 0 ≤ P.yof x i := by
    intro i
    change 0 ≤ ∑ k : Fin n, A i k * x k
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (hA i k) (le_of_lt (hx k))
  have hdualnonneg : ∀ i : Fin m, 0 ≤ realLpDual hpq (P.yof x) i :=
    realLpDual_nonneg_of_nonneg hpq (P.yof x) hypos_nonempty hynonneg
  have hzpos : ∀ j : Fin n, 0 < P.zof x j := by
    intro j
    obtain ⟨i, hyi, haij⟩ := hypos_at_col j
    change 0 < ∑ r : Fin m, A r j * realLpDual hpq (P.yof x) r
    apply (Finset.sum_pos_iff_of_nonneg (fun r _ =>
      mul_nonneg (hA r j) (hdualnonneg r))).2
    exact ⟨i, Finset.mem_univ i, mul_pos haij (hdualpos i hyi)⟩
  change ∀ j, 0 < realLpDualUnit hn hpq.symm (P.zof x) j
  exact realLpDualUnit_pos_of_pos hn hpq.symm (P.zof x) hzpos

/-- Source-shaped positivity preservation under the printed hypotheses
`A ≥ 0` and irreducible `Aᵀ A` (for nontrivial domain dimension). -/
theorem rect_general_xnext_pos_of_nonneg_gram_irreducible {m n : ℕ}
    [Nontrivial (Fin n)] (hn : 0 < n)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    (hGram : Matrix.IsIrreducible
      (Matrix.of (rectGram A) : Matrix (Fin n) (Fin n) ℝ))
    (x : Fin n → ℝ) (hx : ∀ j, 0 < x j) :
    ∀ j, 0 < (RectPNormPair.general hn hpq A).xnext x j :=
  rect_general_xnext_pos_of_pos_columns hn hpq A hA
    (exists_pos_in_column_of_rectGram_irreducible hA hGram) x hx

/-- Every iterate of the actual rectangular smooth Algorithm 15.1 trace stays
strictly positive under Boyd's printed matrix hypotheses. -/
theorem rect_general_xseq_pos_of_nonneg_gram_irreducible {m n : ℕ}
    [Nontrivial (Fin n)] (hn : 0 < n)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    (hGram : Matrix.IsIrreducible
      (Matrix.of (rectGram A) : Matrix (Fin n) (Fin n) ℝ))
    (x0 : Fin n → ℝ) (hx0 : ∀ j, 0 < x0 j) :
    ∀ k j, 0 < (RectPNormPair.general hn hpq A).xseq x0 k j := by
  intro k
  induction k with
  | zero => simpa [RectPNormPair.xseq] using hx0
  | succ k ih =>
      simpa [RectPNormPair.xseq] using
        rect_general_xnext_pos_of_nonneg_gram_irreducible
          hn hpq A hA hGram
          ((RectPNormPair.general hn hpq A).xseq x0 k) ih

/-- Source-facing raw-start package for Boyd's global hypothesis.  The
printed positive `x₀` is normalized exactly as Algorithm 15.1 prescribes, the
normalized start has unit `p`-norm, and every subsequent actual iterate stays
strictly positive. -/
theorem higham15_boyd_normalized_positive_orbit {m n : ℕ}
    [Nontrivial (Fin n)] (hn : 0 < n)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    (hGram : Matrix.IsIrreducible
      (Matrix.of (rectGram A) : Matrix (Fin n) (Fin n) ℝ))
    (x0 : Fin n → ℝ) (hx0 : ∀ j, 0 < x0 j) :
    realVecLpNorm p (realLpNormalizedStart p x0) = 1 ∧
      ∀ k j,
        0 < (RectPNormPair.general hn hpq A).xseq
          (realLpNormalizedStart p x0) k j := by
  constructor
  · exact realLpNormalizedStart_norm_eq_one hn (le_of_lt hpq.lt) x0 hx0
  · exact rect_general_xseq_pos_of_nonneg_gram_irreducible
      hn hpq A hA hGram (realLpNormalizedStart p x0)
      (realLpNormalizedStart_pos hn (le_of_lt hpq.lt) x0 hx0)

/-! ## Strict Lyapunov structure of the actual smooth update -/

/-- The concrete rectangular objective `x ↦ ‖A x‖_p` is continuous. -/
theorem continuous_rect_general_objective {m n : ℕ} (hn : 0 < n)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) :
    Continuous (fun x : Fin n → ℝ =>
      realVecLpNorm p ((RectPNormPair.general hn hpq A).yof x)) := by
  apply (continuous_realVecLpNorm hpq.pos).comp
  unfold RectPNormPair.yof
  fun_prop

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

/-! ## Compact strict-Lyapunov dynamics

This theorem is the non-target-bearing global-dynamics reduction needed for
Boyd's second statement.  It proves attraction from compactness, continuity,
strict Lyapunov increase, and uniqueness of a fixed point.  In particular,
it does not take convergence, attraction, or a subsequential attraction
statement as a premise. -/

/-- A continuous self-map of a compact invariant set converges to its unique
fixed point when it admits a continuous Lyapunov function whose failure to
increase forces a fixed point. -/
theorem tendsto_iterate_of_compact_strictLyapunov_unique_fixed
    {α : Type*} [MetricSpace α]
    (s : Set α) (hs : IsCompact s)
    {T : α → α} {x0 xbar : α}
    (hx0 : x0 ∈ s) (hmap : MapsTo T s s)
    (hT : ContinuousOn T s) (g : α → ℝ) (hg : Continuous g)
    (hmono : ∀ x ∈ s, g x ≤ g (T x))
    (hfixed_of_back : ∀ x ∈ s, g (T x) ≤ g x → T x = x)
    (hunique : ∀ x ∈ s, T x = x → x = xbar) :
    Tendsto (fun k : ℕ => T^[k] x0) atTop (nhds xbar) := by
  let u : ℕ → α := fun k => T^[k] x0
  have hu_mem : ∀ k, u k ∈ s := by
    intro k
    induction k with
    | zero => exact hx0
    | succ k ih =>
        rw [show u (k + 1) = T (u k) by
          simp [u, iterate_succ_apply']]
        exact hmap ih
  let a : ℕ → ℝ := fun k => g (u k)
  have ha_mono : Monotone a := by
    apply monotone_nat_of_le_succ
    intro k
    change g (u k) ≤ g (u (k + 1))
    rw [show u (k + 1) = T (u k) by
      simp [u, iterate_succ_apply']]
    exact hmono (u k) (hu_mem k)
  have ha_bdd : BddAbove (Set.range a) := by
    apply (hs.bddAbove_image hg.continuousOn).mono
    rintro _ ⟨k, rfl⟩
    exact ⟨u k, hu_mem k, rfl⟩
  let ell : ℝ := ⨆ k : ℕ, a k
  have ha_lim : Tendsto a atTop (nhds ell) := by
    simpa [ell] using tendsto_atTop_ciSup ha_mono ha_bdd
  change Tendsto u atTop (nhds xbar)
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨y, hy, phi, hphi, hsub⟩ :=
    hs.tendsto_subseq (fun k => hu_mem (ns k))
  refine ⟨phi, ?_⟩
  have hindex : Tendsto (fun k => ns (phi k)) atTop atTop :=
    hns.comp hphi.tendsto_atTop
  have ha_sub : Tendsto (fun k => a (ns (phi k))) atTop (nhds ell) :=
    ha_lim.comp hindex
  have hgy_sub : Tendsto (fun k => g (u (ns (phi k)))) atTop (nhds (g y)) := by
    exact hg.continuousAt.tendsto.comp (by simpa [Function.comp_def] using hsub)
  have hgy : g y = ell := tendsto_nhds_unique hgy_sub ha_sub
  have hshift : Tendsto (fun k => ns (phi k) + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hindex
  have ha_shift : Tendsto (fun k => a (ns (phi k) + 1)) atTop (nhds ell) :=
    ha_lim.comp hshift
  have hgTy_sub : Tendsto (fun k => g (T (u (ns (phi k))))) atTop
      (nhds (g (T y))) := by
    have hsub_nhds : Tendsto (fun k => u (ns (phi k))) atTop (nhds y) := by
      simpa [Function.comp_def] using hsub
    have hsub_mem : ∀ᶠ k in atTop, u (ns (phi k)) ∈ s :=
      Eventually.of_forall fun k => hu_mem (ns (phi k))
    have hsub_within : Tendsto (fun k => u (ns (phi k))) atTop
        (nhdsWithin y s) :=
      tendsto_nhdsWithin_iff.mpr ⟨hsub_nhds, hsub_mem⟩
    exact hg.continuousAt.tendsto.comp
      ((hT y hy).tendsto.comp hsub_within)
  have hgT_shift : Tendsto (fun k => g (T (u (ns (phi k))))) atTop
      (nhds ell) := by
    simpa [a, u, iterate_succ_apply'] using ha_shift
  have hgTy : g (T y) = ell := tendsto_nhds_unique hgTy_sub hgT_shift
  have hyfixed : T y = y := hfixed_of_back y hy (by rw [hgTy, hgy])
  have hybar : y = xbar := hunique y hy hyfixed
  simpa [Function.comp_def, hybar] using hsub

/-! ## An honest local-contraction certificate for linear convergence -/

/-- A local contraction-to-a-fixed-point certificate on a closed metric
ball.  This is a sufficient local-dynamics hypothesis, not a reformulation of
the conclusion that the iterates converge. -/
def IsLocalContractionTo {α : Type*} [PseudoMetricSpace α]
    (T : α → α) (xbar : α) (K : NNReal) (δ : ℝ) : Prop :=
  K < 1 ∧ 0 ≤ δ ∧ T xbar = xbar ∧
    ∀ x, dist x xbar ≤ δ → dist (T x) xbar ≤ (K : ℝ) * dist x xbar

/-- Iterates satisfying a local contraction certificate never leave its
closed ball and obey the exact geometric error estimate. -/
theorem iterate_dist_le_geometric_of_isLocalContractionTo
    {α : Type*} [PseudoMetricSpace α]
    {T : α → α} {xbar x0 : α} {K : NNReal} {δ : ℝ}
    (hlocal : IsLocalContractionTo T xbar K δ)
    (hx0 : dist x0 xbar ≤ δ) :
    ∀ k : ℕ,
      dist (T^[k] x0) xbar ≤ (K : ℝ) ^ k * dist x0 xbar ∧
      dist (T^[k] x0) xbar ≤ δ := by
  intro k
  induction k with
  | zero => simpa using And.intro (le_refl (dist x0 xbar)) hx0
  | succ k ih =>
      have hstep := hlocal.2.2.2 (T^[k] x0) ih.2
      have hKle : (K : ℝ) ≤ 1 := le_of_lt (by exact_mod_cast hlocal.1)
      constructor
      · rw [iterate_succ_apply']
        calc
          dist (T (T^[k] x0)) xbar
              ≤ (K : ℝ) * dist (T^[k] x0) xbar := hstep
          _ ≤ (K : ℝ) * ((K : ℝ) ^ k * dist x0 xbar) :=
            mul_le_mul_of_nonneg_left ih.1 K.coe_nonneg
          _ = (K : ℝ) ^ (k + 1) * dist x0 xbar := by ring
      · rw [iterate_succ_apply']
        calc
          dist (T (T^[k] x0)) xbar
              ≤ (K : ℝ) * dist (T^[k] x0) xbar := hstep
          _ ≤ 1 * dist (T^[k] x0) xbar :=
            mul_le_mul_of_nonneg_right hKle dist_nonneg
          _ ≤ δ := by simpa using ih.2

/-- The geometric estimate supplied by a local contraction certificate implies
topological convergence to the certified fixed point. -/
theorem tendsto_iterate_of_isLocalContractionTo
    {α : Type*} [PseudoMetricSpace α]
    {T : α → α} {xbar x0 : α} {K : NNReal} {δ : ℝ}
    (hlocal : IsLocalContractionTo T xbar K δ)
    (hx0 : dist x0 xbar ≤ δ) :
    Tendsto (fun k : ℕ => T^[k] x0) atTop (𝓝 xbar) := by
  apply tendsto_iff_dist_tendsto_zero.2
  apply squeeze_zero (fun _ => dist_nonneg)
  · intro k
    exact (iterate_dist_le_geometric_of_isLocalContractionTo hlocal hx0 k).1
  · simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one K.coe_nonneg
      (by exact_mod_cast hlocal.1)).mul_const (dist x0 xbar))

/-- The recursive trace used for Algorithm 15.1 is exactly functional
iteration of its update map. -/
theorem rectPNormPair_xseq_eq_iterate {m n : ℕ} (P : RectPNormPair m n)
    (x0 : Fin n → ℝ) (k : ℕ) :
    P.xseq x0 k = P.xnext^[k] x0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [RectPNormPair.xseq, ih, iterate_succ_apply']

/-- Audit-grade local-linear bridge for the literal rectangular Algorithm
15.1 trace.  Once a proof from Boyd's exact "strong local maximum" condition
to `IsLocalContractionTo` is supplied, this theorem gives both the advertised
linear rate and `x_k → xbar` without assuming either conclusion. -/
theorem higham15_boyd_local_linear_of_local_contraction
    {m n : ℕ} (P : RectPNormPair m n)
    (x0 xbar : Fin n → ℝ) (K : NNReal) (δ : ℝ)
    (hlocal : IsLocalContractionTo P.xnext xbar K δ)
    (hx0 : dist x0 xbar ≤ δ) :
    (∀ k : ℕ,
      dist (P.xseq x0 k) xbar ≤ (K : ℝ) ^ k * dist x0 xbar) ∧
      Tendsto (P.xseq x0) atTop (𝓝 xbar) := by
  constructor
  · intro k
    rw [rectPNormPair_xseq_eq_iterate P x0 k]
    exact (iterate_dist_le_geometric_of_isLocalContractionTo hlocal hx0 k).1
  · have h := tendsto_iterate_of_isLocalContractionTo hlocal hx0
    rw [show P.xseq x0 = (fun k : ℕ => P.xnext^[k] x0) by
      funext k
      exact rectPNormPair_xseq_eq_iterate P x0 k]
    exact h

/-! ## A derivative-level local convergence bridge

The preceding theorem deliberately takes a metric contraction certificate.
The next result proves that certificate from the standard first-order local
dynamics condition: the derivative of the actual update at its fixed point
has operator norm strictly below one.  Thus the remaining Boyd-local gap is
not "prove convergence from convergence"; it is the source-specific
second-order calculation that turns Boyd's strict nondegenerate maximum into
this derivative bound. -/

/-- A Frechet derivative with operator norm below one gives a genuine local
radial contraction about a fixed point.  The radius is constructed from the
little-o remainder in the definition of the derivative. -/
theorem exists_isLocalContractionTo_of_hasFDerivAt_norm_lt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : E → E} {xbar : E} {L : E →L[ℝ] E} {K : NNReal}
    (hfixed : T xbar = xbar)
    (hderiv : HasFDerivAt T L xbar)
    (hLK : ‖L‖ < (K : ℝ)) (hK : K < 1) :
    ∃ δ : ℝ, 0 < δ ∧ IsLocalContractionTo T xbar K δ := by
  let ε : ℝ := (K : ℝ) - ‖L‖
  have hε : 0 < ε := sub_pos.mpr hLK
  have hrem : ∀ᶠ x in nhds xbar,
      ‖T x - T xbar - L (x - xbar)‖ ≤ ε * ‖x - xbar‖ :=
    hderiv.isLittleO.def hε
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.1 hrem
  refine ⟨r / 2, half_pos hr, hK, (half_pos hr).le, hfixed, ?_⟩
  intro x hx
  have hxball : x ∈ Metric.ball xbar r := by
    rw [Metric.mem_ball]
    exact hx.trans_lt (half_lt_self hr)
  have hremainder := hrsub hxball
  rw [hfixed] at hremainder
  rw [dist_eq_norm, dist_eq_norm]
  calc
    ‖T x - xbar‖
        = ‖(T x - xbar - L (x - xbar)) + L (x - xbar)‖ := by
            congr 1
            abel
    _ ≤ ‖T x - xbar - L (x - xbar)‖ + ‖L (x - xbar)‖ :=
      norm_add_le _ _
    _ ≤ ε * ‖x - xbar‖ + ‖L‖ * ‖x - xbar‖ :=
      add_le_add hremainder (L.le_opNorm (x - xbar))
    _ = (K : ℝ) * ‖x - xbar‖ := by
      dsimp [ε]
      ring

/-- Derivative-level local-linear convergence for the literal rectangular
Algorithm 15.1 trace.  Unlike `higham15_boyd_local_linear_of_local_contraction`,
this theorem constructs the contraction radius from differentiability and a
strict derivative-norm bound. -/
theorem higham15_boyd_local_linear_of_fderiv_norm_lt
    {m n : ℕ} (P : RectPNormPair m n)
    (x0 xbar : Fin n → ℝ) (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (K : NNReal)
    (hfixed : P.xnext xbar = xbar)
    (hderiv : HasFDerivAt P.xnext L xbar)
    (hLK : ‖L‖ < (K : ℝ)) (hK : K < 1) :
    ∃ δ : ℝ, 0 < δ ∧
      (dist x0 xbar ≤ δ →
        (∀ k : ℕ,
          dist (P.xseq x0 k) xbar ≤
            (K : ℝ) ^ k * dist x0 xbar) ∧
        Tendsto (P.xseq x0) atTop (nhds xbar)) := by
  obtain ⟨δ, hδ, hlocal⟩ :=
    exists_isLocalContractionTo_of_hasFDerivAt_norm_lt
      hfixed hderiv hLK hK
  refine ⟨δ, hδ, ?_⟩
  intro hx0
  exact higham15_boyd_local_linear_of_local_contraction
    P x0 xbar K δ hlocal hx0

/-! ## The source-derived compact nonnegative carrier -/

/-- The nonnegative `p`-unit sphere used as the compact state space for
Boyd's global iteration. -/
noncomputable def boydNonnegativeUnitCarrier {n : ℕ} (p : ℝ) :
    Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ realVecLpNorm p x = 1}

theorem isClosed_boydNonnegativeUnitCarrier {n : ℕ} {p : ℝ}
    (hp : 0 < p) : IsClosed (boydNonnegativeUnitCarrier (n := n) p) := by
  have hnonneg : IsClosed {x : Fin n → ℝ | ∀ i, 0 ≤ x i} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun i =>
      isClosed_le continuous_const (continuous_apply i)
  have hunit : IsClosed {x : Fin n → ℝ | realVecLpNorm p x = 1} :=
    isClosed_eq (continuous_realVecLpNorm hp) continuous_const
  simpa [boydNonnegativeUnitCarrier, Set.setOf_and] using hnonneg.inter hunit

theorem isCompact_boydNonnegativeUnitCarrier {n : ℕ} {p q : ℝ}
    (hpq : p.HolderConjugate q) :
    IsCompact (boydNonnegativeUnitCarrier (n := n) p) := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  constructor
  · exact isClosed_boydNonnegativeUnitCarrier hpq.pos
  · rw [isBounded_iff_forall_norm_le]
    refine ⟨1, ?_⟩
    intro x hx
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have hholder := realVecLpNorm_holder hpq (basisVec i) x
    have hbasis : realVecLpNorm q (basisVec i) = 1 :=
      realVecLpNorm_basisVec (le_of_lt hpq.symm.lt) i
    have hcoord : (∑ j : Fin n, basisVec i j * x j) = x i := by
      simp [basisVec]
    simpa [hcoord, hbasis, hx.2, Real.norm_eq_abs] using hholder

theorem boydCarrier_ne_zero {n : ℕ} {p : ℝ} (hp : 1 ≤ p)
    {x : Fin n → ℝ} (hx : x ∈ boydNonnegativeUnitCarrier p) : x ≠ 0 := by
  intro hzero
  have hunit := hx.2
  rw [hzero, realVecLpNorm_zero hp] at hunit
  norm_num at hunit

theorem exists_pos_coord_of_mem_boydCarrier {n : ℕ} {p : ℝ}
    (hp : 1 ≤ p) {x : Fin n → ℝ}
    (hx : x ∈ boydNonnegativeUnitCarrier p) : ∃ j, 0 < x j := by
  have hxne := boydCarrier_ne_zero hp hx
  by_contra h
  push_neg at h
  apply hxne
  funext j
  exact le_antisymm (h j) (hx.1 j)

theorem rect_general_yof_ne_zero_of_mem_boydCarrier {m n : ℕ}
    [Nontrivial (Fin n)] (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q) (A : Fin m → Fin n → ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    (hGram : Matrix.IsIrreducible
      (Matrix.of (rectGram A) : Matrix (Fin n) (Fin n) ℝ))
    {x : Fin n → ℝ} (hx : x ∈ boydNonnegativeUnitCarrier p) :
    (RectPNormPair.general hn hpq A).yof x ≠ 0 := by
  obtain ⟨j, hxj⟩ := exists_pos_coord_of_mem_boydCarrier
    (le_of_lt hpq.lt) hx
  obtain ⟨i, haij⟩ :=
    exists_pos_in_column_of_rectGram_irreducible hA hGram j
  have hyi : 0 < (RectPNormPair.general hn hpq A).yof x i := by
    change 0 < ∑ k : Fin n, A i k * x k
    apply (Finset.sum_pos_iff_of_nonneg (fun k _ =>
      mul_nonneg (hA i k) (hx.1 k))).2
    exact ⟨j, Finset.mem_univ j, mul_pos haij hxj⟩
  intro hyzero
  have hi := congrFun hyzero i
  exact (ne_of_gt hyi) (by simpa using hi)

theorem rect_general_zof_nonneg_of_mem_boydCarrier {m n : ℕ}
    [Nontrivial (Fin n)] (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q) (A : Fin m → Fin n → ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    (hGram : Matrix.IsIrreducible
      (Matrix.of (rectGram A) : Matrix (Fin n) (Fin n) ℝ))
    {x : Fin n → ℝ} (hx : x ∈ boydNonnegativeUnitCarrier p) :
    ∀ j, 0 ≤ (RectPNormPair.general hn hpq A).zof x j := by
  have hyne := rect_general_yof_ne_zero_of_mem_boydCarrier
    hn hpq A hA hGram hx
  have hynonneg : ∀ i, 0 ≤ (RectPNormPair.general hn hpq A).yof x i := by
    intro i
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hA i j) (hx.1 j)
  have hdual := realLpDual_nonneg_of_nonneg hpq _ hyne hynonneg
  intro j
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hA i j) (hdual i)

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

/-! ### Continuity of the actual smooth update, including zero coordinates -/

/-- A signed positive real power written without a discontinuous sign
function. -/
noncomputable def realLpSignedPower (r : ℝ) (t : ℝ) : ℝ :=
  (max t 0) ^ r - (max (-t) 0) ^ r

theorem continuous_realLpSignedPower {r : ℝ} (hr : 0 ≤ r) :
    Continuous (realLpSignedPower r) := by
  apply Continuous.sub
  · exact (continuous_id.max continuous_const).rpow_const
      (fun _ => Or.inr hr)
  · exact (continuous_id.neg.max continuous_const).rpow_const
      (fun _ => Or.inr hr)

theorem realLpGradient_coord_eq_signedPower {p t : ℝ} (hp : 1 < p) :
    |t| ^ (p - 2) * t = realLpSignedPower (p - 1) t := by
  by_cases ht0 : t = 0
  · subst t
    simp [realLpSignedPower, Real.zero_rpow (sub_pos.mpr hp).ne']
  rcases lt_or_gt_of_ne ht0 with ht | ht
  · have hnegpos : 0 < -t := neg_pos.mpr ht
    have habs : |t| = -t := abs_of_neg ht
    have hpow : (-t) ^ (p - 2) * (-t) = (-t) ^ (p - 1) := by
      calc
        (-t) ^ (p - 2) * (-t) =
            (-t) ^ (p - 2) * (-t) ^ (1 : ℝ) := by
              rw [Real.rpow_one]
        _ = (-t) ^ ((p - 2) + 1) :=
          (Real.rpow_add hnegpos (p - 2) 1).symm
        _ = (-t) ^ (p - 1) := by congr 1; ring
    rw [habs]
    simp [realLpSignedPower, le_of_lt ht, le_of_lt hnegpos,
      Real.zero_rpow (sub_pos.mpr hp).ne']
    nlinarith
  · have habs : |t| = t := abs_of_pos ht
    have hpow : t ^ (p - 2) * t = t ^ (p - 1) := by
      calc
        t ^ (p - 2) * t = t ^ (p - 2) * t ^ (1 : ℝ) := by
          rw [Real.rpow_one]
        _ = t ^ ((p - 2) + 1) :=
          (Real.rpow_add ht (p - 2) 1).symm
        _ = t ^ (p - 1) := by congr 1; ring
    rw [habs, hpow]
    simp [realLpSignedPower, le_of_lt ht, le_of_lt (neg_neg_of_pos ht),
      Real.zero_rpow (sub_pos.mpr hp).ne']

theorem continuous_realLpGradient_coordFactor {p : ℝ} (hp : 1 < p) :
    Continuous (fun t : ℝ => |t| ^ (p - 2) * t) := by
  rw [show (fun t : ℝ => |t| ^ (p - 2) * t) =
      realLpSignedPower (p - 1) by
    funext t
    exact realLpGradient_coord_eq_signedPower hp]
  exact continuous_realLpSignedPower (sub_nonneg.mpr (le_of_lt hp))

theorem continuous_realLpPowerSum {n : ℕ} {p : ℝ} (hp : 0 < p) :
    Continuous (realLpPowerSum (n := n) p) := by
  unfold realLpPowerSum
  apply continuous_finset_sum
  intro i _hi
  exact (continuous_apply i).abs.rpow_const (fun _ => Or.inr hp.le)

theorem continuousAt_realLpGradient {n : ℕ} {p : ℝ} (hp : 1 < p)
    {x : Fin n → ℝ} (hx : x ≠ 0) :
    ContinuousAt (realLpGradient p) x := by
  apply continuousAt_pi'
  intro i
  unfold realLpGradient
  have hsumpos : 0 < realLpPowerSum p x := realLpPowerSum_pos hp hx
  have hscale : ContinuousAt
      (fun y : Fin n → ℝ => (realLpPowerSum p y) ^ (p⁻¹ - 1)) x :=
    (continuous_realLpPowerSum (zero_lt_one.trans hp)).continuousAt.rpow_const
      (Or.inl (ne_of_gt hsumpos))
  have hcoord : ContinuousAt
      (fun y : Fin n → ℝ => |y i| ^ (p - 2) * y i) x :=
    (continuous_realLpGradient_coordFactor hp).continuousAt.comp
      (continuousAt_apply i x)
  exact hscale.mul hcoord

theorem continuousAt_realLpDual {n : ℕ} {p q : ℝ}
    (hpq : p.HolderConjugate q) {x : Fin n → ℝ} (hx : x ≠ 0) :
    ContinuousAt (realLpDual hpq) x := by
  have heq : Filter.EventuallyEq (nhds x) (realLpDual hpq) (realLpGradient p) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact realLpDual_eq_realLpGradient hpq y hy
  exact (continuousAt_congr heq).2 (continuousAt_realLpGradient hpq.lt hx)

theorem continuousAt_realLpDualUnit {n : ℕ} (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q) {x : Fin n → ℝ} (hx : x ≠ 0) :
    ContinuousAt (realLpDualUnit hn hpq) x := by
  have heq : Filter.EventuallyEq (nhds x)
      (realLpDualUnit hn hpq) (realLpDual hpq) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    simp [realLpDualUnit, hy]
  exact (continuousAt_congr heq).2 (continuousAt_realLpDual hpq hx)

theorem continuous_rect_general_yof {m n : ℕ} (hn : 0 < n)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) :
    Continuous (RectPNormPair.general hn hpq A).yof := by
  unfold RectPNormPair.yof
  fun_prop

theorem continuousAt_rect_general_zof {m n : ℕ} (hn : 0 < n)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) {x : Fin n → ℝ}
    (hyne : (RectPNormPair.general hn hpq A).yof x ≠ 0) :
    ContinuousAt (RectPNormPair.general hn hpq A).zof x := by
  let P := RectPNormPair.general hn hpq A
  have hycont : ContinuousAt P.yof x := by
    exact (continuous_rect_general_yof hn hpq A).continuousAt
  have hdualcomp : ContinuousAt (fun v => realLpDual hpq (P.yof v)) x :=
    (continuousAt_realLpDual hpq hyne).comp hycont
  apply continuousAt_pi'
  intro j
  change ContinuousAt
    (fun v => ∑ i : Fin m, A i j * realLpDual hpq (P.yof v) i) x
  have hsum : ∀ s : Finset (Fin m), ContinuousAt
      (fun v => ∑ i ∈ s, A i j * realLpDual hpq (P.yof v) i) x := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simpa using
          (continuousAt_const : ContinuousAt
            (fun _ : Fin n → ℝ => (0 : ℝ)) x)
    | @insert i s hi ih =>
        simp only [Finset.sum_insert, hi, not_false_eq_true]
        have hcoord : ContinuousAt
            (fun v => realLpDual hpq (P.yof v) i) x :=
          (continuous_apply i).continuousAt.comp hdualcomp
        exact (continuousAt_const.mul hcoord).add ih
  simpa using hsum Finset.univ

theorem continuousAt_rect_general_xnext {m n : ℕ} (hn : 0 < n)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) {x : Fin n → ℝ}
    (hyne : (RectPNormPair.general hn hpq A).yof x ≠ 0)
    (hzne : (RectPNormPair.general hn hpq A).zof x ≠ 0) :
    ContinuousAt (RectPNormPair.general hn hpq A).xnext x := by
  let P := RectPNormPair.general hn hpq A
  have hzcont : ContinuousAt P.zof x :=
    continuousAt_rect_general_zof hn hpq A hyne
  change ContinuousAt (fun v => realLpDualUnit hn hpq.symm (P.zof v)) x
  exact (continuousAt_realLpDualUnit hn hpq.symm hzne).comp hzcont

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

/-! ### Existence and interiority of an actual maximizing fixed point -/

theorem boydNonnegativeUnitCarrier_nonempty {n : ℕ} (hn : 0 < n)
    {p : ℝ} (hp : 1 ≤ p) :
    (boydNonnegativeUnitCarrier (n := n) p).Nonempty := by
  let i0 : Fin n := ⟨0, hn⟩
  refine ⟨basisVec i0, ?_, realVecLpNorm_basisVec hp i0⟩
  intro i
  by_cases hi : i = i0
  · simp [basisVec, hi]
  · simp [basisVec, hi]

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

theorem rectGram_mulVec_eq_transpose_yof {m n : ℕ}
    (hn : 0 < n) {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) (j : Fin n) :
    Matrix.mulVec
        (Matrix.of (rectGram A) : Matrix (Fin n) (Fin n) ℝ) x j =
      ∑ i : Fin m, A i j * (RectPNormPair.general hn hpq A).yof x i := by
  change (∑ k : Fin n, (∑ i : Fin m, A i j * A i k) * x k) =
    ∑ i : Fin m, A i j * (∑ k : Fin n, A i k * x k)
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  ring

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

/-! ### Identification of the carrier maximum with the induced norm -/

theorem complex_rect_action_le_abs_real_action {m n : ℕ}
    {p : ℝ} (hp : 1 ≤ p) (A : Fin m → Fin n → ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (z : CVec n) :
    complexVecLpNorm (ENNReal.ofReal p)
        (complexMatrixVecMul (realRectToCMatrix A) z) ≤
      realVecLpNorm p (fun i : Fin m => ∑ j : Fin n, A i j * ‖z j‖) := by
  have hcoord : componentwiseAbsLe
      (complexMatrixVecMul (realRectToCMatrix A) z)
      (realVecToComplex (fun i : Fin m => ∑ j : Fin n, A i j * ‖z j‖)) := by
    intro i
    change ‖∑ j : Fin n, (A i j : ℂ) * z j‖ ≤
      ‖((∑ j : Fin n, A i j * ‖z j‖ : ℝ) : ℂ)‖
    have hsum_nonneg : 0 ≤ ∑ j : Fin n, A i j * ‖z j‖ :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hA i j) (norm_nonneg _)
    calc
      ‖∑ j : Fin n, (A i j : ℂ) * z j‖ ≤
          ∑ j : Fin n, ‖(A i j : ℂ) * z j‖ := norm_sum_le _ _
      _ = ∑ j : Fin n, A i j * ‖z j‖ := by
        apply Finset.sum_congr rfl
        intro j _hj
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hA i j)]
      _ = ‖((∑ j : Fin n, A i j * ‖z j‖ : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsum_nonneg]
  exact (complexVecLpNorm_ofReal_monotone (n := m) (p := p) hp
    (complexMatrixVecMul (realRectToCMatrix A) z)
    (realVecToComplex (fun i : Fin m => ∑ j : Fin n, A i j * ‖z j‖)) hcoord).trans_eq rfl

/-- A nonnegative-carrier maximizer realizes the repository's complex induced
matrix `p`-norm.  The complex-to-real direction uses `|Az| ≤ A|z|`; the
reverse direction embeds the real maximizing vector. -/
theorem boydCarrier_maximum_eq_opP {m n : ℕ}
    (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q) (A : Fin m → Fin n → ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    {xbar : Fin n → ℝ}
    (hxbar : xbar ∈ boydNonnegativeUnitCarrier p)
    (hmax : ∀ x ∈ boydNonnegativeUnitCarrier p,
      realVecLpNorm p ((RectPNormPair.general hn hpq A).yof x) ≤
        realVecLpNorm p ((RectPNormPair.general hn hpq A).yof xbar)) :
    realVecLpNorm p ((RectPNormPair.general hn hpq A).yof xbar) =
      (RectPNormPair.general hn hpq A).opP := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact le_of_lt hpq.lt⟩
  let P := RectPNormPair.general hn hpq A
  let c := realVecLpNorm p (P.yof xbar)
  have hc_le : c ≤ P.opP := by
    have h := P.op_bound xbar
    change realVecLpNorm p (P.yof xbar) ≤
      P.opP * realVecLpNorm p xbar at h
    rw [hxbar.2, mul_one] at h
    exact h
  have hbound : MixedSubordinateMatrixBound
      (complexVecLpNorm (n := n) (ENNReal.ofReal p))
      (complexVecLpNorm (n := m) (ENNReal.ofReal p))
      (realRectToCMatrix A) c := by
    intro z
    by_cases hz : z = 0
    · subst z
      have hsrc : complexVecLpNorm (n := n) (ENNReal.ofReal p)
          (0 : CVec n) = 0 :=
        (complexVecLpNorm_isComplexVectorNorm
          (n := n) (ENNReal.ofReal p)).eq_zero_iff _ |>.2 rfl
      have houtvec : complexMatrixVecMul (realRectToCMatrix A)
          (0 : CVec n) = (0 : CVec m) := by
        funext i
        simp [complexMatrixVecMul]
      have hout : complexVecLpNorm (n := m) (ENNReal.ofReal p)
          (complexMatrixVecMul (realRectToCMatrix A) (0 : CVec n)) = 0 :=
        (complexVecLpNorm_isComplexVectorNorm
          (n := m) (ENNReal.ofReal p)).eq_zero_iff _ |>.2 houtvec
      rw [hout, hsrc, mul_zero]
    · let a : Fin n → ℝ := fun j => ‖z j‖
      let r : ℝ := complexVecLpNorm (ENNReal.ofReal p) z
      have hrpos : 0 < r := by
        have hnorm := complexVecLpNorm_isComplexVectorNorm
          (n := n) (ENNReal.ofReal p)
        exact lt_of_le_of_ne (hnorm.nonneg z)
          (Ne.symm ((hnorm.eq_zero_iff z).not.mpr hz))
      have har : realVecLpNorm p a = r := by
        simpa [a, r, realVecLpNorm, complexAbsVec] using
          (complexVecLpNorm_ofReal_abs_eq hpq.pos z)
      let u : Fin n → ℝ := fun j => r⁻¹ * a j
      have hu : u ∈ boydNonnegativeUnitCarrier p := by
        constructor
        · intro j
          exact mul_nonneg (inv_nonneg.mpr hrpos.le) (norm_nonneg _)
        · rw [show u = fun j => r⁻¹ * a j from rfl,
            realVecLpNorm_smul_real (le_of_lt hpq.lt), har,
            abs_of_pos (inv_pos.mpr hrpos), inv_mul_cancel₀ (ne_of_gt hrpos)]
      have hy_scale : P.yof u = fun i => r⁻¹ * P.yof a i := by
        funext i
        unfold RectPNormPair.yof
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        dsimp [u]
        ring
      have hscaled := hmax u hu
      have hya_le : realVecLpNorm p (P.yof a) ≤ r * c := by
        rw [hy_scale, realVecLpNorm_smul_real (le_of_lt hpq.lt),
          abs_of_pos (inv_pos.mpr hrpos)] at hscaled
        have hscaled' : r⁻¹ * realVecLpNorm p (P.yof a) ≤ c := by
          simpa [c] using hscaled
        have hmul := mul_le_mul_of_nonneg_left hscaled' hrpos.le
        calc
          realVecLpNorm p (P.yof a) =
              r * (r⁻¹ * realVecLpNorm p (P.yof a)) := by
                field_simp
          _ ≤ r * c := hmul
      calc
        complexVecLpNorm (ENNReal.ofReal p)
            (complexMatrixVecMul (realRectToCMatrix A) z) ≤
            realVecLpNorm p (P.yof a) := by
          simpa [P, RectPNormPair.yof, a] using
            complex_rect_action_le_abs_real_action
              (le_of_lt hpq.lt) A hA z
        _ ≤ c * complexVecLpNorm (ENNReal.ofReal p) z := by
          simpa [r, mul_comm] using hya_le
  have hop_le : P.opP ≤ c := by
    have hvalue := complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
      hn p (le_of_lt hpq.lt) (realRectToCMatrix A)
    exact hvalue.2 c hbound
  exact le_antisymm hc_le hop_le

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

/-! ## Source-facing global Boyd reduction -/

/-- Generic global convergence theorem for the literal smooth rectangular
Algorithm 15.1.  Strict Lyapunov increase is derived internally from Lemma
15.2 and the actual stopping rule.  The source-derived theorems above now
supply compactness, invariance, continuity, existence, positivity, and exact
induced-norm optimality under Boyd's printed hypotheses; uniqueness of the
positive normalized fixed point remains the separate nonlinear
Perron--Frobenius gate. -/
theorem higham15_boyd_global_of_compact_unique_optimal_fixed
    {m n : ℕ} (hn : 0 < n)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ)
    (s : Set (Fin n → ℝ)) (hs : IsCompact s)
    (x0 xbar : Fin n → ℝ)
    (hx0 : x0 ∈ s)
    (hmap : MapsTo (RectPNormPair.general hn hpq A).xnext s s)
    (hunit : ∀ x ∈ s, realVecLpNorm p x = 1)
    (hz : ∀ x ∈ s, (RectPNormPair.general hn hpq A).zof x ≠ 0)
    (hcontinuous : ContinuousOn
      (RectPNormPair.general hn hpq A).xnext s)
    (hunique : ∀ x ∈ s,
      (RectPNormPair.general hn hpq A).xnext x = x → x = xbar)
    (hoptimal : realVecLpNorm p
      ((RectPNormPair.general hn hpq A).yof xbar) =
        (RectPNormPair.general hn hpq A).opP) :
    Tendsto ((RectPNormPair.general hn hpq A).xseq x0) atTop
        (nhds xbar) ∧
      Tendsto ((RectPNormPair.general hn hpq A).gammaSeq x0) atTop
        (nhds (RectPNormPair.general hn hpq A).opP) := by
  let P := RectPNormPair.general hn hpq A
  let g : (Fin n → ℝ) → ℝ := fun x => realVecLpNorm p (P.yof x)
  have hg : Continuous g := by
    simpa [P, g] using continuous_rect_general_objective hn hpq A
  have hmono : ∀ x ∈ s, g x ≤ g (P.xnext x) := by
    intro x hx
    have hchain := P.higham15_lemma15_2b_rectangular x (hunit x hx)
    exact hchain.1.trans hchain.2.1
  have hfixed_of_back : ∀ x ∈ s,
      g (P.xnext x) ≤ g x → P.xnext x = x := by
    intro x hx hback
    exact rect_general_xnext_eq_of_objective_not_increased
      hn hpq A x (hunit x hx) (hz x hx) hback
  have hiter : Tendsto (fun k : ℕ => P.xnext^[k] x0) atTop
      (nhds xbar) :=
    tendsto_iterate_of_compact_strictLyapunov_unique_fixed
      s hs hx0 hmap hcontinuous g hg hmono hfixed_of_back hunique
  have hxlim : Tendsto (P.xseq x0) atTop (nhds xbar) := by
    rw [show P.xseq x0 = (fun k : ℕ => P.xnext^[k] x0) by
      funext k
      exact rectPNormPair_xseq_eq_iterate P x0 k]
    exact hiter
  refine ⟨hxlim, ?_⟩
  have hglim : Tendsto (fun k => g (P.xseq x0 k)) atTop
      (nhds (g xbar)) := hg.continuousAt.tendsto.comp hxlim
  simpa [RectPNormPair.gammaSeq, g, P, hoptimal] using hglim

end Ch15
end NumStability
