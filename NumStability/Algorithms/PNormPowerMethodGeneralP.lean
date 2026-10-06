-- Algorithms/PNormPowerMethodGeneralP.lean
--
-- Concrete finite-dimensional real l^p closure for Higham, Chapter 15,
-- equations (15.2) and (15.3), in the smooth range 1 < p < infinity.

import Mathlib.Analysis.InnerProductSpace.NormPow
import NumStability.Analysis.Norms
import NumStability.Algorithms.PNormPowerMethod

namespace NumStability
namespace Ch15

open scoped BigOperators

/-- The concrete finite-dimensional real `l^p` norm, obtained by restricting
the repository's finite-product complex `L^p` norm to real vectors. -/
noncomputable def realVecLpNorm {n : ℕ} (p : ℝ) (x : Fin n → ℝ) : ℝ :=
  complexVecLpNorm (ENNReal.ofReal p) (fun i => (x i : ℂ))

lemma realVecLpNorm_eq_sum_rpow {n : ℕ} {p : ℝ} (hp : 0 < p)
    (x : Fin n → ℝ) :
    realVecLpNorm p x = (∑ i : Fin n, |x i| ^ p) ^ p⁻¹ := by
  simpa [realVecLpNorm] using
    (complexVecLpNorm_ofReal_eq_sum_rpow (n := n) hp
      (fun i : Fin n => (x i : ℂ)))

lemma realVecLpNorm_zero {n : ℕ} {p : ℝ} (hp : 1 ≤ p) :
    realVecLpNorm (n := n) p 0 = 0 := by
  haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact hp⟩
  simpa [realVecLpNorm] using
    (complexVecLpNorm_isComplexVectorNorm
      (n := n) (ENNReal.ofReal p)).eq_zero_iff
      (0 : Fin n → ℂ) |>.2 rfl

lemma realVecLpNorm_pos {n : ℕ} {p : ℝ} (hp : 1 ≤ p)
    {x : Fin n → ℝ} (hx : x ≠ 0) :
    0 < realVecLpNorm p x := by
  haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact hp⟩
  have hnonneg :=
    (complexVecLpNorm_isComplexVectorNorm
      (n := n) (ENNReal.ofReal p)).nonneg
      (fun i : Fin n => (x i : ℂ))
  have hne : realVecLpNorm p x ≠ 0 := by
    intro hzero
    have hc : (fun i : Fin n => (x i : ℂ)) = 0 :=
      ((complexVecLpNorm_isComplexVectorNorm
        (n := n) (ENNReal.ofReal p)).eq_zero_iff _).1 hzero
    apply hx
    funext i
    have hi := congrFun hc i
    simpa using congrArg Complex.re hi
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- Real finite-dimensional Holder inequality for the concrete norms. -/
lemma realVecLpNorm_holder {n : ℕ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (a x : Fin n → ℝ) :
    |∑ i : Fin n, a i * x i| ≤ realVecLpNorm q a * realVecLpNorm p x := by
  have h := complexVecLpNorm_holder hpq
    (fun i : Fin n => (a i : ℂ)) (fun i : Fin n => (x i : ℂ))
  have hsum : (∑ i : Fin n, (a i : ℂ) * (x i : ℂ)) =
      ((∑ i : Fin n, a i * x i : ℝ) : ℂ) := by
    norm_num
  calc
    |∑ i : Fin n, a i * x i| =
        ‖((∑ i : Fin n, a i * x i : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖∑ i : Fin n, (a i : ℂ) * (x i : ℂ)‖ := by rw [hsum]
    _ ≤ realVecLpNorm q a * realVecLpNorm p x := by
      simpa [realVecLpNorm] using h

/-- A real `q`-unit-ball functional attaining the real `p`-norm.  This is the
concrete finite-dimensional duality bridge needed by Algorithm 15.1. -/
def IsRealLpNormer {n : ℕ} (p q : ℝ)
    (x d : Fin n → ℝ) : Prop :=
  realVecLpNorm q d ≤ 1 ∧
    (∑ i : Fin n, d i * x i) = realVecLpNorm p x

lemma exists_realLpNormer {n : ℕ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (x : Fin n → ℝ) :
    ∃ d : Fin n → ℝ, IsRealLpNormer p q x d := by
  classical
  obtain ⟨g, hg_unit, hvalue⟩ :=
    exists_nnreal_lp_normer hpq.symm (fun i : Fin n => (x i : ℂ))
  let d : Fin n → ℝ := fun i => signVec x i * (g i : ℝ)
  refine ⟨d, ?_, ?_⟩
  · rw [realVecLpNorm_eq_sum_rpow hpq.symm.pos]
    have hg_real : (∑ i : Fin n, (g i : ℝ) ^ q) ≤ 1 := by
      have hg_cast : ((∑ i : Fin n, g i ^ q : NNReal) : ℝ) ≤ 1 := by
        exact_mod_cast hg_unit
      simpa [NNReal.coe_rpow] using hg_cast
    have hsum : (∑ i : Fin n, |d i| ^ q) =
        ∑ i : Fin n, (g i : ℝ) ^ q := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [show |d i| = (g i : ℝ) by
        simp [d, abs_mul, abs_signVec, NNReal.coe_nonneg]]
    rw [hsum]
    exact Real.rpow_le_one
      (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (NNReal.coe_nonneg _) q))
      hg_real (inv_nonneg.mpr (le_of_lt hpq.symm.pos))
  · rw [realVecLpNorm_eq_sum_rpow hpq.pos]
    have hvalue_real :
        (∑ i : Fin n, |x i| * (g i : ℝ)) =
          (∑ i : Fin n, |x i| ^ p) ^ (1 / p) := by
      have hcast := congrArg (fun t : NNReal => (t : ℝ)) hvalue
      simpa [NNReal.coe_rpow, Complex.norm_real] using hcast
    calc
      (∑ i : Fin n, d i * x i) =
          ∑ i : Fin n, |x i| * (g i : ℝ) := by
            apply Finset.sum_congr rfl
            intro i _hi
            calc
              d i * x i = (x i * signVec x i) * (g i : ℝ) := by
                simp [d]; ring
              _ = |x i| * (g i : ℝ) := by
                rw [mul_signVec_eq_abs]
      _ = (∑ i : Fin n, |x i| ^ p) ^ (1 / p) := hvalue_real
      _ = (∑ i : Fin n, |x i| ^ p) ^ p⁻¹ := by rw [one_div]

/-- A canonical concrete normalized dual vector for finite-dimensional real
`l^p`, chosen from the proved Holder-attainment theorem. -/
noncomputable def realLpDual {n : ℕ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (x : Fin n → ℝ) : Fin n → ℝ :=
  Classical.choose (exists_realLpNormer hpq x)

lemma realLpDual_spec {n : ℕ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (x : Fin n → ℝ) :
    IsRealLpNormer p q x (realLpDual hpq x) :=
  Classical.choose_spec (exists_realLpNormer hpq x)

lemma realLpDual_norm_eq_one {n : ℕ} {p q : ℝ}
    (hpq : p.HolderConjugate q) {x : Fin n → ℝ} (hx : x ≠ 0) :
    realVecLpNorm q (realLpDual hpq x) = 1 := by
  have hspec := realLpDual_spec hpq x
  have hxpos : 0 < realVecLpNorm p x :=
    realVecLpNorm_pos (le_of_lt hpq.lt) hx
  have hholder := realVecLpNorm_holder hpq
    (realLpDual hpq x) x
  rw [hspec.2, abs_of_pos hxpos] at hholder
  have hge : 1 ≤ realVecLpNorm q (realLpDual hpq x) := by
    nlinarith
  exact le_antisymm hspec.1 hge

/-- The finite power sum underlying the concrete `l^p` norm. -/
noncomputable def realLpPowerSum {n : ℕ} (p : ℝ)
    (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, |x i| ^ p

/-- The explicit gradient of the finite-dimensional real `l^p` norm away
from zero.  The formula remains total at zero by Lean's `rpow` convention,
but it is only used as a gradient when `x ≠ 0`. -/
noncomputable def realLpGradient {n : ℕ} (p : ℝ)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (realLpPowerSum p x) ^ (p⁻¹ - 1) *
    (|x i| ^ (p - 2) * x i)

lemma realLpPowerSum_pos {n : ℕ} {p : ℝ} (hp : 1 < p)
    {x : Fin n → ℝ} (hx : x ≠ 0) :
    0 < realLpPowerSum p x := by
  have hnormpos : 0 < realVecLpNorm p x :=
    realVecLpNorm_pos (le_of_lt hp) hx
  have hsum_nonneg : 0 ≤ realLpPowerSum p x := by
    exact Finset.sum_nonneg
      (fun i _ => Real.rpow_nonneg (abs_nonneg (x i)) p)
  have hsum_ne : realLpPowerSum p x ≠ 0 := by
    intro hzero
    rw [realVecLpNorm_eq_sum_rpow (zero_lt_one.trans hp),
      show (∑ i : Fin n, |x i| ^ p) = realLpPowerSum p x by rfl,
      hzero, Real.zero_rpow (inv_ne_zero (ne_of_gt (zero_lt_one.trans hp)))] at hnormpos
    exact (lt_irrefl 0 hnormpos)
  exact lt_of_le_of_ne hsum_nonneg (Ne.symm hsum_ne)

/-- Direct calculus proof that the concrete finite-dimensional real `l^p`
norm is differentiable away from zero, with its standard gradient. -/
theorem realVecLpNorm_hasDirectionalGradientAt {n : ℕ} {p : ℝ}
    (hp : 1 < p) (x : Fin n → ℝ) (hx : x ≠ 0) :
    HasDirectionalGradientAt (realVecLpNorm p) (realLpGradient p x) x := by
  intro h
  let S : ℝ := realLpPowerSum p x
  let D : ℝ := ∑ i : Fin n, |x i| ^ (p - 2) * x i * h i
  have hsum : HasDerivAt
      (fun t : ℝ => ∑ i : Fin n, |x i + t * h i| ^ p)
      (p * D) 0 := by
    have hterms : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        HasDerivAt (fun t : ℝ => |x i + t * h i| ^ p)
          (p * |x i| ^ (p - 2) * x i * h i) 0 := by
      intro i _hi
      have hline : HasDerivAt (fun t : ℝ => x i + t * h i) (h i) 0 := by
        have hline' := (hasDerivAt_const (x := (0 : ℝ)) (x i)).add
          ((hasDerivAt_id (𝕜 := ℝ) 0).const_mul (h i))
        convert hline' using 1
        · funext t
          simp only [Pi.add_apply, id_eq]
          ring
        · ring
      have hbase : HasDerivAt (fun u : ℝ => |u| ^ p)
          (p * |x i| ^ (p - 2) * x i) (x i + 0 * h i) := by
        simpa using hasDerivAt_abs_rpow (x i) hp
      convert hbase.comp 0 hline using 1 <;> ring
    convert HasDerivAt.fun_sum hterms using 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  have hSpos : 0 < S := realLpPowerSum_pos hp hx
  have hrpow := hsum.rpow_const (p := p⁻¹) (Or.inl (by
    simpa [S, realLpPowerSum] using ne_of_gt hSpos))
  have hfun :
      (fun t : ℝ => realVecLpNorm p (fun i => x i + t * h i)) =
        (fun t : ℝ =>
          (∑ i : Fin n, |x i + t * h i| ^ p) ^ p⁻¹) := by
    funext t
    exact realVecLpNorm_eq_sum_rpow (zero_lt_one.trans hp) _
  rw [hfun]
  convert hrpow using 1
  unfold realLpGradient
  rw [show (∑ i : Fin n,
      (realLpPowerSum p x) ^ (p⁻¹ - 1) *
        (|x i| ^ (p - 2) * x i) * h i) =
      (realLpPowerSum p x) ^ (p⁻¹ - 1) * D by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ring]
  field_simp [ne_of_gt (zero_lt_one.trans hp)]
  <;> unfold realLpPowerSum
  <;> ring_nf

lemma realVecLpNorm_basisVec {n : ℕ} {p : ℝ} (hp : 1 ≤ p)
    (j : Fin n) :
    realVecLpNorm p (basisVec j) = 1 := by
  haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact hp⟩
  have h := complexVecLpNorm_standardBasisCVec
    (n := n) (ENNReal.ofReal p) j
  have heq : (fun i : Fin n => ((basisVec j i : ℝ) : ℂ)) =
      standardBasisCVec j := by
    funext i
    by_cases hij : i = j <;> simp [basisVec, standardBasisCVec, hij]
  rw [realVecLpNorm, heq]
  exact h

/-- Total unit normalized dual.  At zero, where every unit dual vector attains
the zero pairing, use the first coordinate vector. -/
noncomputable def realLpDualUnit {n : ℕ} (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q) (x : Fin n → ℝ) : Fin n → ℝ :=
  if x = 0 then basisVec ⟨0, hn⟩ else realLpDual hpq x

lemma realLpDualUnit_attains {n : ℕ} (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q) (x : Fin n → ℝ) :
    (∑ i : Fin n, realLpDualUnit hn hpq x i * x i) = realVecLpNorm p x := by
  by_cases hx : x = 0
  · simp [realLpDualUnit, hx, realVecLpNorm_zero (le_of_lt hpq.lt)]
  · simpa [realLpDualUnit, hx] using (realLpDual_spec hpq x).2

lemma realLpDualUnit_norm_eq_one {n : ℕ} (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q) (x : Fin n → ℝ) :
    realVecLpNorm q (realLpDualUnit hn hpq x) = 1 := by
  by_cases hx : x = 0
  · simp [realLpDualUnit, hx,
      realVecLpNorm_basisVec (le_of_lt hpq.symm.lt)]
  · simpa [realLpDualUnit, hx] using realLpDual_norm_eq_one hpq hx

/-- The exact induced matrix `l^p` norm for a real square matrix, inherited
from the repository's least-bound complex matrix `L^p` norm. -/
noncomputable def realMatrixLpNorm {n : ℕ} (hn : 0 < n)
    (p : ℝ) (hp : 1 ≤ p) (A : Fin n → Fin n → ℝ) : ℝ :=
  complexMatrixLpNormOfReal hn p hp (realRectToCMatrix A)

/-- Concrete general-`p` instance of every duality/operator primitive used by
Higham's p-norm power method. -/
noncomputable def pNormPair_general {n : ℕ} (hn : 0 < n)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin n → Fin n → ℝ) : PNormPair n where
  A := A
  pN := realVecLpNorm p
  qN := realVecLpNorm q
  opP := realMatrixLpNorm hn p (le_of_lt hpq.lt) A
  dp := realLpDual hpq
  dq := realLpDualUnit hn hpq.symm
  pN_nonneg := fun v => by
    haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
      rw [ENNReal.one_le_ofReal]
      exact le_of_lt hpq.lt⟩
    exact (complexVecLpNorm_isComplexVectorNorm
      (n := n) (ENNReal.ofReal p)).nonneg _
  dp_attains := fun v => (realLpDual_spec hpq v).2
  dp_qunit := fun v => (realLpDual_spec hpq v).1
  dq_attains := realLpDualUnit_attains hn hpq.symm
  dq_punit := realLpDualUnit_norm_eq_one hn hpq.symm
  holder := fun u v => (le_abs_self _).trans (realVecLpNorm_holder hpq u v)
  op_bound := fun v => by
    have hval := complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
      (m := n) (n := n) hn p (le_of_lt hpq.lt) (realRectToCMatrix A)
    have hbound := hval.1 (fun j : Fin n => (v j : ℂ))
    simpa [realMatrixLpNorm, realVecLpNorm, complexMatrixVecMul,
      realRectToCMatrix] using hbound

/-- The chosen concrete normalized dual is the actual gradient of the
finite-dimensional real `l^p` norm; this is derived from direct calculus and
Holder duality, not included as interface data. -/
theorem realLpDual_hasDirectionalGradientAt {n : ℕ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (x : Fin n → ℝ) (hx : x ≠ 0) :
    HasDirectionalGradientAt (realVecLpNorm p) (realLpDual hpq x) x := by
  have hraw := realVecLpNorm_hasDirectionalGradientAt hpq.lt x hx
  have hsub : IsSubgradient (realVecLpNorm p) x (realLpDual hpq x) := by
    intro v
    have hvnonneg : 0 ≤ realVecLpNorm p v := by
      haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
        rw [ENNReal.one_le_ofReal]
        exact le_of_lt hpq.lt⟩
      exact (complexVecLpNorm_isComplexVectorNorm
        (n := n) (ENNReal.ofReal p)).nonneg _
    have hdot : (∑ i : Fin n, realLpDual hpq x i * v i) ≤
        realVecLpNorm p v := by
      calc
        (∑ i : Fin n, realLpDual hpq x i * v i) ≤
            |∑ i : Fin n, realLpDual hpq x i * v i| := le_abs_self _
        _ ≤ realVecLpNorm q (realLpDual hpq x) * realVecLpNorm p v :=
          realVecLpNorm_holder hpq _ _
        _ ≤ 1 * realVecLpNorm p v :=
          mul_le_mul_of_nonneg_right (realLpDual_spec hpq x).1 hvnonneg
        _ = realVecLpNorm p v := one_mul _
    calc
      realVecLpNorm p x +
          (∑ i : Fin n, realLpDual hpq x i * (v i - x i)) =
          ∑ i : Fin n, realLpDual hpq x i * v i := by
            rw [← (realLpDual_spec hpq x).2]
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro i _hi
            ring
      _ ≤ realVecLpNorm p v := hdot
  have heq := unique_subgradient_of_directional_gradient
    (realVecLpNorm p) x (realLpGradient p x) (realLpDual hpq x)
    hraw hsub
  simpa [heq] using hraw

/-- Fully concrete smooth general-`p` instance (`1 < p,q < infinity`) for
Higham's equations (15.2), (15.3), and (15.5). -/
noncomputable def SmoothPNormPair.general {n : ℕ} (hn : 0 < n)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin n → Fin n → ℝ) : SmoothPNormPair n where
  P := pNormPair_general hn hpq A
  p := p
  q := q
  one_lt_p := hpq.lt
  one_lt_q := hpq.symm.lt
  conjugate := hpq.inv_add_inv_eq_one
  pN_zero := realVecLpNorm_zero (le_of_lt hpq.lt)
  pN_pos := fun x hx => realVecLpNorm_pos (le_of_lt hpq.lt) hx
  dp_qnorm_one := fun x hx => realLpDual_norm_eq_one hpq hx
  pN_gradient := fun x hx => realLpDual_hasDirectionalGradientAt hpq x hx

/-- The concrete square-matrix form of Higham's singleton subdifferential
formula (15.2), valid for every real Holder-conjugate `1 < p,q < infinity`. -/
theorem eq15_2_subdifferential_singleton_general {n : ℕ} (hn : 0 < n)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hfull : Function.Injective
      (fun v : Fin n → ℝ => fun i => ∑ j : Fin n, A i j * v j))
    (hx : x ≠ 0) :
    ∀ g, IsSubgradient
        (fun v : Fin n → ℝ =>
          realVecLpNorm p (fun i => ∑ j : Fin n, A i j * v j)) x g ↔
      g = fun j => ∑ i : Fin n, A i j *
        realLpDual hpq (fun r => ∑ k : Fin n, A r k * x k) i := by
  let S := SmoothPNormPair.general hn hpq A
  simpa [S, SmoothPNormPair.general, pNormPair_general,
    PNormPair.yof, PNormPair.zof] using
    S.eq15_2_subdifferential_singleton x hfull hx

/-- The concrete homogeneous quotient from Higham equation (15.3). -/
noncomputable def realLpQuotient {n : ℕ} (p : ℝ)
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  realVecLpNorm p (fun i => ∑ j : Fin n, A i j * x j) /
    realVecLpNorm p x

/-- The concrete right-hand side of Higham equation (15.3). -/
noncomputable def realLpQuotientGradient {n : ℕ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (A : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  fun j =>
    (∑ i : Fin n, A i j *
      realLpDual hpq (fun r => ∑ k : Fin n, A r k * x k) i) /
        realVecLpNorm p x -
      (realVecLpNorm p (fun r => ∑ k : Fin n, A r k * x k) /
        realVecLpNorm p x ^ 2) * realLpDual hpq x j

/-- Concrete, source-hypothesis form of equation (15.3): full rank and
`x ≠ 0` imply the displayed general-`p` quotient gradient. -/
theorem eq15_3_directional_general_of_full_rank {n : ℕ} (hn : 0 < n)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hfull : Function.Injective
      (fun v : Fin n → ℝ => fun i => ∑ j : Fin n, A i j * v j))
    (hx : x ≠ 0) :
    HasDirectionalGradientAt (realLpQuotient p A)
      (realLpQuotientGradient hpq A x) x := by
  let S := SmoothPNormPair.general hn hpq A
  simpa [S, SmoothPNormPair.general, pNormPair_general,
    SmoothPNormPair.eq15_3_F, SmoothPNormPair.eq15_3_gradient,
    PNormPair.yof, PNormPair.zof, realLpQuotient,
    realLpQuotientGradient] using
    S.eq15_3_directional_of_full_rank x hfull hx

/-! ## Literal rectangular source form (`A : R^{m x n}`) -/

noncomputable def realRectMatVec {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i => ∑ j : Fin n, A i j * x j

noncomputable def realRectTransposeVec {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (u : Fin m → ℝ) : Fin n → ℝ :=
  fun j => ∑ i : Fin m, A i j * u i

lemma realRectTranspose_pairing {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (u : Fin m → ℝ)
    (v : Fin n → ℝ) :
    (∑ j : Fin n, realRectTransposeVec A u j * v j) =
      ∑ i : Fin m, u i * realRectMatVec A v i := by
  unfold realRectTransposeVec realRectMatVec
  calc
    (∑ j : Fin n, (∑ i : Fin m, A i j * u i) * v j) =
        ∑ j : Fin n, ∑ i : Fin m, (A i j * u i) * v j := by
          apply Finset.sum_congr rfl
          intro j _hj
          rw [Finset.sum_mul]
    _ = ∑ i : Fin m, ∑ j : Fin n, (A i j * u i) * v j :=
      Finset.sum_comm
    _ = ∑ i : Fin m, u i * ∑ j : Fin n, A i j * v j := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring

lemma realRectMatVec_add_smul {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (x h : Fin n → ℝ) (t : ℝ) :
    realRectMatVec A (fun j => x j + t * h j) =
      fun i => realRectMatVec A x i + t * realRectMatVec A h i := by
  funext i
  unfold realRectMatVec
  calc
    (∑ j : Fin n, A i j * (x j + t * h j)) =
        ∑ j : Fin n, (A i j * x j + t * (A i j * h j)) := by
          apply Finset.sum_congr rfl
          intro j _hj
          ring
    _ = (∑ j : Fin n, A i j * x j) +
        ∑ j : Fin n, t * (A i j * h j) := Finset.sum_add_distrib
    _ = (∑ j : Fin n, A i j * x j) +
        t * ∑ j : Fin n, A i j * h j := by rw [Finset.mul_sum]

/-- Chain rule for the literal rectangular numerator `x |-> ||A x||_p`. -/
theorem realRectLpComposite_hasDirectionalGradientAt {m n : ℕ}
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hy : realRectMatVec A x ≠ 0) :
    HasDirectionalGradientAt
      (fun v => realVecLpNorm p (realRectMatVec A v))
      (realRectTransposeVec A (realLpDual hpq (realRectMatVec A x))) x := by
  intro h
  have hbase := realLpDual_hasDirectionalGradientAt hpq
    (realRectMatVec A x) hy (realRectMatVec A h)
  convert hbase using 1
  · funext t
    change realVecLpNorm p (realRectMatVec A (fun i => x i + t * h i)) = _
    rw [realRectMatVec_add_smul]
  · exact realRectTranspose_pairing A _ h

/-- The concrete dual vector is a subgradient of the concrete real `l^p`
norm, derived solely from Holder attainment and its unit dual norm. -/
theorem realLpDual_isSubgradient {n : ℕ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (x : Fin n → ℝ) :
    IsSubgradient (realVecLpNorm p) x (realLpDual hpq x) := by
  intro v
  have hvnonneg : 0 ≤ realVecLpNorm p v := by
    haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
      rw [ENNReal.one_le_ofReal]
      exact le_of_lt hpq.lt⟩
    exact (complexVecLpNorm_isComplexVectorNorm
      (n := n) (ENNReal.ofReal p)).nonneg _
  have hdot : (∑ i : Fin n, realLpDual hpq x i * v i) ≤
      realVecLpNorm p v := by
    calc
      (∑ i : Fin n, realLpDual hpq x i * v i) ≤
          |∑ i : Fin n, realLpDual hpq x i * v i| := le_abs_self _
      _ ≤ realVecLpNorm q (realLpDual hpq x) * realVecLpNorm p v :=
        realVecLpNorm_holder hpq _ _
      _ ≤ 1 * realVecLpNorm p v :=
        mul_le_mul_of_nonneg_right (realLpDual_spec hpq x).1 hvnonneg
      _ = realVecLpNorm p v := one_mul _
  calc
    realVecLpNorm p x +
        (∑ i : Fin n, realLpDual hpq x i * (v i - x i)) =
        ∑ i : Fin n, realLpDual hpq x i * v i := by
          rw [← (realLpDual_spec hpq x).2, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _hi
          ring
    _ ≤ realVecLpNorm p v := hdot

/-- The transpose dual produced from `A x` is a global subgradient of the
literal rectangular map `x |-> ||A x||_p`. -/
theorem realRectLpComposite_isSubgradient {m n : ℕ}
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    IsSubgradient (fun v => realVecLpNorm p (realRectMatVec A v)) x
      (realRectTransposeVec A (realLpDual hpq (realRectMatVec A x))) := by
  intro v
  have hbase := realLpDual_isSubgradient hpq (realRectMatVec A x)
    (realRectMatVec A v)
  calc
    realVecLpNorm p (realRectMatVec A x) +
        (∑ j : Fin n,
          realRectTransposeVec A (realLpDual hpq (realRectMatVec A x)) j *
            (v j - x j)) =
      realVecLpNorm p (realRectMatVec A x) +
        (∑ i : Fin m, realLpDual hpq (realRectMatVec A x) i *
          (realRectMatVec A v i - realRectMatVec A x i)) := by
            congr 1
            rw [realRectTranspose_pairing]
            apply Finset.sum_congr rfl
            intro i _hi
            congr 1
            unfold realRectMatVec
            calc
              (∑ j : Fin n, A i j * (v j - x j)) =
                  ∑ j : Fin n, (A i j * v j - A i j * x j) := by
                    apply Finset.sum_congr rfl
                    intro j _hj
                    ring
              _ = (∑ j : Fin n, A i j * v j) -
                  ∑ j : Fin n, A i j * x j := by
                    rw [Finset.sum_sub_distrib]
    _ ≤ realVecLpNorm p (realRectMatVec A v) := hbase

/-- **Higham (15.2), literal rectangular source strength.**  For a full
column-rank real `m x n` matrix and nonzero `x`, the subdifferential of
`x |-> ||A x||_p` is the displayed singleton for every `1 < p < infinity`. -/
theorem eq15_2_subdifferential_singleton_general_rect {m n : ℕ}
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hfull : Function.Injective (realRectMatVec A)) (hx : x ≠ 0) :
    ∀ g, IsSubgradient
        (fun v => realVecLpNorm p (realRectMatVec A v)) x g ↔
      g = realRectTransposeVec A (realLpDual hpq (realRectMatVec A x)) := by
  have hy : realRectMatVec A x ≠ 0 := by
    intro hy0
    apply hx
    apply hfull
    rw [hy0]
    funext i
    simp [realRectMatVec]
  have hgrad := realRectLpComposite_hasDirectionalGradientAt hpq A x hy
  intro g
  constructor
  · intro hg
    exact unique_subgradient_of_directional_gradient _ x _ g hgrad hg
  · intro hg
    subst g
    exact realRectLpComposite_isSubgradient hpq A x

noncomputable def realRectLpQuotient {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  realVecLpNorm p (realRectMatVec A x) / realVecLpNorm p x

noncomputable def realRectLpQuotientGradient {m n : ℕ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  fun j =>
    realRectTransposeVec A (realLpDual hpq (realRectMatVec A x)) j /
        realVecLpNorm p x -
      (realVecLpNorm p (realRectMatVec A x) / realVecLpNorm p x ^ 2) *
        realLpDual hpq x j

/-- **Higham (15.3), literal rectangular source strength.**  Full column rank
and `x ≠ 0` suffice for the displayed quotient gradient. -/
theorem eq15_3_directional_general_rect_of_full_rank {m n : ℕ}
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hfull : Function.Injective (realRectMatVec A)) (hx : x ≠ 0) :
    HasDirectionalGradientAt (realRectLpQuotient p A)
      (realRectLpQuotientGradient hpq A x) x := by
  have hy : realRectMatVec A x ≠ 0 := by
    intro hy0
    apply hx
    apply hfull
    rw [hy0]
    funext i
    simp [realRectMatVec]
  intro h
  have hnum := realRectLpComposite_hasDirectionalGradientAt hpq A x hy h
  have hden := realLpDual_hasDirectionalGradientAt hpq x hx h
  have hxnorm : realVecLpNorm p x ≠ 0 :=
    ne_of_gt (realVecLpNorm_pos (le_of_lt hpq.lt) hx)
  have hxnorm0 : realVecLpNorm p (fun i => x i + 0 * h i) ≠ 0 := by
    simpa using hxnorm
  have hquot := hnum.div hden hxnorm0
  change HasDerivAt
    (fun t : ℝ => realRectLpQuotient p A (fun i => x i + t * h i))
    (∑ i : Fin n, realRectLpQuotientGradient hpq A x i * h i) 0
  convert hquot using 1
  simp only [zero_mul, add_zero]
  unfold realRectLpQuotientGradient
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  rw [show (∑ i : Fin n,
        realRectTransposeVec A (realLpDual hpq (realRectMatVec A x)) i /
          realVecLpNorm p x * h i) =
        (∑ i : Fin n,
          realRectTransposeVec A (realLpDual hpq (realRectMatVec A x)) i * h i) /
            realVecLpNorm p x by
      calc
        _ = (realVecLpNorm p x)⁻¹ *
            (∑ i : Fin n,
              realRectTransposeVec A (realLpDual hpq (realRectMatVec A x)) i * h i) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro i _hi
                rw [div_eq_mul_inv]
                ring
        _ = _ := by rw [div_eq_mul_inv]; ring]
  rw [show (∑ i : Fin n,
        realVecLpNorm p (realRectMatVec A x) / realVecLpNorm p x ^ 2 *
          realLpDual hpq x i * h i) =
        (realVecLpNorm p (realRectMatVec A x) / realVecLpNorm p x ^ 2) *
          (∑ i : Fin n, realLpDual hpq x i * h i) by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      ring]
  field_simp [hxnorm]

end Ch15
end NumStability
