import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.NormEstimation.OneNorm.FiniteIndex.Basic
import NumStability.Algorithms.NormEstimation.OneNorm.PowerMethod.CondEstimation
import NumStability.Algorithms.NormEstimation.PNorm.Duality.PNormPowerMethod
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification

/-!
# NumStability Algorithms NormEstimation PNorm Duality PNormGeneral

Canonical destination for material split out of
`NumStability.Algorithms.PNormPowerMethodGeneralP` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

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

end Ch15
end NumStability
