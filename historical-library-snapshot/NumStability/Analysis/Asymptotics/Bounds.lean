-- Analysis/Asymptotics/Bounds.lean
--
-- Elementary asymptotic estimates used by stability bounds.

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Elementary asymptotic bounds

Provides small reusable limit and eventual-bound lemmas for scalar sequences
appearing in perturbation and conditioning arguments.
-/

namespace NumStability

/-- A real-valued convergence squeeze used by the perturbation-limit
    condition-number layer: if `Q i` is eventually within an error `err i` of
    `c`, and the error tends to zero, then `Q i` tends to `c`. -/
theorem tendsto_of_eventually_abs_sub_le_tendsto_zero
    {ι : Type*} {l : Filter ι} {Q err : ι → ℝ} {c : ℝ}
    (herr : Filter.Tendsto err l (nhds 0))
    (hbound : Filter.Eventually (fun i => |Q i - c| ≤ err i) l) :
    Filter.Tendsto Q l (nhds c) := by
  refine Metric.tendsto_nhds.mpr ?_
  intro ε hε
  have herr_ev : Filter.Eventually (fun i => err i < ε) l := by
    have h := (Metric.tendsto_nhds.mp herr) ε hε
    filter_upwards [h] with i hi
    have hiabs : |err i| < ε := by
      simpa [Real.dist_eq] using hi
    exact (le_abs_self (err i)).trans_lt hiabs
  filter_upwards [hbound, herr_ev] with i hb he
  have hdist : dist (Q i) c ≤ err i := by
    simpa [Real.dist_eq] using hb
  exact lt_of_le_of_lt hdist he

/-- Real squeeze principle for indexed quantities bounded between two functions
    that tend to the same limit. -/
theorem tendsto_of_eventually_between_tendsto
    {ι : Type*} {l : Filter ι} {L Q U : ι → ℝ} {c : ℝ}
    (hL : Filter.Tendsto L l (nhds c))
    (hU : Filter.Tendsto U l (nhds c))
    (hbetween : Filter.Eventually (fun i => L i ≤ Q i ∧ Q i ≤ U i) l) :
    Filter.Tendsto Q l (nhds c) := by
  refine Metric.tendsto_nhds.mpr ?_
  intro ε hε
  have hL_ev : Filter.Eventually (fun i => dist (L i) c < ε) l :=
    (Metric.tendsto_nhds.mp hL) ε hε
  have hU_ev : Filter.Eventually (fun i => dist (U i) c < ε) l :=
    (Metric.tendsto_nhds.mp hU) ε hε
  filter_upwards [hL_ev, hU_ev, hbetween] with i hLi hUi hbetween_i
  have hL_abs : |L i - c| < ε := by
    simpa [Real.dist_eq] using hLi
  have hU_abs : |U i - c| < ε := by
    simpa [Real.dist_eq] using hUi
  have hQ_abs : |Q i - c| < ε := by
    have hL_bounds := abs_lt.mp hL_abs
    have hU_bounds := abs_lt.mp hU_abs
    exact abs_lt.mpr ⟨by linarith [hbetween_i.1], by linarith [hbetween_i.2]⟩
  simpa [Real.dist_eq] using hQ_abs

/-- A bounded-factor convergence lemma for the Theorem 6.4 perturbation-limit
    route: multiplying a quantity tending to zero by an eventually bounded real
    factor and a fixed positive constant still tends to zero. -/
theorem tendsto_const_mul_of_tendsto_zero_of_eventually_abs_le
    {ι : Type*} {l : Filter ι} {d b : ι → ℝ} {K B : ℝ}
    (hK : 0 < K) (hB0 : 0 ≤ B)
    (hd : Filter.Tendsto d l (nhds 0))
    (hb : Filter.Eventually (fun i => |b i| ≤ B) l) :
    Filter.Tendsto (fun i => K * d i * b i) l (nhds 0) := by
  refine Metric.tendsto_nhds.mpr ?_
  intro ε hε
  have hB1pos : 0 < B + 1 := by linarith
  have hdenpos : 0 < K * (B + 1) := mul_pos hK hB1pos
  have hd_ev :
      Filter.Eventually (fun i => dist (d i) 0 < ε / (K * (B + 1))) l :=
    (Metric.tendsto_nhds.mp hd) (ε / (K * (B + 1))) (div_pos hε hdenpos)
  filter_upwards [hd_ev, hb] with i hdi hbi
  have hdi_abs : |d i| < ε / (K * (B + 1)) := by
    simpa [Real.dist_eq] using hdi
  have hbi_le : |b i| ≤ B + 1 := hbi.trans (by linarith)
  have hprod_le : |K * d i * b i| ≤ K * |d i| * (B + 1) := by
    have hleft : K * |d i| * |b i| ≤ K * |d i| * (B + 1) :=
      mul_le_mul_of_nonneg_left hbi_le (mul_nonneg (le_of_lt hK) (abs_nonneg _))
    simpa [abs_mul, abs_of_pos hK, mul_assoc] using hleft
  have hmul : K * |d i| < K * (ε / (K * (B + 1))) :=
    mul_lt_mul_of_pos_left hdi_abs hK
  have htarget : K * |d i| * (B + 1) < ε := by
    have hmul2 :
        K * |d i| * (B + 1) < (K * (ε / (K * (B + 1)))) * (B + 1) :=
      mul_lt_mul_of_pos_right hmul hB1pos
    have hsimp : (K * (ε / (K * (B + 1)))) * (B + 1) = ε := by
      field_simp [ne_of_gt hK, ne_of_gt hB1pos]
    exact hmul2.trans_eq hsimp
  have hfinal : |K * d i * b i| < ε := hprod_le.trans_lt htarget
  simpa [Real.dist_eq] using hfinal
end NumStability
