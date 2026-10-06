import HighamBench.P14Definitions
import NumStability.Algorithms.Summation.Recursive.Core

namespace HighamBench

open scoped BigOperators

noncomputable def p14StandardAddModelToFPModel
    (fp : StandardAddModel) : NumStability.FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := fun x y => x - y
  fl_mul := fun x y => x * y
  fl_div := fun x y => x / y
  fl_sqrt := Real.sqrt
  fl_add_zero := fp.fl_add_zero
  model_add := fp.model_add
  model_sub := by
    intro x y
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_mul := by
    intro x y
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_div := by
    intro x y _
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_sqrt := by
    intro x _
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩

lemma p14_recursiveSum_eq_fl_recursiveSum
    (fp : StandardAddModel) : ∀ (n : ℕ) (v : Fin n → ℝ),
      recursiveSum fp.fl_add n v =
        NumStability.fl_recursiveSum (p14StandardAddModelToFPModel fp) n v
  | 0, v => by
      simp [recursiveSum, NumStability.fl_recursiveSum]
  | n + 1, v => by
      by_cases hn : n = 0
      · subst n
        rw [recursiveSum, dif_pos rfl]
        rw [NumStability.fl_recursiveSum, Fin.foldl_succ_last,
          Fin.foldl_zero]
        exact fp.fl_add_zero (v (Fin.last 0)) |>.symm
      · rw [recursiveSum, dif_neg hn]
        rw [NumStability.fl_recursiveSum, Fin.foldl_succ_last]
        rw [← NumStability.fl_recursiveSum]
        rw [p14_recursiveSum_eq_fl_recursiveSum fp n
          (fun i : Fin n => v i.castSucc)]
        rfl

theorem p14_t1_positive_recursive_sum_relative_error
    {n : ℕ} (hn : 0 < n)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (x : Fin n → ℝ)
    (u : ι → ℝ)
    (run : ∀ t, P14BasicSumExecution x (u t))
    (hu : Filter.Tendsto u l (nhds 0)) :
    let exactSum := p14ExpSum x
    0 < exactSum ∧
    (∀ t i,
      |p14ComputedExp (run t) i - Real.exp (x i)| ≤
        u t * Real.exp (x i)) ∧
    (∃ remainder : ι → ℝ,
      remainder =O[l] (fun t => (u t) ^ 2) ∧
      ∀ᶠ t in l,
        |p14BasicSumDelta (run t)| ≤
          (n + 1 : ℝ) * u t * exactSum + |remainder t|) ∧
    ∀ t,
      p14RecursiveComputedExpSum (run t) =
        exactSum + p14BasicSumDelta (run t) := by
  -- PROOF_START P14-T1-H001
  dsimp only
  have hexact : 0 < p14ExpSum x := by
    unfold p14ExpSum
    apply Finset.sum_pos
    · intro i _
      exact Real.exp_pos _
    · exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hexp : ∀ t i,
      |p14ComputedExp (run t) i - Real.exp (x i)| ≤
        u t * Real.exp (x i) := by
    intro t i
    calc
      |p14ComputedExp (run t) i - Real.exp (x i)| =
          |Real.exp (x i) * (run t).expError i| := by
            congr 1
            simp only [p14ComputedExp]
            ring
      _ = Real.exp (x i) * |(run t).expError i| := by
            rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      _ ≤ Real.exp (x i) * u t :=
            mul_le_mul_of_nonneg_left ((run t).expError_le i)
              (Real.exp_pos _).le
      _ = u t * Real.exp (x i) := by ring
  refine ⟨hexact, hexp, ?_, ?_⟩
  · refine ⟨fun _ => 0, ?_, ?_⟩
    · exact Asymptotics.isBigO_zero _ _
    · let m : ℝ := ((n - 1 : ℕ) : ℝ)
      let c : ℝ := m * (m + 2)
      have hscaled : Filter.Tendsto (fun t => c * u t) l (nhds 0) := by
        simpa using (tendsto_const_nhds.mul hu :
          Filter.Tendsto (fun t => c * u t) l (nhds (c * 0)))
      have hsmall : ∀ᶠ t in l, c * u t ≤ 1 := by
        filter_upwards [((tendsto_order.1 hscaled).2 1 (by norm_num))]
          with t ht
        exact ht.le
      have hvalid : ∀ᶠ t in l,
          NumStability.gammaValid
            (p14StandardAddModelToFPModel (run t).fp) (n - 1) := by
        have hmScaled : Filter.Tendsto (fun t => m * u t) l (nhds 0) := by
          simpa using (tendsto_const_nhds.mul hu :
            Filter.Tendsto (fun t => m * u t) l (nhds (m * 0)))
        filter_upwards [((tendsto_order.1 hmScaled).2 1 (by norm_num))]
          with t ht
        simpa [NumStability.gammaValid, p14StandardAddModelToFPModel,
          (run t).unit_eq, m] using ht
      filter_upwards [hsmall, hvalid] with t hsmall_t hvalid_t
      have hu_nonneg : 0 ≤ u t := by
        simpa [(run t).unit_eq] using (run t).fp.u_nonneg
      have hm_nonneg : 0 ≤ m := by
        dsimp [m]
        positivity
      have hnm : (n : ℝ) = m + 1 := by
        dsimp [m]
        norm_num
        exact_mod_cast (Nat.sub_add_cancel hn).symm
      have hgamma :
          NumStability.gamma
              (p14StandardAddModelToFPModel (run t).fp) (n - 1) *
              (1 + u t) ≤ (n : ℝ) * u t := by
        have hden : 0 < 1 - m * u t := by
          simpa [NumStability.gammaValid, p14StandardAddModelToFPModel,
            (run t).unit_eq, m] using hvalid_t
        rw [NumStability.gamma]
        simp only [p14StandardAddModelToFPModel, (run t).unit_eq]
        change (m * u t / (1 - m * u t)) * (1 + u t) ≤
          (n : ℝ) * u t
        rw [div_mul_eq_mul_div, div_le_iff₀ hden]
        rw [hnm]
        dsimp [c] at hsmall_t
        nlinarith
      have habsSum :
          ∑ i : Fin n, |p14ComputedExp (run t) i| ≤
            (1 + u t) * p14ExpSum x := by
        unfold p14ExpSum
        calc
          ∑ i : Fin n, |p14ComputedExp (run t) i| ≤
              ∑ i : Fin n, Real.exp (x i) * (1 + u t) := by
                apply Finset.sum_le_sum
                intro i _
                rw [p14ComputedExp, abs_mul,
                  abs_of_pos (Real.exp_pos _)]
                apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
                calc
                  |1 + (run t).expError i| ≤
                      |(1 : ℝ)| + |(run t).expError i| := abs_add_le _ _
                  _ ≤ 1 + u t := by
                    simpa using add_le_add_left ((run t).expError_le i) 1
          _ = (1 + u t) * ∑ i : Fin n, Real.exp (x i) := by
                rw [← Finset.sum_mul]
                ring
      have hsumInput :
          |p14ExactComputedExpSum (run t) - p14ExpSum x| ≤
            u t * p14ExpSum x := by
        unfold p14ExactComputedExpSum p14ExpSum
        rw [← Finset.sum_sub_distrib]
        calc
          |∑ i : Fin n,
              (p14ComputedExp (run t) i - Real.exp (x i))| ≤
              ∑ i : Fin n,
                |p14ComputedExp (run t) i - Real.exp (x i)| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i : Fin n, u t * Real.exp (x i) := by
            exact Finset.sum_le_sum fun i _ => hexp t i
          _ = u t * ∑ i : Fin n, Real.exp (x i) := by
            rw [Finset.mul_sum]
      have hrecursive :
          |p14RecursiveComputedExpSum (run t) -
              p14ExactComputedExpSum (run t)| ≤
            NumStability.gamma
                (p14StandardAddModelToFPModel (run t).fp) (n - 1) *
              ∑ i : Fin n, |p14ComputedExp (run t) i| := by
        simpa [p14RecursiveComputedExpSum, p14ExactComputedExpSum,
          p14_recursiveSum_eq_fl_recursiveSum] using
            (NumStability.recursiveSum_forward_error_bound
              (p14StandardAddModelToFPModel (run t).fp) n
              (p14ComputedExp (run t)) hvalid_t)
      have hrecursive' :
          |p14RecursiveComputedExpSum (run t) -
              p14ExactComputedExpSum (run t)| ≤
            (n : ℝ) * u t * p14ExpSum x := by
        calc
          |p14RecursiveComputedExpSum (run t) -
              p14ExactComputedExpSum (run t)| ≤
              NumStability.gamma
                  (p14StandardAddModelToFPModel (run t).fp) (n - 1) *
                ∑ i : Fin n, |p14ComputedExp (run t) i| := hrecursive
          _ ≤ NumStability.gamma
                  (p14StandardAddModelToFPModel (run t).fp) (n - 1) *
                ((1 + u t) * p14ExpSum x) := by
              apply mul_le_mul_of_nonneg_left habsSum
              exact NumStability.gamma_nonneg _ hvalid_t
          _ = (NumStability.gamma
                  (p14StandardAddModelToFPModel (run t).fp) (n - 1) *
                (1 + u t)) * p14ExpSum x := by ring
          _ ≤ ((n : ℝ) * u t) * p14ExpSum x :=
              mul_le_mul_of_nonneg_right hgamma hexact.le
      rw [abs_zero, add_zero]
      unfold p14BasicSumDelta
      calc
        |p14RecursiveComputedExpSum (run t) - p14ExpSum x| ≤
            |p14RecursiveComputedExpSum (run t) -
                p14ExactComputedExpSum (run t)| +
              |p14ExactComputedExpSum (run t) - p14ExpSum x| := by
                  have := abs_add_le
                    (p14RecursiveComputedExpSum (run t) -
                      p14ExactComputedExpSum (run t))
                    (p14ExactComputedExpSum (run t) - p14ExpSum x)
                  convert this using 1 <;> ring
        _ ≤ (n : ℝ) * u t * p14ExpSum x +
              u t * p14ExpSum x := add_le_add hrecursive' hsumInput
        _ = (n + 1 : ℝ) * u t * p14ExpSum x := by ring
  · intro t
    unfold p14BasicSumDelta
    ring

end HighamBench
