import HighamBench.P14Definitions
import NumStability.Algorithms.Summation.Recursive.Core

namespace HighamBench

open scoped BigOperators

noncomputable def p14FPModelOfStandardAddModel
    (fp : StandardAddModel) : NumStability.FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := fun a b => a - b
  fl_mul := fun a b => a * b
  fl_div := fun a b => a / b
  fl_sqrt := Real.sqrt
  fl_add_zero := fp.fl_add_zero
  model_add := fp.model_add
  model_sub := by
    intro a b
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_mul := by
    intro a b
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_div := by
    intro a b _
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_sqrt := by
    intro a _
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩

lemma p14_recursiveSum_eq_fl_recursiveSum
    (fp : StandardAddModel) :
    ∀ (n : ℕ) (v : Fin n → ℝ),
      recursiveSum fp.fl_add n v =
        NumStability.fl_recursiveSum (p14FPModelOfStandardAddModel fp) n v := by
  intro n
  induction n with
  | zero =>
      intro v
      simp [recursiveSum, NumStability.fl_recursiveSum]
  | succ n ih =>
      intro v
      rw [NumStability.fl_recursiveSum, Fin.foldl_succ_last]
      change recursiveSum fp.fl_add (n + 1) v =
        fp.fl_add
          (NumStability.fl_recursiveSum (p14FPModelOfStandardAddModel fp) n
            (fun i => v i.castSucc))
          (v (Fin.last n))
      by_cases hn : n = 0
      · subst n
        simp [recursiveSum, NumStability.fl_recursiveSum, fp.fl_add_zero]
      · rw [recursiveSum]
        simp only [hn, ↓reduceDIte]
        rw [ih]

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
  dsimp
  have hexact_pos : 0 < p14ExpSum x := by
    apply Finset.sum_pos
    · intro i _
      exact Real.exp_pos _
    · exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hu_nonneg : ∀ t, 0 ≤ u t := by
    intro t
    rw [← (run t).unit_eq]
    exact (run t).fp.u_nonneg
  have hexp_error : ∀ t i,
      |p14ComputedExp (run t) i - Real.exp (x i)| ≤
        u t * Real.exp (x i) := by
    intro t i
    rw [p14ComputedExp]
    have h := (run t).expError_le i
    calc
      |Real.exp (x i) * (1 + (run t).expError i) - Real.exp (x i)| =
          |Real.exp (x i) * (run t).expError i| := by
            congr 1
            ring
      _ = Real.exp (x i) * |(run t).expError i| := by
            rw [abs_mul, abs_of_pos (Real.exp_pos (x i))]
      _ ≤ Real.exp (x i) * u t :=
            mul_le_mul_of_nonneg_left h (le_of_lt (Real.exp_pos (x i)))
      _ = u t * Real.exp (x i) := mul_comm _ _
  refine ⟨hexact_pos, hexp_error, ?_, ?_⟩
  · let remainder : ι → ℝ :=
      fun t => (n : ℝ) * p14ExpSum x * (u t) ^ 2
    refine ⟨remainder, ?_, ?_⟩
    · exact Asymptotics.isBigO_const_mul_self
        ((n : ℝ) * p14ExpSum x) (fun t => (u t) ^ 2) l
    · have hgamma_tendsto :
          Filter.Tendsto (fun t => (((n - 1 : ℕ) : ℝ) * u t)) l (nhds 0) := by
          simpa using hu.const_mul (((n - 1 : ℕ) : ℝ))
      have hgamma_eventually :
          ∀ᶠ t in l, (((n - 1 : ℕ) : ℝ) * u t) < 1 :=
        (tendsto_order.1 hgamma_tendsto).2 1 (by norm_num)
      have hsmall_tendsto :
          Filter.Tendsto
            (fun t => (n : ℝ) * (((n - 1 : ℕ) : ℝ) * u t))
            l (nhds 0) := by
          simpa using hgamma_tendsto.const_mul (n : ℝ)
      have hsmall_eventually :
          ∀ᶠ t in l,
            (n : ℝ) * (((n - 1 : ℕ) : ℝ) * u t) ≤ 1 :=
        ((tendsto_order.1 hsmall_tendsto).2 1 (by norm_num)).mono
          (fun _ h => le_of_lt h)
      filter_upwards [hgamma_eventually, hsmall_eventually] with t hvalid hsmall
      let fp := p14FPModelOfStandardAddModel (run t).fp
      let v : Fin n → ℝ := p14ComputedExp (run t)
      have hfp_u : fp.u = u t := by
        simpa [fp, p14FPModelOfStandardAddModel] using (run t).unit_eq
      have hvalid_fp : NumStability.gammaValid fp (n - 1) := by
        simpa [NumStability.gammaValid, hfp_u] using hvalid
      have hsmall_fp :
          (n : ℝ) * (((n - 1 : ℕ) : ℝ) * fp.u) ≤ 1 := by
        simpa [hfp_u] using hsmall
      have hgamma :
          NumStability.gamma fp (n - 1) ≤ (n : ℝ) * u t := by
        rw [← hfp_u]
        exact NumStability.gamma_pred_le_n_mul_u_of_n_mul_pred_u_le_one
          fp hn hvalid_fp hsmall_fp
      have hv_abs :
          ∑ i : Fin n, |v i| ≤ (1 + u t) * p14ExpSum x := by
        calc
          ∑ i : Fin n, |v i| ≤
              ∑ i : Fin n, (1 + u t) * Real.exp (x i) := by
                apply Finset.sum_le_sum
                intro i _
                calc
                  |v i| ≤ |Real.exp (x i)| + |v i - Real.exp (x i)| := by
                    have := abs_add_le (Real.exp (x i)) (v i - Real.exp (x i))
                    simpa [add_sub_cancel] using this
                  _ ≤ Real.exp (x i) + u t * Real.exp (x i) := by
                    exact add_le_add (le_of_eq (abs_of_pos (Real.exp_pos (x i))))
                      (hexp_error t i)
                  _ = (1 + u t) * Real.exp (x i) := by ring
          _ = (1 + u t) * p14ExpSum x := by
                simp [p14ExpSum, Finset.mul_sum]
      have hsum_error :
          |∑ i : Fin n, v i - p14ExpSum x| ≤ u t * p14ExpSum x := by
        calc
          |∑ i : Fin n, v i - p14ExpSum x| =
              |∑ i : Fin n, (v i - Real.exp (x i))| := by
                congr 1
                simp [p14ExpSum, Finset.sum_sub_distrib]
          _ ≤ ∑ i : Fin n, |v i - Real.exp (x i)| :=
                Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i : Fin n, u t * Real.exp (x i) := by
                exact Finset.sum_le_sum (fun i _ => hexp_error t i)
          _ = u t * p14ExpSum x := by
                simp [p14ExpSum, Finset.mul_sum]
      have hrecursive :
          |p14RecursiveComputedExpSum (run t) - ∑ i : Fin n, v i| ≤
            NumStability.gamma fp (n - 1) * ∑ i : Fin n, |v i| := by
        simpa [p14RecursiveComputedExpSum, fp, v,
          p14_recursiveSum_eq_fl_recursiveSum] using
          NumStability.recursiveSum_forward_error_bound fp n v hvalid_fp
      have hround_bound :
          |p14RecursiveComputedExpSum (run t) - ∑ i : Fin n, v i| ≤
            ((n : ℝ) * u t) * ((1 + u t) * p14ExpSum x) := by
        calc
          |p14RecursiveComputedExpSum (run t) - ∑ i : Fin n, v i| ≤
              NumStability.gamma fp (n - 1) * ∑ i : Fin n, |v i| := hrecursive
          _ ≤ ((n : ℝ) * u t) * ∑ i : Fin n, |v i| := by
                exact mul_le_mul_of_nonneg_right hgamma
                  (Finset.sum_nonneg fun _ _ => abs_nonneg _)
          _ ≤ ((n : ℝ) * u t) * ((1 + u t) * p14ExpSum x) := by
                exact mul_le_mul_of_nonneg_left hv_abs
                  (mul_nonneg (by positivity) (hu_nonneg t))
      change
        |p14RecursiveComputedExpSum (run t) - p14ExpSum x| ≤
          (n + 1 : ℝ) * u t * p14ExpSum x + |remainder t|
      calc
        |p14RecursiveComputedExpSum (run t) - p14ExpSum x| ≤
            |p14RecursiveComputedExpSum (run t) - ∑ i : Fin n, v i| +
              |∑ i : Fin n, v i - p14ExpSum x| := by
                have := abs_add_le
                  (p14RecursiveComputedExpSum (run t) - ∑ i : Fin n, v i)
                  (∑ i : Fin n, v i - p14ExpSum x)
                simpa only [sub_add_sub_cancel] using this
        _ ≤ ((n : ℝ) * u t) * ((1 + u t) * p14ExpSum x) +
              u t * p14ExpSum x := add_le_add hround_bound hsum_error
        _ = (n + 1 : ℝ) * u t * p14ExpSum x + |remainder t| := by
              dsimp [remainder]
              rw [abs_of_nonneg]
              · push_cast
                ring
              · positivity
  · intro t
    unfold p14BasicSumDelta
    ring

end HighamBench
