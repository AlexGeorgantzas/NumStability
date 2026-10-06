import HighamBench.P14Definitions
import NumStability.Algorithms.Summation.Recursive.Core

namespace HighamBench

open scoped BigOperators

noncomputable def p14FPModelOfStandardAddModel (fp : StandardAddModel) :
    NumStability.FPModel where
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

lemma p14_recursiveSum_eq_fl_recursiveSum (fp : StandardAddModel) :
    ∀ (m : ℕ) (v : Fin m → ℝ),
      recursiveSum fp.fl_add m v =
        NumStability.fl_recursiveSum (p14FPModelOfStandardAddModel fp) m v
  | 0, v => by
      simp [recursiveSum, NumStability.fl_recursiveSum]
  | m + 1, v => by
      unfold NumStability.fl_recursiveSum
      rw [Fin.foldl_succ_last]
      change recursiveSum fp.fl_add (m + 1) v =
        fp.fl_add
          (NumStability.fl_recursiveSum (p14FPModelOfStandardAddModel fp) m
            (fun i : Fin m => v i.castSucc))
          (v (Fin.last m))
      rw [← p14_recursiveSum_eq_fl_recursiveSum fp m
        (fun i : Fin m => v i.castSucc)]
      by_cases hm : m = 0
      · subst m
        simp [recursiveSum, fp.fl_add_zero]
      · simp [recursiveSum, hm]

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
  have hexact_pos : 0 < p14ExpSum x := by
    letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    unfold p14ExpSum
    positivity
  have hexp_error : ∀ t i,
      |p14ComputedExp (run t) i - Real.exp (x i)| ≤
        u t * Real.exp (x i) := by
    intro t i
    rw [p14ComputedExp]
    have hrewrite :
        Real.exp (x i) * (1 + (run t).expError i) - Real.exp (x i) =
          Real.exp (x i) * (run t).expError i := by ring
    rw [hrewrite, abs_mul, abs_of_pos (Real.exp_pos (x i))]
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left ((run t).expError_le i)
        (le_of_lt (Real.exp_pos (x i)))
  refine ⟨hexact_pos, hexp_error, ?_, ?_⟩
  · let R : ι → ℝ := fun t =>
        (n : ℝ) * p14ExpSum x * (u t) ^ 2
    refine ⟨R, ?_, ?_⟩
    · dsimp [R]
      simpa only [mul_assoc] using
        (Asymptotics.isBigO_const_mul_self ((n : ℝ) * p14ExpSum x)
          (fun t => (u t) ^ 2) l)
    · have hvalid_lim :
          Filter.Tendsto (fun t => (((n - 1 : ℕ) : ℝ) * u t)) l (nhds 0) := by
          simpa using hu.const_mul (((n - 1 : ℕ) : ℝ))
      have hsmall_lim :
          Filter.Tendsto
            (fun t => (n : ℝ) * (((n - 1 : ℕ) : ℝ) * u t)) l
            (nhds 0) := by
          simpa [mul_assoc] using
            hu.const_mul ((n : ℝ) * ((n - 1 : ℕ) : ℝ))
      have hvalid_ev :
          ∀ᶠ t in l, (((n - 1 : ℕ) : ℝ) * u t) < 1 :=
        (tendsto_order.1 hvalid_lim).2 1 (by norm_num)
      have hsmall_ev :
          ∀ᶠ t in l,
            (n : ℝ) * (((n - 1 : ℕ) : ℝ) * u t) ≤ 1 :=
        ((tendsto_order.1 hsmall_lim).2 1 (by norm_num)).mono
          (fun _ ht => ht.le)
      filter_upwards [hvalid_ev, hsmall_ev] with t hvalid hsmall
      have hu_nonneg : 0 ≤ u t := by
        rw [← (run t).unit_eq]
        exact (run t).fp.u_nonneg
      let fp := p14FPModelOfStandardAddModel (run t).fp
      have hfp_u : fp.u = u t := by
        dsimp [fp, p14FPModelOfStandardAddModel]
        exact (run t).unit_eq
      have hgamma_valid : NumStability.gammaValid fp (n - 1) := by
        unfold NumStability.gammaValid
        rw [hfp_u]
        exact hvalid
      have hgamma_le :
          NumStability.gamma fp (n - 1) ≤ (n : ℝ) * u t := by
        have h := NumStability.gamma_pred_le_n_mul_u_of_n_mul_pred_u_le_one
          fp hn hgamma_valid (by simpa [hfp_u] using hsmall)
        simpa [hfp_u] using h
      have hsum_round :=
        NumStability.recursiveSum_forward_error_bound fp n
          (p14ComputedExp (run t)) hgamma_valid
      have hrecursive_eq :
          p14RecursiveComputedExpSum (run t) =
            NumStability.fl_recursiveSum fp n (p14ComputedExp (run t)) := by
        unfold p14RecursiveComputedExpSum
        rw [p14_recursiveSum_eq_fl_recursiveSum]
      have hcomputed_abs :
          ∑ i : Fin n, |p14ComputedExp (run t) i| ≤
            (1 + u t) * p14ExpSum x := by
        unfold p14ExpSum
        calc
          ∑ i : Fin n, |p14ComputedExp (run t) i|
              ≤ ∑ i : Fin n, (1 + u t) * Real.exp (x i) := by
                apply Finset.sum_le_sum
                intro i _
                rw [p14ComputedExp, abs_mul, abs_of_pos (Real.exp_pos (x i))]
                have hfactor :
                    |1 + (run t).expError i| ≤ 1 + u t := by
                  calc
                    |1 + (run t).expError i|
                        ≤ |(1 : ℝ)| + |(run t).expError i| := abs_add_le _ _
                    _ ≤ 1 + u t := by
                      simpa using add_le_add_left ((run t).expError_le i) 1
                nlinarith [Real.exp_pos (x i)]
          _ = (1 + u t) * ∑ i : Fin n, Real.exp (x i) := by
                rw [Finset.mul_sum]
      have hinput_error :
          |∑ i : Fin n, p14ComputedExp (run t) i -
              ∑ i : Fin n, Real.exp (x i)| ≤
            u t * p14ExpSum x := by
        unfold p14ExpSum
        rw [← Finset.sum_sub_distrib]
        calc
          |∑ i : Fin n,
              (p14ComputedExp (run t) i - Real.exp (x i))|
              ≤ ∑ i : Fin n,
                |p14ComputedExp (run t) i - Real.exp (x i)| :=
                  Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i : Fin n, u t * Real.exp (x i) := by
                exact Finset.sum_le_sum (fun i _ => hexp_error t i)
          _ = u t * ∑ i : Fin n, Real.exp (x i) := by
                rw [Finset.mul_sum]
      have hround_error :
          |p14RecursiveComputedExpSum (run t) -
              ∑ i : Fin n, p14ComputedExp (run t) i| ≤
            (n : ℝ) * u t * (1 + u t) * p14ExpSum x := by
        rw [hrecursive_eq]
        calc
          |NumStability.fl_recursiveSum fp n (p14ComputedExp (run t)) -
              ∑ i : Fin n, p14ComputedExp (run t) i|
              ≤ NumStability.gamma fp (n - 1) *
                  ∑ i : Fin n, |p14ComputedExp (run t) i| := hsum_round
          _ ≤ ((n : ℝ) * u t) *
                ∑ i : Fin n, |p14ComputedExp (run t) i| := by
                  exact mul_le_mul_of_nonneg_right hgamma_le (Finset.sum_nonneg
                    (fun i _ => abs_nonneg _))
          _ ≤ ((n : ℝ) * u t) * ((1 + u t) * p14ExpSum x) := by
                  exact mul_le_mul_of_nonneg_left hcomputed_abs
                    (mul_nonneg (Nat.cast_nonneg n) hu_nonneg)
          _ = (n : ℝ) * u t * (1 + u t) * p14ExpSum x := by ring
      have htotal :
          |p14BasicSumDelta (run t)| ≤
            u t * p14ExpSum x +
              (n : ℝ) * u t * (1 + u t) * p14ExpSum x := by
        unfold p14BasicSumDelta p14ExpSum
        calc
          |p14RecursiveComputedExpSum (run t) -
              ∑ i : Fin n, Real.exp (x i)|
              ≤ |p14RecursiveComputedExpSum (run t) -
                    ∑ i : Fin n, p14ComputedExp (run t) i| +
                  |∑ i : Fin n, p14ComputedExp (run t) i -
                    ∑ i : Fin n, Real.exp (x i)| := by
                      convert abs_add_le
                        (p14RecursiveComputedExpSum (run t) -
                          ∑ i : Fin n, p14ComputedExp (run t) i)
                        (∑ i : Fin n, p14ComputedExp (run t) i -
                          ∑ i : Fin n, Real.exp (x i)) using 1 <;> ring
          _ ≤ (n : ℝ) * u t * (1 + u t) *
                    ∑ i : Fin n, Real.exp (x i) +
                  u t * ∑ i : Fin n, Real.exp (x i) :=
                    add_le_add hround_error hinput_error
          _ = u t * ∑ i : Fin n, Real.exp (x i) +
                (n : ℝ) * u t * (1 + u t) *
                  ∑ i : Fin n, Real.exp (x i) := by ring
      calc
        |p14BasicSumDelta (run t)|
            ≤ u t * p14ExpSum x +
                (n : ℝ) * u t * (1 + u t) * p14ExpSum x := htotal
        _ = (n + 1 : ℝ) * u t * p14ExpSum x + |R t| := by
          have hR_nonneg : 0 ≤ R t := by
            dsimp [R]
            positivity
          rw [abs_of_nonneg hR_nonneg]
          dsimp [R]
          push_cast
          ring
  · intro t
    unfold p14BasicSumDelta
    ring

end HighamBench
