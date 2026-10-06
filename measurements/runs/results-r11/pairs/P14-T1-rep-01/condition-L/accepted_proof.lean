import HighamBench.P14Definitions
import NumStability.Algorithms.Summation.Recursive.Core

namespace HighamBench

open scoped BigOperators

noncomputable def p14StandardAddFPModel (fp : StandardAddModel) :
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
    refine ⟨0, ?_, by ring⟩
    simpa using fp.u_nonneg
  model_mul := by
    intro a b
    refine ⟨0, ?_, by ring⟩
    simpa using fp.u_nonneg
  model_div := by
    intro a b _
    refine ⟨0, ?_, by ring⟩
    simpa using fp.u_nonneg
  model_sqrt := by
    intro a _
    refine ⟨0, ?_, by ring⟩
    simpa using fp.u_nonneg

lemma p14_recursiveSum_eq_fl_recursiveSum (fp : StandardAddModel) :
    ∀ (m : ℕ) (v : Fin m → ℝ),
      recursiveSum fp.fl_add m v =
        NumStability.fl_recursiveSum (p14StandardAddFPModel fp) m v := by
  intro m
  induction m with
  | zero =>
      intro v
      simp [recursiveSum, NumStability.fl_recursiveSum]
  | succ m ih =>
      intro v
      have hfold :
          NumStability.fl_recursiveSum (p14StandardAddFPModel fp) (m + 1) v =
            fp.fl_add
              (NumStability.fl_recursiveSum (p14StandardAddFPModel fp) m
                (fun i => v i.castSucc))
              (v (Fin.last m)) :=
        Fin.foldl_succ_last _ _
      rw [hfold]
      simp only [recursiveSum]
      split_ifs with hm
      · subst m
        simp [NumStability.fl_recursiveSum, p14StandardAddFPModel,
          fp.fl_add_zero]
      · rw [ih]

lemma p14_computedExp_error_le
    {n : ℕ} {x : Fin n → ℝ} {u : ℝ}
    (run : P14BasicSumExecution x u) (i : Fin n) :
    |p14ComputedExp run i - Real.exp (x i)| ≤ u * Real.exp (x i) := by
  calc
    |p14ComputedExp run i - Real.exp (x i)| =
        Real.exp (x i) * |run.expError i| := by
          simp only [p14ComputedExp]
          have hrewrite :
              Real.exp (x i) * (1 + run.expError i) - Real.exp (x i) =
                Real.exp (x i) * run.expError i := by ring
          rw [hrewrite]
          rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.exp (x i) * u :=
      mul_le_mul_of_nonneg_left (run.expError_le i) (Real.exp_pos _).le
    _ = u * Real.exp (x i) := by ring

lemma p14_basicSumDelta_bound
    {n : ℕ} (hn : 0 < n) {x : Fin n → ℝ} {u : ℝ}
    (run : P14BasicSumExecution x u)
    (hvalid : (((n - 1 : ℕ) : ℝ) * u) < 1)
    (hsmall : (n : ℝ) * (((n - 1 : ℕ) : ℝ) * u) ≤ 1) :
    |p14BasicSumDelta run| ≤
      (n + 1 : ℝ) * u * p14ExpSum x +
        (n : ℝ) * p14ExpSum x * u ^ 2 := by
  let fp := p14StandardAddFPModel run.fp
  have hfp_u : fp.u = u := run.unit_eq
  have hu : 0 ≤ u := by
    rw [← hfp_u]
    exact fp.u_nonneg
  have hgammaValid : NumStability.gammaValid fp (n - 1) := by
    simpa [NumStability.gammaValid, hfp_u] using hvalid
  have hrecursive :
      |p14RecursiveComputedExpSum run - p14ExactComputedExpSum run| ≤
        NumStability.gamma fp (n - 1) *
          ∑ i : Fin n, |p14ComputedExp run i| := by
    simpa [p14RecursiveComputedExpSum, p14ExactComputedExpSum, fp,
      p14StandardAddFPModel, p14_recursiveSum_eq_fl_recursiveSum] using
      (NumStability.recursiveSum_forward_error_bound fp n
        (p14ComputedExp run) hgammaValid)
  have hcomputed_abs :
      (∑ i : Fin n, |p14ComputedExp run i|) ≤
        (1 + u) * p14ExpSum x := by
    calc
      (∑ i : Fin n, |p14ComputedExp run i|) ≤
          ∑ i : Fin n, Real.exp (x i) * (1 + u) := by
            apply Finset.sum_le_sum
            intro i _
            have hone : |1 + run.expError i| ≤ 1 + u := by
              calc
                |1 + run.expError i| ≤ |(1 : ℝ)| + |run.expError i| :=
                  abs_add_le _ _
                _ ≤ 1 + u := by
                  simpa using add_le_add_left (run.expError_le i) 1
            simp only [p14ComputedExp, abs_mul, abs_of_pos (Real.exp_pos _)]
            exact mul_le_mul_of_nonneg_left hone (Real.exp_pos _).le
      _ = (∑ i : Fin n, Real.exp (x i)) * (1 + u) :=
        by rw [Finset.sum_mul]
      _ = (1 + u) * p14ExpSum x := by
        rw [p14ExpSum]
        ring
  have hexp_error :
      |p14ExactComputedExpSum run - p14ExpSum x| ≤ u * p14ExpSum x := by
    calc
      |p14ExactComputedExpSum run - p14ExpSum x| =
          |∑ i : Fin n, (p14ComputedExp run i - Real.exp (x i))| := by
            simp only [p14ExactComputedExpSum, p14ExpSum,
              Finset.sum_sub_distrib]
      _ ≤ ∑ i : Fin n,
          |p14ComputedExp run i - Real.exp (x i)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin n, u * Real.exp (x i) := by
            exact Finset.sum_le_sum fun i _ => p14_computedExp_error_le run i
      _ = u * p14ExpSum x := by
            simp [p14ExpSum, Finset.mul_sum]
  have hsum_nonneg : 0 ≤ p14ExpSum x := by
    unfold p14ExpSum
    exact Finset.sum_nonneg fun i _ => (Real.exp_pos (x i)).le
  have hfactor_nonneg : 0 ≤ (1 + u) * p14ExpSum x :=
    mul_nonneg (by linarith) hsum_nonneg
  have hgamma_nonneg : 0 ≤ NumStability.gamma fp (n - 1) :=
    NumStability.gamma_nonneg fp hgammaValid
  have hgamma_le :
      NumStability.gamma fp (n - 1) ≤ (n : ℝ) * u := by
    have hs : (n : ℝ) * (((n - 1 : ℕ) : ℝ) * fp.u) ≤ 1 := by
      simpa [hfp_u] using hsmall
    have hg := NumStability.gamma_pred_le_n_mul_u_of_n_mul_pred_u_le_one
      fp hn hgammaValid hs
    simpa [hfp_u] using hg
  calc
    |p14BasicSumDelta run| =
        |(p14RecursiveComputedExpSum run - p14ExactComputedExpSum run) +
          (p14ExactComputedExpSum run - p14ExpSum x)| := by
            simp only [p14BasicSumDelta]
            congr 1
            ring
    _ ≤ |p14RecursiveComputedExpSum run - p14ExactComputedExpSum run| +
          |p14ExactComputedExpSum run - p14ExpSum x| := abs_add_le _ _
    _ ≤ NumStability.gamma fp (n - 1) *
          (∑ i : Fin n, |p14ComputedExp run i|) + u * p14ExpSum x :=
            add_le_add hrecursive hexp_error
    _ ≤ NumStability.gamma fp (n - 1) *
          ((1 + u) * p14ExpSum x) + u * p14ExpSum x :=
            add_le_add
              (mul_le_mul_of_nonneg_left hcomputed_abs hgamma_nonneg) le_rfl
    _ ≤ ((n : ℝ) * u) * ((1 + u) * p14ExpSum x) +
          u * p14ExpSum x :=
            add_le_add
              (mul_le_mul_of_nonneg_right hgamma_le hfactor_nonneg) le_rfl
    _ = (n + 1 : ℝ) * u * p14ExpSum x +
          (n : ℝ) * p14ExpSum x * u ^ 2 := by
            push_cast
            ring

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
    unfold p14ExpSum
    apply Finset.sum_pos'
    · intro i _
      exact (Real.exp_pos (x i)).le
    · let i : Fin n := ⟨0, hn⟩
      exact ⟨i, Finset.mem_univ i, Real.exp_pos (x i)⟩
  refine ⟨hexact_pos, ?_, ?_, ?_⟩
  · exact fun t i => p14_computedExp_error_le (run t) i
  · let remainder : ι → ℝ :=
      fun t => (n : ℝ) * p14ExpSum x * (u t) ^ 2
    refine ⟨remainder, ?_, ?_⟩
    · simpa [remainder] using Asymptotics.isBigO_const_mul_self
        ((n : ℝ) * p14ExpSum x) (fun t => (u t) ^ 2) l
    · let C : ℝ := (n : ℝ) ^ 2 + 1
      have hC : 0 < C := by
        dsimp [C]
        nlinarith [sq_nonneg (n : ℝ)]
      have hevent : ∀ᶠ t in l, dist (u t) 0 < 1 / C :=
        (Metric.tendsto_nhds.1 hu) (1 / C) (one_div_pos.mpr hC)
      filter_upwards [hevent] with t ht
      have hut : 0 ≤ u t := by
        rw [← (run t).unit_eq]
        exact (run t).fp.u_nonneg
      have hut_lt : u t < 1 / C := by
        simpa [Real.dist_eq, abs_of_nonneg hut] using ht
      have hn_cast : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hk_cast : (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by positivity
      have hk_le : (((n - 1 : ℕ) : ℝ)) ≤ (n : ℝ) := by
        exact_mod_cast Nat.sub_le n 1
      have hsq_pos : 0 < (n : ℝ) ^ 2 := sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hn_cast)
      have hfrac : (n : ℝ) ^ 2 / C < 1 := by
        apply (div_lt_one hC).2
        dsimp [C]
        linarith
      have hsmall_strict :
          (n : ℝ) * (((n - 1 : ℕ) : ℝ) * u t) < 1 := by
        calc
          (n : ℝ) * (((n - 1 : ℕ) : ℝ) * u t) =
              ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) * u t := by ring
          _ ≤ (n : ℝ) ^ 2 * u t := by
            have hcoef :
                (n : ℝ) * ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
              rw [pow_two]
              exact mul_le_mul_of_nonneg_left hk_le
                (show (0 : ℝ) ≤ (n : ℝ) by positivity)
            exact mul_le_mul_of_nonneg_right hcoef hut
          _ < (n : ℝ) ^ 2 * (1 / C) :=
            mul_lt_mul_of_pos_left hut_lt hsq_pos
          _ = (n : ℝ) ^ 2 / C := by ring
          _ < 1 := hfrac
      have hvalid : (((n - 1 : ℕ) : ℝ) * u t) < 1 := by
        calc
          (((n - 1 : ℕ) : ℝ) * u t) ≤
              (n : ℝ) * (((n - 1 : ℕ) : ℝ) * u t) := by
                exact le_mul_of_one_le_left (mul_nonneg hk_cast hut) hn_cast
          _ < 1 := hsmall_strict
      have hbound := p14_basicSumDelta_bound hn (run t) hvalid hsmall_strict.le
      have hrem_nonneg : 0 ≤ remainder t := by
        dsimp [remainder]
        exact mul_nonneg
          (mul_nonneg (by positivity) hexact_pos.le) (sq_nonneg (u t))
      rw [abs_of_nonneg hrem_nonneg]
      simpa [remainder] using hbound
  · intro t
    simp only [p14BasicSumDelta]
    ring

end HighamBench
