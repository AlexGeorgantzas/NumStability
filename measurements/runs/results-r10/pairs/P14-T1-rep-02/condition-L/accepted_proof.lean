import HighamBench.P14Definitions
import NumStability.Algorithms.Summation.Recursive.Core

namespace HighamBench

open scoped BigOperators

noncomputable def p14StandardAddModelToFP (fp : StandardAddModel) :
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

lemma p14_recursiveSum_eq_library_recursiveSum (fp : StandardAddModel) :
    ∀ (m : ℕ) (v : Fin m → ℝ),
      recursiveSum fp.fl_add m v =
        NumStability.fl_recursiveSum (p14StandardAddModelToFP fp) m v
  | 0, v => by
      simp [recursiveSum, NumStability.fl_recursiveSum]
  | m + 1, v => by
      by_cases hm : m = 0
      · subst m
        simp only [recursiveSum, if_pos, NumStability.fl_recursiveSum]
        rw [Fin.foldl_succ_last]
        simp [p14StandardAddModelToFP, fp.fl_add_zero]
      · rw [recursiveSum]
        simp only [hm, dite_false]
        rw [NumStability.fl_recursiveSum, Fin.foldl_succ_last]
        change fp.fl_add (recursiveSum fp.fl_add m fun i => v i.castSucc)
            (v (Fin.last m)) =
          fp.fl_add
            (NumStability.fl_recursiveSum (p14StandardAddModelToFP fp) m
              fun i => v i.castSucc)
            (v (Fin.last m))
        rw [p14_recursiveSum_eq_library_recursiveSum fp m]

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
    apply Finset.sum_pos
    · intro i _
      exact Real.exp_pos _
    · exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hu_nonneg : ∀ t, 0 ≤ u t := by
    intro t
    rw [← (run t).unit_eq]
    exact (run t).fp.u_nonneg
  have hexpError : ∀ t i,
      |p14ComputedExp (run t) i - Real.exp (x i)| ≤
        u t * Real.exp (x i) := by
    intro t i
    rw [p14ComputedExp]
    have hi := (run t).expError_le i
    have he : 0 ≤ Real.exp (x i) := (Real.exp_pos _).le
    rw [show Real.exp (x i) * (1 + (run t).expError i) - Real.exp (x i) =
      Real.exp (x i) * (run t).expError i by ring, abs_mul,
      abs_of_nonneg he]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hi he
  refine ⟨hexact_pos, hexpError, ?_, ?_⟩
  · let remainder : ι → ℝ := fun t =>
      (n : ℝ) * p14ExpSum x * (u t) ^ 2
    refine ⟨remainder, ?_, ?_⟩
    · simpa only [remainder] using
        (Asymptotics.isBigO_refl (fun t => (u t) ^ 2) l).const_mul_left
          ((n : ℝ) * p14ExpSum x)
    · have hvalidEventually : ∀ᶠ t in l,
          (((n - 1 : ℕ) : ℝ) * u t) < 1 := by
        have ht := hu.const_mul (((n - 1 : ℕ) : ℝ))
        exact Filter.Tendsto.eventually_lt_const (by norm_num) ht
      have hsmallEventually : ∀ᶠ t in l,
          (n : ℝ) * (((n - 1 : ℕ) : ℝ) * u t) ≤ 1 := by
        have ht := hu.const_mul
          ((n : ℝ) * ((n - 1 : ℕ) : ℝ))
        have hevent : ∀ᶠ t in l,
            (n : ℝ) * ((n - 1 : ℕ) : ℝ) * u t < 1 :=
          Filter.Tendsto.eventually_lt_const (by norm_num) ht
        filter_upwards [hevent] with t ht'
        simpa only [mul_assoc] using ht'.le
      filter_upwards [hvalidEventually, hsmallEventually] with t hvalid hsmall
      let fp : NumStability.FPModel := p14StandardAddModelToFP (run t).fp
      have hfp_u : fp.u = u t := by
        simpa [fp, p14StandardAddModelToFP] using (run t).unit_eq
      have hgammaValid : NumStability.gammaValid fp (n - 1) := by
        unfold NumStability.gammaValid
        rwa [hfp_u]
      have hgamma : NumStability.gamma fp (n - 1) ≤ (n : ℝ) * u t := by
        have hg := NumStability.gamma_pred_le_n_mul_u_of_n_mul_pred_u_le_one
          fp hn hgammaValid (by simpa only [hfp_u] using hsmall)
        simpa only [hfp_u] using hg
      have hcomputedAbs :
          ∑ i : Fin n, |p14ComputedExp (run t) i| ≤
            (1 + u t) * p14ExpSum x := by
        calc
          ∑ i : Fin n, |p14ComputedExp (run t) i| ≤
              ∑ i : Fin n,
                (1 + u t) * Real.exp (x i) := by
            apply Finset.sum_le_sum
            intro i _
            calc
              |p14ComputedExp (run t) i| ≤
                  |p14ComputedExp (run t) i - Real.exp (x i)| +
                    |Real.exp (x i)| := by
                calc
                  |p14ComputedExp (run t) i| =
                      |(p14ComputedExp (run t) i - Real.exp (x i)) +
                        Real.exp (x i)| := by ring_nf
                  _ ≤ _ := abs_add_le _ _
              _ ≤ u t * Real.exp (x i) + |Real.exp (x i)| :=
                add_le_add (hexpError t i) le_rfl
              _ = u t * Real.exp (x i) + Real.exp (x i) := by
                rw [abs_of_pos (Real.exp_pos _)]
              _ = (1 + u t) * Real.exp (x i) := by ring
          _ = (1 + u t) * p14ExpSum x := by
            simp [p14ExpSum, Finset.mul_sum]
      have hexpSumError :
          |p14ExactComputedExpSum (run t) - p14ExpSum x| ≤
            u t * p14ExpSum x := by
        rw [p14ExactComputedExpSum, p14ExpSum, ← Finset.sum_sub_distrib]
        calc
          |∑ i : Fin n,
              (p14ComputedExp (run t) i - Real.exp (x i))| ≤
              ∑ i : Fin n,
                |p14ComputedExp (run t) i - Real.exp (x i)| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i : Fin n, u t * Real.exp (x i) := by
            exact Finset.sum_le_sum fun i _ => hexpError t i
          _ = u t * ∑ i : Fin n, Real.exp (x i) := by
            rw [Finset.mul_sum]
      have hrecursiveError :
          |p14RecursiveComputedExpSum (run t) -
              p14ExactComputedExpSum (run t)| ≤
            NumStability.gamma fp (n - 1) *
              ∑ i : Fin n, |p14ComputedExp (run t) i| := by
        rw [p14RecursiveComputedExpSum,
          p14_recursiveSum_eq_library_recursiveSum]
        exact NumStability.recursiveSum_forward_error_bound fp n
          (p14ComputedExp (run t)) hgammaValid
      have hgamma_nonneg : 0 ≤ NumStability.gamma fp (n - 1) :=
        NumStability.gamma_nonneg fp hgammaValid
      have hfactor_nonneg :
          0 ≤ (1 + u t) * p14ExpSum x :=
        mul_nonneg (by linarith [hu_nonneg t]) hexact_pos.le
      have htotal :
          |p14BasicSumDelta (run t)| ≤
            ((n : ℝ) * u t) * ((1 + u t) * p14ExpSum x) +
              u t * p14ExpSum x := by
        unfold p14BasicSumDelta
        calc
          |p14RecursiveComputedExpSum (run t) - p14ExpSum x| ≤
              |p14RecursiveComputedExpSum (run t) -
                  p14ExactComputedExpSum (run t)| +
                |p14ExactComputedExpSum (run t) - p14ExpSum x| := by
            have heq :
                p14RecursiveComputedExpSum (run t) - p14ExpSum x =
                  (p14RecursiveComputedExpSum (run t) -
                    p14ExactComputedExpSum (run t)) +
                  (p14ExactComputedExpSum (run t) - p14ExpSum x) := by ring
            rw [heq]
            exact abs_add_le _ _
          _ ≤ NumStability.gamma fp (n - 1) *
                  (∑ i : Fin n, |p14ComputedExp (run t) i|) +
                u t * p14ExpSum x := add_le_add hrecursiveError hexpSumError
          _ ≤ NumStability.gamma fp (n - 1) *
                  ((1 + u t) * p14ExpSum x) +
                u t * p14ExpSum x := by
            gcongr
          _ ≤ ((n : ℝ) * u t) *
                  ((1 + u t) * p14ExpSum x) +
                u t * p14ExpSum x := by
            gcongr
      calc
        |p14BasicSumDelta (run t)| ≤
            ((n : ℝ) * u t) * ((1 + u t) * p14ExpSum x) +
              u t * p14ExpSum x := htotal
        _ = (n + 1 : ℝ) * u t * p14ExpSum x + |remainder t| := by
          rw [show |remainder t| = remainder t by
            apply abs_of_nonneg
            exact mul_nonneg
              (mul_nonneg (Nat.cast_nonneg _) hexact_pos.le) (sq_nonneg _)]
          simp only [remainder, Nat.cast_add, Nat.cast_one]
          ring
  · intro t
    unfold p14BasicSumDelta
    ring

end HighamBench
