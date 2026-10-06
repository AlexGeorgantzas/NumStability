import HighamBench.P14Definitions
import NumStability.Algorithms.Summation.Recursive.Core

namespace HighamBench

open scoped BigOperators

noncomputable def p14StandardAddModelToFPModel
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
    ∀ (m : ℕ) (v : Fin m → ℝ),
      recursiveSum fp.fl_add m v =
        NumStability.fl_recursiveSum (p14StandardAddModelToFPModel fp) m v := by
  intro m
  induction m with
  | zero =>
      intro v
      simp [recursiveSum, NumStability.fl_recursiveSum]
  | succ m ih =>
      intro v
      rw [show NumStability.fl_recursiveSum
          (p14StandardAddModelToFPModel fp) (m + 1) v =
            fp.fl_add
              (NumStability.fl_recursiveSum
                (p14StandardAddModelToFPModel fp) m
                (fun i : Fin m => v i.castSucc))
              (v (Fin.last m)) by
            exact Fin.foldl_succ_last _ _]
      rw [← ih]
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
  have hsum_pos : 0 < p14ExpSum x := by
    unfold p14ExpSum
    refine Finset.sum_pos' (fun i _ => (Real.exp_pos (x i)).le) ?_
    let i : Fin n := ⟨0, hn⟩
    exact ⟨i, Finset.mem_univ i, Real.exp_pos (x i)⟩
  refine ⟨hsum_pos, ?_, ?_, ?_⟩
  · intro t i
    rw [p14ComputedExp]
    have herr := (run t).expError_le i
    have hexp : 0 < Real.exp (x i) := Real.exp_pos _
    calc
      |Real.exp (x i) * (1 + (run t).expError i) - Real.exp (x i)| =
          Real.exp (x i) * |(run t).expError i| := by
            rw [show Real.exp (x i) * (1 + (run t).expError i) -
                Real.exp (x i) = Real.exp (x i) * (run t).expError i by ring,
              abs_mul, abs_of_pos hexp]
      _ ≤ Real.exp (x i) * u t :=
        mul_le_mul_of_nonneg_left herr hexp.le
      _ = u t * Real.exp (x i) := by ring
  · let remainder : ι → ℝ :=
      fun t => (n : ℝ) * (u t) ^ 2 * p14ExpSum x
    refine ⟨remainder, ?_, ?_⟩
    · have hsq := Asymptotics.isBigO_refl (fun t => (u t) ^ 2) l
      have hscaled := hsq.const_mul_left ((n : ℝ) * p14ExpSum x)
      simpa only [remainder, mul_comm, mul_left_comm, mul_assoc] using hscaled
    · let c : ℝ := (n : ℝ) * ((n - 1 : ℕ) : ℝ)
      have hcu : Filter.Tendsto (fun t => c * u t) l (nhds 0) := by
        convert tendsto_const_nhds.mul hu using 1 <;> simp
      have hevent : ∀ᶠ t in l, c * u t < 1 :=
        hcu (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
      filter_upwards [hevent] with t ht
      let fp := p14StandardAddModelToFPModel (run t).fp
      have hu_nonneg : 0 ≤ u t := by
        rw [← (run t).unit_eq]
        exact (run t).fp.u_nonneg
      have hsmall :
          (n : ℝ) * (((n - 1 : ℕ) : ℝ) * fp.u) ≤ 1 := by
        change (n : ℝ) * (((n - 1 : ℕ) : ℝ) * (run t).fp.u) ≤ 1
        rw [(run t).unit_eq]
        exact le_of_lt (by simpa only [c, mul_assoc] using ht)
      have hvalid : NumStability.gammaValid fp (n - 1) := by
        unfold NumStability.gammaValid
        change ((n - 1 : ℕ) : ℝ) * (run t).fp.u < 1
        rw [(run t).unit_eq]
        have hn_real : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have hk_nonneg : 0 ≤ ((n - 1 : ℕ) : ℝ) := by positivity
        have hku_nonneg :
            0 ≤ ((n - 1 : ℕ) : ℝ) * u t :=
          mul_nonneg hk_nonneg hu_nonneg
        have hle :
            ((n - 1 : ℕ) : ℝ) * u t ≤
              (n : ℝ) * (((n - 1 : ℕ) : ℝ) * u t) := by
          nlinarith
        exact lt_of_le_of_lt hle (by simpa only [c, mul_assoc] using ht)
      have hgamma :
          NumStability.gamma fp (n - 1) ≤ (n : ℝ) * u t := by
        have h := NumStability.gamma_pred_le_n_mul_u_of_n_mul_pred_u_le_one
          fp hn hvalid hsmall
        simpa [fp, p14StandardAddModelToFPModel, (run t).unit_eq] using h
      have hgamma_nonneg : 0 ≤ NumStability.gamma fp (n - 1) :=
        NumStability.gamma_nonneg fp hvalid
      have hexp_error :
          |p14ExactComputedExpSum (run t) - p14ExpSum x| ≤
            u t * p14ExpSum x := by
        unfold p14ExactComputedExpSum p14ExpSum
        rw [← Finset.sum_sub_distrib]
        calc
          |∑ i, (p14ComputedExp (run t) i - Real.exp (x i))| ≤
              ∑ i, |p14ComputedExp (run t) i - Real.exp (x i)| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i, u t * Real.exp (x i) := by
            exact Finset.sum_le_sum (fun i _ => by
              rw [p14ComputedExp]
              have herr := (run t).expError_le i
              have hexp : 0 < Real.exp (x i) := Real.exp_pos _
              calc
                |Real.exp (x i) * (1 + (run t).expError i) -
                    Real.exp (x i)| =
                    Real.exp (x i) * |(run t).expError i| := by
                      rw [show Real.exp (x i) * (1 + (run t).expError i) -
                          Real.exp (x i) =
                            Real.exp (x i) * (run t).expError i by ring,
                        abs_mul, abs_of_pos hexp]
                _ ≤ Real.exp (x i) * u t :=
                  mul_le_mul_of_nonneg_left herr hexp.le
                _ = u t * Real.exp (x i) := by ring)
          _ = u t * ∑ i, Real.exp (x i) := by rw [Finset.mul_sum]
      have hcomputed_abs :
          (∑ i : Fin n, |p14ComputedExp (run t) i|) ≤
            (1 + u t) * p14ExpSum x := by
        unfold p14ExpSum
        calc
          (∑ i : Fin n, |p14ComputedExp (run t) i|) ≤
              ∑ i : Fin n, (1 + u t) * Real.exp (x i) := by
            exact Finset.sum_le_sum (fun i _ => by
              rw [p14ComputedExp, abs_mul, abs_of_pos (Real.exp_pos (x i))]
              have hone : |1 + (run t).expError i| ≤
                  1 + |(run t).expError i| := by
                simpa using abs_add_le (1 : ℝ) ((run t).expError i)
              calc
                Real.exp (x i) * |1 + (run t).expError i| ≤
                    Real.exp (x i) * (1 + |(run t).expError i|) :=
                  mul_le_mul_of_nonneg_left hone (Real.exp_pos _).le
                _ ≤ Real.exp (x i) * (1 + u t) := by
                  gcongr
                  exact (run t).expError_le i
                _ = (1 + u t) * Real.exp (x i) := by ring)
          _ = (1 + u t) * ∑ i : Fin n, Real.exp (x i) := by
            rw [Finset.mul_sum]
      have hadd :
          |p14RecursiveComputedExpSum (run t) -
              p14ExactComputedExpSum (run t)| ≤
            NumStability.gamma fp (n - 1) *
              ∑ i : Fin n, |p14ComputedExp (run t) i| := by
        rw [p14RecursiveComputedExpSum, p14ExactComputedExpSum,
          p14_recursiveSum_eq_fl_recursiveSum]
        exact NumStability.recursiveSum_forward_error_bound
          fp n (p14ComputedExp (run t)) hvalid
      have hsum_nonneg : 0 ≤ p14ExpSum x := hsum_pos.le
      have hfactor_nonneg : 0 ≤ (1 + u t) * p14ExpSum x := by positivity
      have htotal :
          |p14RecursiveComputedExpSum (run t) - p14ExpSum x| ≤
            ((n : ℝ) * u t) * ((1 + u t) * p14ExpSum x) +
              u t * p14ExpSum x := by
        calc
          |p14RecursiveComputedExpSum (run t) - p14ExpSum x| ≤
              |p14RecursiveComputedExpSum (run t) -
                  p14ExactComputedExpSum (run t)| +
                |p14ExactComputedExpSum (run t) - p14ExpSum x| := by
            have htri := abs_add_le
              (p14RecursiveComputedExpSum (run t) -
                p14ExactComputedExpSum (run t))
              (p14ExactComputedExpSum (run t) - p14ExpSum x)
            convert htri using 1 <;> ring
          _ ≤ NumStability.gamma fp (n - 1) *
                  (∑ i : Fin n, |p14ComputedExp (run t) i|) +
                u t * p14ExpSum x := add_le_add hadd hexp_error
          _ ≤ NumStability.gamma fp (n - 1) *
                  ((1 + u t) * p14ExpSum x) +
                u t * p14ExpSum x := by
            gcongr
          _ ≤ ((n : ℝ) * u t) *
                  ((1 + u t) * p14ExpSum x) +
                u t * p14ExpSum x := by
            gcongr
      rw [p14BasicSumDelta]
      change |p14RecursiveComputedExpSum (run t) - p14ExpSum x| ≤ _
      calc
        |p14RecursiveComputedExpSum (run t) - p14ExpSum x| ≤
            ((n : ℝ) * u t) * ((1 + u t) * p14ExpSum x) +
              u t * p14ExpSum x := htotal
        _ = (n + 1 : ℝ) * u t * p14ExpSum x + |remainder t| := by
          rw [show |remainder t| = remainder t by
            apply abs_of_nonneg
            dsimp [remainder]
            positivity]
          dsimp [remainder]
          push_cast
          ring
  · intro t
    unfold p14BasicSumDelta
    ring

end HighamBench
