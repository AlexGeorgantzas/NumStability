import HighamBench.P14Definitions
import NumStability.Algorithms.Summation.Recursive.Core

namespace HighamBench

open scoped BigOperators

noncomputable def p14AsFPModel (fp : StandardAddModel) :
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

lemma p14_recursiveSum_eq_library (fp : StandardAddModel) :
    ∀ (m : ℕ) (v : Fin m → ℝ),
      recursiveSum fp.fl_add m v =
        NumStability.fl_recursiveSum (p14AsFPModel fp) m v
  | 0, v => by
      simp [recursiveSum, NumStability.fl_recursiveSum]
  | m + 1, v => by
      rw [NumStability.fl_recursiveSum, Fin.foldl_succ_last]
      change recursiveSum fp.fl_add (m + 1) v =
        fp.fl_add
          (NumStability.fl_recursiveSum (p14AsFPModel fp) m
            (fun i : Fin m => v i.castSucc))
          (v (Fin.last m))
      rw [← p14_recursiveSum_eq_library fp m (fun i : Fin m => v i.castSucc)]
      simp only [recursiveSum]
      split_ifs with h
      · subst m
        change v 0 = fp.fl_add 0 (v 0)
        rw [fp.fl_add_zero]
      · rfl

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
  have hu_nonneg : ∀ t, 0 ≤ u t := by
    intro t
    have h := (run t).fp.u_nonneg
    simpa [(run t).unit_eq] using h
  have hexact_pos : 0 < p14ExpSum x := by
    unfold p14ExpSum
    apply Finset.sum_pos
    · intro i _
      exact Real.exp_pos _
    · exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hexpError : ∀ t i,
      |p14ComputedExp (run t) i - Real.exp (x i)| ≤
        u t * Real.exp (x i) := by
    intro t i
    rw [p14ComputedExp]
    have he : 0 ≤ Real.exp (x i) := (Real.exp_pos _).le
    calc
      |Real.exp (x i) * (1 + (run t).expError i) - Real.exp (x i)| =
          Real.exp (x i) * |(run t).expError i| := by
            rw [show Real.exp (x i) * (1 + (run t).expError i) -
                Real.exp (x i) = Real.exp (x i) * (run t).expError i by ring,
              abs_mul, abs_of_nonneg he]
      _ ≤ Real.exp (x i) * u t :=
        mul_le_mul_of_nonneg_left ((run t).expError_le i) he
      _ = u t * Real.exp (x i) := by ring
  have hcomputed_abs : ∀ t,
      ∑ i : Fin n, |p14ComputedExp (run t) i| ≤
        (1 + u t) * p14ExpSum x := by
    intro t
    unfold p14ExpSum
    calc
      ∑ i : Fin n, |p14ComputedExp (run t) i| ≤
          ∑ i : Fin n, (1 + u t) * Real.exp (x i) := by
        apply Finset.sum_le_sum
        intro i _
        calc
          |p14ComputedExp (run t) i| =
              |(p14ComputedExp (run t) i - Real.exp (x i)) +
                Real.exp (x i)| := by ring_nf
          _ ≤ |p14ComputedExp (run t) i - Real.exp (x i)| +
                |Real.exp (x i)| := abs_add_le _ _
          _ ≤ u t * Real.exp (x i) + Real.exp (x i) := by
            gcongr
            · exact hexpError t i
            · rw [abs_of_pos (Real.exp_pos _)]
          _ = (1 + u t) * Real.exp (x i) := by ring
      _ = (1 + u t) * ∑ i : Fin n, Real.exp (x i) := by
        rw [Finset.mul_sum]
  have hinput_sum : ∀ t,
      |p14ExactComputedExpSum (run t) - p14ExpSum x| ≤
        u t * p14ExpSum x := by
    intro t
    unfold p14ExactComputedExpSum p14ExpSum
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ i : Fin n, (p14ComputedExp (run t) i - Real.exp (x i))| ≤
          ∑ i : Fin n,
            |p14ComputedExp (run t) i - Real.exp (x i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin n, u t * Real.exp (x i) := by
        exact Finset.sum_le_sum (fun i _ => hexpError t i)
      _ = u t * ∑ i : Fin n, Real.exp (x i) := by
        rw [Finset.mul_sum]
  let remainder : ι → ℝ := fun t =>
    p14ExpSum x *
      ((((n - 1 : ℕ) : ℝ) * (n : ℝ) * (u t) ^ 2) /
        (1 - ((n - 1 : ℕ) : ℝ) * u t))
  have hden_tendsto : Filter.Tendsto
      (fun t => (1 - ((n - 1 : ℕ) : ℝ) * u t)⁻¹) l (nhds 1) := by
    have hbase : Filter.Tendsto
        (fun t => 1 - ((n - 1 : ℕ) : ℝ) * u t) l (nhds 1) := by
      convert (hu.const_mul (((n - 1 : ℕ) : ℝ))).const_sub 1 using 1 <;> ring
    simpa using hbase.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hrem : remainder =O[l] (fun t => (u t) ^ 2) := by
    have hinv :
        (fun t => (1 - ((n - 1 : ℕ) : ℝ) * u t)⁻¹) =O[l]
          (fun _ : ι => (1 : ℝ)) := hden_tendsto.isBigO_one ℝ
    have hsq : (fun t => (u t) ^ 2) =O[l] (fun t => (u t) ^ 2) :=
      Asymptotics.isBigO_refl _ _
    have hprod := hsq.mul hinv
    have hconst := hprod.const_mul_left
      (p14ExpSum x * (((n - 1 : ℕ) : ℝ) * (n : ℝ)))
    simpa [remainder, div_eq_mul_inv, mul_assoc] using hconst
  have hsmall : ∀ᶠ t in l,
      ((n - 1 : ℕ) : ℝ) * u t < 1 / 2 := by
    have hzero : Filter.Tendsto
        (fun t => ((n - 1 : ℕ) : ℝ) * u t) l (nhds 0) := by
      convert hu.const_mul (((n - 1 : ℕ) : ℝ)) using 1 <;> ring
    exact hzero.eventually_lt_const (by norm_num)
  refine ⟨hexact_pos, hexpError, ⟨remainder, hrem, ?_⟩, ?_⟩
  · filter_upwards [hsmall] with t ht
    have hvalid : NumStability.gammaValid (p14AsFPModel (run t).fp) (n - 1) := by
      unfold NumStability.gammaValid
      simpa [p14AsFPModel, (run t).unit_eq] using (lt_trans ht (by norm_num))
    have hround := NumStability.recursiveSum_forward_error_bound
      (p14AsFPModel (run t).fp) n (p14ComputedExp (run t)) hvalid
    have hround' :
        |p14RecursiveComputedExpSum (run t) -
            p14ExactComputedExpSum (run t)| ≤
          NumStability.gamma (p14AsFPModel (run t).fp) (n - 1) *
            ∑ i : Fin n, |p14ComputedExp (run t) i| := by
      simpa [p14RecursiveComputedExpSum, p14ExactComputedExpSum,
        p14_recursiveSum_eq_library] using hround
    have hgamma_nonneg :
        0 ≤ NumStability.gamma (p14AsFPModel (run t).fp) (n - 1) :=
      NumStability.gamma_nonneg _ hvalid
    have hround'' :
        |p14RecursiveComputedExpSum (run t) -
            p14ExactComputedExpSum (run t)| ≤
          NumStability.gamma (p14AsFPModel (run t).fp) (n - 1) *
            ((1 + u t) * p14ExpSum x) :=
      le_trans hround'
        (mul_le_mul_of_nonneg_left (hcomputed_abs t) hgamma_nonneg)
    have htotal :
        |p14BasicSumDelta (run t)| ≤
          NumStability.gamma (p14AsFPModel (run t).fp) (n - 1) *
              ((1 + u t) * p14ExpSum x) +
            u t * p14ExpSum x := by
      unfold p14BasicSumDelta
      calc
        |p14RecursiveComputedExpSum (run t) - p14ExpSum x| =
            |(p14RecursiveComputedExpSum (run t) -
                p14ExactComputedExpSum (run t)) +
              (p14ExactComputedExpSum (run t) - p14ExpSum x)| := by
                congr 1 <;> ring
        _ ≤ |p14RecursiveComputedExpSum (run t) -
                p14ExactComputedExpSum (run t)| +
              |p14ExactComputedExpSum (run t) - p14ExpSum x| :=
            abs_add_le _ _
        _ ≤ NumStability.gamma (p14AsFPModel (run t).fp) (n - 1) *
                ((1 + u t) * p14ExpSum x) +
              u t * p14ExpSum x := add_le_add hround'' (hinput_sum t)
    have hden : 1 - ((n - 1 : ℕ) : ℝ) * u t ≠ 0 := by
      linarith
    have hncast : (n : ℝ) = ((n - 1 : ℕ) : ℝ) + 1 := by
      norm_cast
      omega
    have hcoeff :
        NumStability.gamma (p14AsFPModel (run t).fp) (n - 1) * (1 + u t) + u t =
          (n : ℝ) * u t +
            (((n - 1 : ℕ) : ℝ) * (n : ℝ) * (u t) ^ 2) /
              (1 - ((n - 1 : ℕ) : ℝ) * u t) := by
      unfold NumStability.gamma
      simp only [p14AsFPModel, (run t).unit_eq]
      rw [hncast]
      field_simp [hden]
      ring
    have hrewrite :
        NumStability.gamma (p14AsFPModel (run t).fp) (n - 1) *
              ((1 + u t) * p14ExpSum x) + u t * p14ExpSum x =
          (n : ℝ) * u t * p14ExpSum x + remainder t := by
      rw [← mul_assoc, ← add_mul, hcoeff]
      simp only [remainder]
      ring
    rw [hrewrite] at htotal
    calc
      |p14BasicSumDelta (run t)| ≤
          (n : ℝ) * u t * p14ExpSum x + remainder t := htotal
      _ ≤ (n + 1 : ℝ) * u t * p14ExpSum x + |remainder t| := by
        have hus : 0 ≤ u t * p14ExpSum x :=
          mul_nonneg (hu_nonneg t) hexact_pos.le
        have hr : remainder t ≤ |remainder t| := le_abs_self _
        push_cast
        nlinarith
  · intro t
    unfold p14BasicSumDelta
    ring

end HighamBench
