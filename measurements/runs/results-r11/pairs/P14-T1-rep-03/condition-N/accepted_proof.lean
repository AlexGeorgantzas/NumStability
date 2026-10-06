import HighamBench.P14Definitions

namespace HighamBench

open scoped BigOperators

private noncomputable def p14RoundoffConstant : ℕ → ℝ
  | 0 => 0
  | k + 1 => 2 * p14RoundoffConstant k + k

private lemma p14RoundoffConstant_nonneg (k : ℕ) :
    0 ≤ p14RoundoffConstant k := by
  induction k with
  | zero => simp [p14RoundoffConstant]
  | succ k ih =>
      simp only [p14RoundoffConstant]
      positivity

private lemma p14_recursive_sum_error
    (fp : StandardAddModel) (u : ℝ) (hunit : fp.u = u)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (k : ℕ)
    (v : Fin (k + 1) → ℝ) (hv : ∀ i, 0 ≤ v i) :
    let total := ∑ i, v i
    0 ≤ recursiveSum fp.fl_add (k + 1) v ∧
      |recursiveSum fp.fl_add (k + 1) v - total| ≤
        (k : ℝ) * u * total + p14RoundoffConstant k * u ^ 2 * total := by
  induction k with
  | zero =>
      simp [recursiveSum, p14RoundoffConstant, hv]
  | succ k ih =>
      let v' : Fin (k + 1) → ℝ := fun i => v i.castSucc
      let oldTotal : ℝ := ∑ i, v' i
      let oldSum : ℝ := recursiveSum fp.fl_add (k + 1) v'
      let last : ℝ := v (Fin.last (k + 1))
      have hv' : ∀ i, 0 ≤ v' i := fun i => hv i.castSucc
      have hlast : 0 ≤ last := hv _
      have holdTotal : 0 ≤ oldTotal := Finset.sum_nonneg fun i _ => hv' i
      have ih' := ih v' hv'
      change 0 ≤ oldSum ∧
        |oldSum - oldTotal| ≤
          (k : ℝ) * u * oldTotal +
            p14RoundoffConstant k * u ^ 2 * oldTotal at ih'
      obtain ⟨holdSum, holdError⟩ := ih'
      obtain ⟨δ, hδ, hadd⟩ := fp.model_add oldSum last
      have hδ' : |δ| ≤ u := by simpa [hunit] using hδ
      have hδ_lower : -u ≤ δ := (abs_le.mp hδ').1
      have honeδ : 0 ≤ 1 + δ := by linarith
      have htotal : 0 ≤ oldTotal + last := add_nonneg holdTotal hlast
      have hold_le : oldSum ≤ oldTotal + |oldSum - oldTotal| := by
        have := le_abs_self (oldSum - oldTotal)
        linarith
      have hsum_le : oldSum + last ≤
          oldTotal + last + |oldSum - oldTotal| := by linarith
      have hadd_nonneg : 0 ≤ fp.fl_add oldSum last := by
        rw [hadd]
        positivity
      have herror_step :
          |fp.fl_add oldSum last - (oldTotal + last)| ≤
            (1 + u) * |oldSum - oldTotal| + u * (oldTotal + last) := by
        rw [hadd]
        have hid :
            (oldSum + last) * (1 + δ) - (oldTotal + last) =
              (oldSum - oldTotal) + δ * (oldSum + last) := by ring
        rw [hid]
        calc
          |(oldSum - oldTotal) + δ * (oldSum + last)| ≤
              |oldSum - oldTotal| + |δ * (oldSum + last)| := abs_add_le _ _
          _ = |oldSum - oldTotal| + |δ| * (oldSum + last) := by
              rw [abs_mul, abs_of_nonneg (add_nonneg holdSum hlast)]
          _ ≤ |oldSum - oldTotal| + u * (oldSum + last) := by
              gcongr
          _ ≤ |oldSum - oldTotal| +
                u * (oldTotal + last + |oldSum - oldTotal|) := by
              gcongr
          _ = (1 + u) * |oldSum - oldTotal| +
                u * (oldTotal + last) := by ring
      have hC : 0 ≤ p14RoundoffConstant k := p14RoundoffConstant_nonneg k
      have holdTotal_le : oldTotal ≤ oldTotal + last := by linarith
      have hquadratic :
          (1 + u) *
              ((k : ℝ) * u * oldTotal +
                p14RoundoffConstant k * u ^ 2 * oldTotal) +
              u * (oldTotal + last) ≤
            ((k + 1 : ℕ) : ℝ) * u * (oldTotal + last) +
              p14RoundoffConstant (k + 1) * u ^ 2 *
                (oldTotal + last) := by
        simp only [p14RoundoffConstant, Nat.cast_add, Nat.cast_one]
        have hk : 0 ≤ (k : ℝ) := by positivity
        have hCu : 0 ≤ p14RoundoffConstant k + (k : ℝ) := add_nonneg hC hk
        have hu_cube : u ^ 3 ≤ u ^ 2 := by
          nlinarith [sq_nonneg u]
        have hlin :
            (k : ℝ) * u * oldTotal ≤
              (k : ℝ) * u * (oldTotal + last) := by gcongr
        have hquad :
            (p14RoundoffConstant k + (k : ℝ)) * u ^ 2 * oldTotal ≤
              (p14RoundoffConstant k + (k : ℝ)) * u ^ 2 *
                (oldTotal + last) := by gcongr
        have hcubic :
            p14RoundoffConstant k * u ^ 3 * oldTotal ≤
              p14RoundoffConstant k * u ^ 2 * (oldTotal + last) := by
          calc
            p14RoundoffConstant k * u ^ 3 * oldTotal ≤
                p14RoundoffConstant k * u ^ 2 * oldTotal := by gcongr
            _ ≤ p14RoundoffConstant k * u ^ 2 * (oldTotal + last) := by
                gcongr
        calc
          (1 + u) *
                ((k : ℝ) * u * oldTotal +
                  p14RoundoffConstant k * u ^ 2 * oldTotal) +
              u * (oldTotal + last) =
              (k : ℝ) * u * oldTotal + u * (oldTotal + last) +
                (p14RoundoffConstant k + (k : ℝ)) * u ^ 2 * oldTotal +
                p14RoundoffConstant k * u ^ 3 * oldTotal := by ring
          _ ≤ (k : ℝ) * u * (oldTotal + last) + u * (oldTotal + last) +
                (p14RoundoffConstant k + (k : ℝ)) * u ^ 2 *
                  (oldTotal + last) +
                p14RoundoffConstant k * u ^ 2 * (oldTotal + last) := by
              gcongr
          _ = ((k : ℝ) + 1) * u * (oldTotal + last) +
                (2 * p14RoundoffConstant k + (k : ℝ)) * u ^ 2 *
                  (oldTotal + last) := by ring
      have herror :
          |fp.fl_add oldSum last - (oldTotal + last)| ≤
            ((k + 1 : ℕ) : ℝ) * u * (oldTotal + last) +
              p14RoundoffConstant (k + 1) * u ^ 2 *
                (oldTotal + last) :=
        herror_step.trans ((show
          (1 + u) * |oldSum - oldTotal| + u * (oldTotal + last) ≤
            (1 + u) *
                ((k : ℝ) * u * oldTotal +
                  p14RoundoffConstant k * u ^ 2 * oldTotal) +
              u * (oldTotal + last) by
            gcongr).trans hquadratic)
      have hrec : recursiveSum fp.fl_add (k + 1 + 1) v =
          fp.fl_add oldSum last := by
        rw [recursiveSum]
        rw [dif_neg (Nat.succ_ne_zero k)]
      have htotal_eq : (∑ i, v i) = oldTotal + last := by
        rw [Fin.sum_univ_castSucc]
      simp only [hrec, htotal_eq]
      exact ⟨hadd_nonneg, herror⟩

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
  cases n with
  | zero => simp at hn
  | succ k =>
      have hsum_pos : 0 < p14ExpSum x := by
        rw [p14ExpSum]
        exact Finset.sum_pos (fun i _ => Real.exp_pos (x i)) Finset.univ_nonempty
      have hu_nonneg (t : ι) : 0 ≤ u t := by
        rw [← (run t).unit_eq]
        exact (run t).fp.u_nonneg
      have hexp_error : ∀ t i,
          |p14ComputedExp (run t) i - Real.exp (x i)| ≤
            u t * Real.exp (x i) := by
        intro t i
        have hi := (run t).expError_le i
        rw [p14ComputedExp]
        have hid :
            Real.exp (x i) * (1 + (run t).expError i) - Real.exp (x i) =
              Real.exp (x i) * (run t).expError i := by ring
        rw [hid, abs_mul, abs_of_pos (Real.exp_pos (x i))]
        calc
          Real.exp (x i) * |(run t).expError i| ≤
              Real.exp (x i) * u t := by
            gcongr
          _ = u t * Real.exp (x i) := by ring
      refine ⟨hsum_pos, hexp_error, ?_, ?_⟩
      · let C : ℝ := p14RoundoffConstant k
        let D : ℝ := ((k : ℝ) + 2 * C) * p14ExpSum x
        refine ⟨(fun t => D * (u t) ^ 2), ?_, ?_⟩
        · simpa using
            (Asymptotics.isBigO_const_mul_self D (fun t => (u t) ^ 2) l)
        · have hu_lt : ∀ᶠ t in l, u t < 1 :=
            (tendsto_order.mp hu).2 1 (by norm_num)
          filter_upwards [hu_lt] with t hut_lt
          have hut : 0 ≤ u t := hu_nonneg t
          have hut_one : u t ≤ 1 := hut_lt.le
          have hsum_nonneg : 0 ≤ p14ExpSum x := hsum_pos.le
          have hcomp_nonneg : ∀ i, 0 ≤ p14ComputedExp (run t) i := by
            intro i
            rw [p14ComputedExp]
            apply mul_nonneg (Real.exp_pos (x i)).le
            have hi := (run t).expError_le i
            have hi' : |(run t).expError i| ≤ u t := hi
            have := (abs_le.mp hi').1
            linarith
          have hinput :
              |p14ExactComputedExpSum (run t) - p14ExpSum x| ≤
                u t * p14ExpSum x := by
            rw [p14ExactComputedExpSum, p14ExpSum,
              ← Finset.sum_sub_distrib]
            calc
              |∑ i, (p14ComputedExp (run t) i - Real.exp (x i))| ≤
                  ∑ i, |p14ComputedExp (run t) i - Real.exp (x i)| := by
                simpa using Finset.abs_sum_le_sum_abs
                  (fun i => p14ComputedExp (run t) i - Real.exp (x i))
                  Finset.univ
              _ ≤ ∑ i, u t * Real.exp (x i) := by
                exact Finset.sum_le_sum fun i _ => hexp_error t i
              _ = u t * ∑ i, Real.exp (x i) := by
                rw [Finset.mul_sum]
          have hcomputed_nonneg : 0 ≤ p14ExactComputedExpSum (run t) := by
            rw [p14ExactComputedExpSum]
            exact Finset.sum_nonneg fun i _ => hcomp_nonneg i
          have hcomputed_le :
              p14ExactComputedExpSum (run t) ≤
                p14ExpSum x + u t * p14ExpSum x := by
            have hle := le_abs_self
              (p14ExactComputedExpSum (run t) - p14ExpSum x)
            linarith
          have hcomputed_le_two :
              p14ExactComputedExpSum (run t) ≤ 2 * p14ExpSum x := by
            have hus : u t * p14ExpSum x ≤ p14ExpSum x :=
              mul_le_of_le_one_left hsum_nonneg hut_one
            linarith
          have hrec := p14_recursive_sum_error
            (run t).fp (u t) (run t).unit_eq hut hut_one k
            (p14ComputedExp (run t)) hcomp_nonneg
          have hrec_error :
              |p14RecursiveComputedExpSum (run t) -
                  p14ExactComputedExpSum (run t)| ≤
                (k : ℝ) * u t * p14ExactComputedExpSum (run t) +
                  C * (u t) ^ 2 * p14ExactComputedExpSum (run t) := by
            simpa [p14RecursiveComputedExpSum, p14ExactComputedExpSum, C]
              using hrec.2
          have hC : 0 ≤ C := by
            exact p14RoundoffConstant_nonneg k
          have hD : 0 ≤ D := by
            dsimp [D]
            positivity
          have hfirst :
              (k : ℝ) * u t * p14ExactComputedExpSum (run t) ≤
                (k : ℝ) * u t *
                  (p14ExpSum x + u t * p14ExpSum x) := by
            gcongr
          have hsecond :
              C * (u t) ^ 2 * p14ExactComputedExpSum (run t) ≤
                C * (u t) ^ 2 * (2 * p14ExpSum x) := by
            gcongr
          change
            |p14RecursiveComputedExpSum (run t) - p14ExpSum x| ≤
              ((k + 1 : ℕ) + 1 : ℝ) * u t * p14ExpSum x +
                |D * (u t) ^ 2|
          have htriangle :
              |p14RecursiveComputedExpSum (run t) - p14ExpSum x| ≤
                |p14RecursiveComputedExpSum (run t) -
                    p14ExactComputedExpSum (run t)| +
                  |p14ExactComputedExpSum (run t) - p14ExpSum x| := by
            have hid :
                p14RecursiveComputedExpSum (run t) - p14ExpSum x =
                  (p14RecursiveComputedExpSum (run t) -
                    p14ExactComputedExpSum (run t)) +
                  (p14ExactComputedExpSum (run t) - p14ExpSum x) := by ring
            rw [hid]
            exact abs_add_le _ _
          calc
            |p14RecursiveComputedExpSum (run t) - p14ExpSum x| ≤
                |p14RecursiveComputedExpSum (run t) -
                    p14ExactComputedExpSum (run t)| +
                  |p14ExactComputedExpSum (run t) - p14ExpSum x| := htriangle
            _ ≤ ((k : ℝ) * u t * p14ExactComputedExpSum (run t) +
                    C * (u t) ^ 2 * p14ExactComputedExpSum (run t)) +
                  u t * p14ExpSum x := add_le_add hrec_error hinput
            _ ≤ ((k : ℝ) * u t *
                    (p14ExpSum x + u t * p14ExpSum x) +
                  C * (u t) ^ 2 * (2 * p14ExpSum x)) +
                  u t * p14ExpSum x := by gcongr
            _ = ((k : ℝ) + 1) * u t * p14ExpSum x +
                  D * (u t) ^ 2 := by
                dsimp [D]
                ring
            _ ≤ ((k + 1 : ℕ) + 1 : ℝ) * u t * p14ExpSum x +
                  |D * (u t) ^ 2| := by
                rw [abs_of_nonneg (mul_nonneg hD (sq_nonneg (u t)))]
                norm_num [Nat.cast_add, Nat.cast_one]
                nlinarith [mul_nonneg hut hsum_nonneg]
      · intro t
        rw [p14BasicSumDelta]
        ring

end HighamBench
