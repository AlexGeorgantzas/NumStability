import HighamBench.P14Definitions

namespace HighamBench

open scoped BigOperators

private lemma recursiveSum_error_bound
    (n : ℕ) (fp : StandardAddModel)
    (v y : Fin n → ℝ)
    (hv : ∀ i, 0 ≤ v i)
    (hy : ∀ i, |y i - v i| ≤ fp.u * v i) :
    |recursiveSum fp.fl_add n y - ∑ i, v i| ≤
      ((1 + fp.u) ^ n - 1) * ∑ i, v i := by
  induction n with
  | zero => simp [recursiveSum]
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        simpa [recursiveSum] using hy (0 : Fin 1)
      · obtain ⟨δ, hδ, hadd⟩ := fp.model_add
          (recursiveSum fp.fl_add n (fun i => y i.castSucc))
          (y (Fin.last n))
        have hprev := ih (fun i => v i.castSucc) (fun i => y i.castSucc)
          (fun i => hv i.castSucc) (fun i => hy i.castSucc)
        let A := recursiveSum fp.fl_add n (fun i => y i.castSucc)
        let S := ∑ i : Fin n, v i.castSucc
        let b := y (Fin.last n)
        let a := v (Fin.last n)
        let q := (1 + fp.u) ^ n - 1
        have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => hv i.castSucc)
        have ha : 0 ≤ a := hv (Fin.last n)
        have hp : |A - S| ≤ q * S := by simpa [A, S, q] using hprev
        have hb : |b - a| ≤ fp.u * a := by simpa [a, b] using hy (Fin.last n)
        have habs : |A + b| ≤ S + a + (q * S + fp.u * a) := by
          calc
            |A + b| = |(S + a) + ((A - S) + (b - a))| := by ring_nf
            _ ≤ |S + a| + (|A - S| + |b - a|) := by
              linarith [abs_add_le (S + a) ((A - S) + (b - a)),
                abs_add_le (A - S) (b - a)]
            _ ≤ S + a + (q * S + fp.u * a) := by
              rw [abs_of_nonneg (add_nonneg hS ha)]
              gcongr
        have hu0 : 0 ≤ fp.u := fp.u_nonneg
        have hbase : 1 ≤ 1 + fp.u := by linarith
        have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
        have hpow : (1 + fp.u) ^ 2 ≤ (1 + fp.u) ^ (n + 1) :=
          pow_le_pow_right₀ hbase (Nat.succ_le_succ hn1)
        have hrec : (1 + fp.u) ^ (n + 1) =
            (1 + fp.u) ^ n * (1 + fp.u) := by
          rw [pow_succ]
        rw [recursiveSum, dif_neg hn, hadd, Fin.sum_univ_castSucc]
        change |(A + b) * (1 + δ) - (S + a)| ≤
          ((1 + fp.u) ^ (n + 1) - 1) * (S + a)
        calc
          |(A + b) * (1 + δ) - (S + a)| =
              |((A - S) + (b - a)) + δ * (A + b)| := by ring_nf
          _ ≤ (|A - S| + |b - a|) + |δ| * |A + b| := by
            exact (abs_add_le _ _).trans
              (add_le_add (abs_add_le _ _) (le_of_eq (abs_mul _ _)))
          _ ≤ (q * S + fp.u * a) +
              fp.u * (S + a + (q * S + fp.u * a)) := by
            gcongr
          _ ≤ ((1 + fp.u) ^ (n + 1) - 1) * (S + a) := by
            dsimp [q]
            norm_num [pow_two] at hpow
            nlinarith [hrec]

private lemma pow_remainder_isBigO
    {ι : Type*} {l : Filter ι}
    (u : ι → ℝ) (hu : Filter.Tendsto u l (nhds 0)) (n : ℕ) :
    (fun t => (1 + u t) ^ n - 1 - (n : ℝ) * u t) =O[l]
      (fun t => (u t) ^ 2) := by
  induction n with
  | zero => simpa using Asymptotics.isBigO_zero (fun t => (u t) ^ 2) l
  | succ n ih =>
      have hbase : (fun t => 1 + u t) =O[l] (fun _ => (1 : ℝ)) := by
        apply Filter.Tendsto.isBigO_one
        simpa using hu.const_add 1
      have hprod :
          (fun t => (1 + u t) * ((1 + u t) ^ n - 1 - (n : ℝ) * u t)) =O[l]
            (fun t => (u t) ^ 2) := by
        simpa only [one_mul] using hbase.mul ih
      have hquadratic : (fun t => (n : ℝ) * (u t) ^ 2) =O[l]
          (fun t => (u t) ^ 2) :=
        Asymptotics.isBigO_const_mul_self (n : ℝ) _ l
      apply (hprod.add hquadratic).congr_left
      intro t
      rw [pow_succ]
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
  let i0 : Fin n := ⟨0, hn⟩
  have hexact_pos : 0 < p14ExpSum x := by
    unfold p14ExpSum
    exact Finset.sum_pos' (fun i _ => (Real.exp_pos (x i)).le)
      ⟨i0, Finset.mem_univ i0, Real.exp_pos (x i0)⟩
  have hexp : ∀ t i,
      |p14ComputedExp (run t) i - Real.exp (x i)| ≤
        u t * Real.exp (x i) := by
    intro t i
    rw [p14ComputedExp]
    have he := (run t).expError_le i
    rw [abs_le] at he ⊢
    constructor <;> nlinarith [Real.exp_pos (x i)]
  have hround : ∀ t,
      |p14BasicSumDelta (run t)| ≤
        ((1 + u t) ^ n - 1) * p14ExpSum x := by
    intro t
    have h := recursiveSum_error_bound n (run t).fp
      (fun i => Real.exp (x i)) (fun i => p14ComputedExp (run t) i)
      (fun i => (Real.exp_pos (x i)).le)
      (fun i => by
        simpa only [(run t).unit_eq] using hexp t i)
    simpa only [p14BasicSumDelta, p14RecursiveComputedExpSum,
      p14ExpSum, (run t).unit_eq] using h
  let remainder : ι → ℝ := fun t =>
    p14ExpSum x * ((1 + u t) ^ n - 1 - (n : ℝ) * u t)
  have hremainder : remainder =O[l] (fun t => (u t) ^ 2) := by
    have hc := Asymptotics.isBigO_const_mul_self (p14ExpSum x)
      (fun t => (1 + u t) ^ n - 1 - (n : ℝ) * u t) l
    exact hc.trans (pow_remainder_isBigO u hu n)
  refine ⟨hexact_pos, hexp, ⟨remainder, hremainder, ?_⟩, ?_⟩
  · apply Filter.Eventually.of_forall
    intro t
    have hut : 0 ≤ u t := by
      rw [← (run t).unit_eq]
      exact (run t).fp.u_nonneg
    calc
      |p14BasicSumDelta (run t)| ≤
          ((1 + u t) ^ n - 1) * p14ExpSum x := hround t
      _ = (n : ℝ) * u t * p14ExpSum x + remainder t := by
        dsimp [remainder]
        ring
      _ ≤ (n + 1 : ℝ) * u t * p14ExpSum x + |remainder t| := by
        have hr := le_abs_self (remainder t)
        push_cast
        nlinarith [mul_nonneg hut hexact_pos.le]
  · intro t
    rw [p14BasicSumDelta]
    ring

end HighamBench
