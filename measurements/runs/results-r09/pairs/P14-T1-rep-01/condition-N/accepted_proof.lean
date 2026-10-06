import HighamBench.P14Definitions

namespace HighamBench

open scoped BigOperators

private def p14ErrorConstant : ℕ → ℝ
  | 0 => 0
  | n + 1 => (n : ℝ) + 2 * p14ErrorConstant n + 1

private lemma p14ErrorConstant_nonneg (n : ℕ) :
    0 ≤ p14ErrorConstant n := by
  induction n with
  | zero => simp [p14ErrorConstant]
  | succ n ih =>
      simp only [p14ErrorConstant]
      positivity

private lemma p14_recursiveSum_error_bound :
    ∀ {n : ℕ} (hn : 0 < n) (w v : Fin n → ℝ) (a : StandardAddModel)
      (u : ℝ),
      a.u = u →
      0 ≤ u →
      u ≤ 1 →
      (∀ i, 0 ≤ w i) →
      (∀ i, |v i - w i| ≤ u * w i) →
      |recursiveSum a.fl_add n v - ∑ i, w i| ≤
        (n : ℝ) * u * (∑ i, w i) +
          p14ErrorConstant n * u ^ 2 * (∑ i, w i) := by
  intro n
  induction n with
  | zero =>
      intro hn
      omega
  | succ n ih =>
      intro hn w v a u hau hu hu1 hw hv
      by_cases hn0 : n = 0
      · subst n
        have hbase := hv (0 : Fin 1)
        have hextra : 0 ≤ u ^ 2 * w 0 := mul_nonneg (sq_nonneg u) (hw 0)
        simpa [recursiveSum, Fin.sum_univ_one, p14ErrorConstant,
          mul_assoc] using hbase.trans (le_add_of_nonneg_right hextra)
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        let w' : Fin n → ℝ := fun i => w i.castSucc
        let v' : Fin n → ℝ := fun i => v i.castSucc
        let W : ℝ := ∑ i, w' i
        let z : ℝ := w (Fin.last n)
        let R : ℝ := recursiveSum a.fl_add n v'
        let q : ℝ := v (Fin.last n)
        have hW : 0 ≤ W := by
          dsimp [W, w']
          exact Finset.sum_nonneg fun i _ => hw i.castSucc
        have hz : 0 ≤ z := hw (Fin.last n)
        have hih : |R - W| ≤
            (n : ℝ) * u * W + p14ErrorConstant n * u ^ 2 * W := by
          apply ih hnpos w' v' a u hau hu hu1
          · intro i
            exact hw i.castSucc
          · intro i
            exact hv i.castSucc
        have hq : |q - z| ≤ u * z := hv (Fin.last n)
        obtain ⟨δ, hδ, hadd⟩ := a.model_add R q
        have hau' : a.u = u := hau
        rw [hau'] at hδ
        have hRq : |R + q| ≤ |R - W| + |q - z| + W + z := by
          calc
            |R + q| = |(R - W) + (q - z) + W + z| := by ring_nf
            _ ≤ |R - W| + |q - z| + |W| + |z| := by
              calc
                |(R - W) + (q - z) + W + z| ≤
                    |(R - W) + (q - z) + W| + |z| := abs_add_le _ _
                _ ≤ |(R - W) + (q - z)| + |W| + |z| := by
                  gcongr
                  exact abs_add_le _ _
                _ ≤ |R - W| + |q - z| + |W| + |z| := by
                  gcongr
                  exact abs_add_le _ _
            _ = |R - W| + |q - z| + W + z := by
              rw [abs_of_nonneg hW, abs_of_nonneg hz]
        have hmain :
            |(R + q) * (1 + δ) - (W + z)| ≤
              (n + 1 : ℕ) * u * (W + z) +
                p14ErrorConstant (n + 1) * u ^ 2 * (W + z) := by
          have hsplit :
              |(R + q) * (1 + δ) - (W + z)| ≤
                |R - W| + |q - z| + |δ| * |R + q| := by
            calc
              |(R + q) * (1 + δ) - (W + z)| =
                  |(R - W) + (q - z) + δ * (R + q)| := by ring_nf
              _ ≤ |R - W| + |q - z| + |δ * (R + q)| := by
                calc
                  |(R - W) + (q - z) + δ * (R + q)| ≤
                      |(R - W) + (q - z)| + |δ * (R + q)| := abs_add_le _ _
                  _ ≤ |R - W| + |q - z| + |δ * (R + q)| := by
                    gcongr
                    exact abs_add_le _ _
              _ = |R - W| + |q - z| + |δ| * |R + q| := by
                rw [abs_mul]
          have hδnonneg : 0 ≤ |δ| := abs_nonneg δ
          have hpre :
              |R - W| + |q - z| + |δ| * |R + q| ≤
                ((n : ℝ) * u * W + p14ErrorConstant n * u ^ 2 * W) +
                u * z + u *
                  (((n : ℝ) * u * W + p14ErrorConstant n * u ^ 2 * W) +
                    u * z + W + z) := by
            calc
              |R - W| + |q - z| + |δ| * |R + q| ≤
                  ((n : ℝ) * u * W + p14ErrorConstant n * u ^ 2 * W) +
                  u * z + u * |R + q| := by
                    gcongr
              _ ≤
                  ((n : ℝ) * u * W + p14ErrorConstant n * u ^ 2 * W) +
                  u * z + u *
                    (|R - W| + |q - z| + W + z) := by
                    gcongr
              _ ≤
                  ((n : ℝ) * u * W + p14ErrorConstant n * u ^ 2 * W) +
                  u * z + u *
                    (((n : ℝ) * u * W + p14ErrorConstant n * u ^ 2 * W) +
                      u * z + W + z) := by
                    gcongr
          have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
          have hC : 0 ≤ p14ErrorConstant n := p14ErrorConstant_nonneg n
          have hu2 : 0 ≤ u ^ 2 := sq_nonneg u
          have hu3 : u ^ 3 ≤ u ^ 2 := by nlinarith
          have hcu : p14ErrorConstant n * u ^ 3 * W ≤
              p14ErrorConstant n * u ^ 2 * W := by
            gcongr
          have hrest : 0 ≤
              ((n : ℝ) - 1) * u * z + u ^ 2 * W +
                (p14ErrorConstant n * u ^ 2 * W -
                  p14ErrorConstant n * u ^ 3 * W) +
                ((n : ℝ) + 2 * p14ErrorConstant n) * u ^ 2 * z := by
            have h1 : 0 ≤ ((n : ℝ) - 1) * u * z :=
              mul_nonneg (mul_nonneg (sub_nonneg.mpr hnreal) hu) hz
            have h2 : 0 ≤ u ^ 2 * W := mul_nonneg hu2 hW
            have h3 : 0 ≤ p14ErrorConstant n * u ^ 2 * W -
                p14ErrorConstant n * u ^ 3 * W := sub_nonneg.mpr hcu
            have h4 : 0 ≤ ((n : ℝ) + 2 * p14ErrorConstant n) * u ^ 2 * z :=
              mul_nonneg (mul_nonneg (add_nonneg (Nat.cast_nonneg n)
                (mul_nonneg (by norm_num) hC)) hu2) hz
            exact add_nonneg (add_nonneg (add_nonneg h1 h2) h3) h4
          calc
            |(R + q) * (1 + δ) - (W + z)| ≤
                |R - W| + |q - z| + |δ| * |R + q| := hsplit
            _ ≤
                ((n : ℝ) * u * W + p14ErrorConstant n * u ^ 2 * W) +
                u * z + u *
                  (((n : ℝ) * u * W + p14ErrorConstant n * u ^ 2 * W) +
                    u * z + W + z) := hpre
            _ ≤ (n + 1 : ℕ) * u * (W + z) +
                p14ErrorConstant (n + 1) * u ^ 2 * (W + z) := by
              simp only [p14ErrorConstant]
              push_cast
              calc
                (n : ℝ) * u * W + p14ErrorConstant n * u ^ 2 * W + u * z +
                    u * ((n : ℝ) * u * W + p14ErrorConstant n * u ^ 2 * W +
                      u * z + W + z) ≤
                    (n : ℝ) * u * W + p14ErrorConstant n * u ^ 2 * W + u * z +
                      u * ((n : ℝ) * u * W + p14ErrorConstant n * u ^ 2 * W +
                        u * z + W + z) +
                      (((n : ℝ) - 1) * u * z + u ^ 2 * W +
                        (p14ErrorConstant n * u ^ 2 * W -
                          p14ErrorConstant n * u ^ 3 * W) +
                        ((n : ℝ) + 2 * p14ErrorConstant n) * u ^ 2 * z) :=
                  le_add_of_nonneg_right hrest
                _ = ((n : ℝ) + 1) * u * (W + z) +
                    ((n : ℝ) + 2 * p14ErrorConstant n + 1) * u ^ 2 *
                      (W + z) := by ring
        simpa [recursiveSum, hn0, w', v', W, z, R, q, hadd,
          Fin.sum_univ_castSucc] using hmain

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
  have hsum_nonneg : 0 ≤ p14ExpSum x := by
    unfold p14ExpSum
    exact Finset.sum_nonneg fun i _ => (Real.exp_pos (x i)).le
  have hsum_pos : 0 < p14ExpSum x := by
    unfold p14ExpSum
    apply Finset.sum_pos
    · intro i _
      exact Real.exp_pos (x i)
    · exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hexp : ∀ t i,
      |p14ComputedExp (run t) i - Real.exp (x i)| ≤
        u t * Real.exp (x i) := by
    intro t i
    rw [p14ComputedExp, mul_add, mul_one, add_sub_cancel_left, abs_mul,
      abs_of_pos (Real.exp_pos (x i))]
    have hi := (run t).expError_le i
    nlinarith [Real.exp_pos (x i)]
  refine ⟨hsum_pos, hexp, ?_, ?_⟩
  · refine ⟨fun t => p14ErrorConstant n * p14ExpSum x * (u t) ^ 2, ?_, ?_⟩
    · simpa [mul_assoc] using
        (Asymptotics.isBigO_const_mul_self
          (p14ErrorConstant n * p14ExpSum x) (fun t => (u t) ^ 2) l)
    · have hu_one : ∀ᶠ t in l, u t < 1 :=
        (tendsto_order.1 hu).2 1 zero_lt_one
      filter_upwards [hu_one] with t hut
      have hut0 : 0 ≤ u t := by
        rw [← (run t).unit_eq]
        exact (run t).fp.u_nonneg
      have hbound := p14_recursiveSum_error_bound hn
        (fun i => Real.exp (x i)) (p14ComputedExp (run t)) (run t).fp (u t)
        (run t).unit_eq hut0 hut.le
        (fun i => (Real.exp_pos (x i)).le) (hexp t)
      have hdelta : |p14BasicSumDelta (run t)| ≤
          (n : ℝ) * u t * p14ExpSum x +
            p14ErrorConstant n * (u t) ^ 2 * p14ExpSum x := by
        simpa [p14BasicSumDelta, p14RecursiveComputedExpSum, p14ExpSum] using hbound
      have hC : 0 ≤ p14ErrorConstant n := p14ErrorConstant_nonneg n
      have hrem : 0 ≤ p14ErrorConstant n * p14ExpSum x * (u t) ^ 2 :=
        mul_nonneg (mul_nonneg hC hsum_nonneg) (sq_nonneg (u t))
      rw [abs_of_nonneg hrem]
      calc
        |p14BasicSumDelta (run t)| ≤
            (n : ℝ) * u t * p14ExpSum x +
              p14ErrorConstant n * (u t) ^ 2 * p14ExpSum x := hdelta
        _ ≤ (n + 1 : ℝ) * u t * p14ExpSum x +
              p14ErrorConstant n * p14ExpSum x * (u t) ^ 2 := by
            have hus : 0 ≤ u t * p14ExpSum x :=
              mul_nonneg hut0 hsum_nonneg
            nlinarith
  · intro t
    unfold p14BasicSumDelta
    ring

end HighamBench
