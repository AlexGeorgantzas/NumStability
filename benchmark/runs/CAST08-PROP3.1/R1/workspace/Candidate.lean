import NumStability.Algorithms.Summation.Recursive.Core
import Mathlib.Analysis.MeanInequalities

open scoped BigOperators

namespace HighamBenchCandidate

/-- The `j`th consecutive block at the next level consists of the indices
`j * b^levels + i`, for `0 ≤ i < b^levels`. -/
def blockIndex (b levels : ℕ) (j : Fin b) (i : Fin (b ^ levels)) :
    Fin (b ^ (levels + 1)) :=
  ⟨j.val * b ^ levels + i.val, by
    have h₁ : j.val * b ^ levels + i.val < (j.val + 1) * b ^ levels := by
      simpa [Nat.add_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        Nat.add_lt_add_left i.isLt (j.val * b ^ levels)
    have h₂ : (j.val + 1) * b ^ levels ≤ b * b ^ levels :=
      Nat.mul_le_mul_right (b ^ levels) (Nat.succ_le_of_lt j.isLt)
    calc
      j.val * b ^ levels + i.val < (j.val + 1) * b ^ levels := h₁
      _ ≤ b * b ^ levels := h₂
      _ = b ^ (levels + 1) := by simp [pow_succ, Nat.mul_comm]
  ⟩

/-- Equal-block superblock summation. Level zero is a single input. Each
higher level recursively computes `b` consecutive child totals and adds them
left to right using the rounded addition of `fp`. Thus level one is ordinary
recursive summation, and level `t` has `b^t` inputs and exactly `t` summation
levels. The final transfer omitted by Figure 3.1(a)'s propagation loop is
included, as in the paper's prose and Figure 3.2. -/
noncomputable def superblockSum (fp : NumStability.FPModel) (b : ℕ) :
    (levels : ℕ) → (Fin (b ^ levels) → ℝ) → ℝ
  | 0, v => v ⟨0, by simp⟩
  | levels + 1, v =>
      NumStability.fl_recursiveSum fp b (fun j =>
        superblockSum fp b levels (fun i => v (blockIndex b levels j i)))

private def blockEquiv (b levels : ℕ) :
    Fin b × Fin (b ^ levels) ≃ Fin (b ^ (levels + 1)) :=
  finProdFinEquiv.trans (Fin.castOrderIso (by simp [pow_succ, Nat.mul_comm])).toEquiv

private theorem blockEquiv_apply (b levels : ℕ) (j : Fin b) (i : Fin (b ^ levels)) :
    blockEquiv b levels (j, i) = blockIndex b levels j i := by
  apply Fin.ext
  simp [blockEquiv, Fin.castOrderIso, finProdFinEquiv, blockIndex,
    Nat.mul_comm, Nat.add_comm]

private theorem sum_blockIndex (b levels : ℕ)
    (f : Fin (b ^ (levels + 1)) → ℝ) :
    (∑ j : Fin b, ∑ i : Fin (b ^ levels), f (blockIndex b levels j i)) =
      ∑ k : Fin (b ^ (levels + 1)), f k := by
  rw [← Fintype.sum_prod_type
    (fun p : Fin b × Fin (b ^ levels) => f (blockIndex b levels p.1 p.2))]
  exact Fintype.sum_equiv (blockEquiv b levels)
    (fun p => f (blockIndex b levels p.1 p.2)) f
    (by intro p; rw [blockEquiv_apply])

private theorem recursive_composition_bound
    (fp : NumStability.FPModel) (b k : ℕ)
    (c e m : Fin b → ℝ)
    (hm : ∀ j, 0 ≤ m j)
    (he : ∀ j, |e j| ≤ m j)
    (hc : ∀ j, |c j - e j| ≤ NumStability.gamma fp k * m j)
    (hv : NumStability.gammaValid fp (k + (b - 1))) :
    |NumStability.fl_recursiveSum fp b c - ∑ j : Fin b, e j| ≤
      NumStability.gamma fp (k + (b - 1)) * ∑ j : Fin b, m j := by
  have hvk : NumStability.gammaValid fp k :=
    NumStability.gammaValid_mono fp (Nat.le_add_right k (b - 1)) hv
  have hvb : NumStability.gammaValid fp (b - 1) :=
    NumStability.gammaValid_mono fp (Nat.le_add_left (b - 1) k) hv
  have hg0 : 0 ≤ NumStability.gamma fp (b - 1) :=
    NumStability.gamma_nonneg fp hvb
  have hmSum : 0 ≤ ∑ j : Fin b, m j := Finset.sum_nonneg (by intro j _; exact hm j)
  have hcj : ∀ j : Fin b,
      |c j| ≤ (1 + NumStability.gamma fp k) * m j := by
    intro j
    calc
      |c j| = |(c j - e j) + e j| := by ring
      _ ≤ |c j - e j| + |e j| := abs_add_le _ _
      _ ≤ NumStability.gamma fp k * m j + m j := add_le_add (hc j) (he j)
      _ = (1 + NumStability.gamma fp k) * m j := by ring
  have hcSum : (∑ j : Fin b, |c j|) ≤
      (1 + NumStability.gamma fp k) * ∑ j : Fin b, m j := by
    calc
      (∑ j : Fin b, |c j|) ≤ ∑ j : Fin b, (1 + NumStability.gamma fp k) * m j :=
        Finset.sum_le_sum (by intro j _; exact hcj j)
      _ = (1 + NumStability.gamma fp k) * ∑ j : Fin b, m j := by
        rw [Finset.mul_sum]
  have heSum : |(∑ j : Fin b, c j) - ∑ j : Fin b, e j| ≤
      NumStability.gamma fp k * ∑ j : Fin b, m j := by
    calc
      |(∑ j : Fin b, c j) - ∑ j : Fin b, e j| =
          |∑ j : Fin b, (c j - e j)| := by rw [Finset.sum_sub_distrib]
      _ ≤ ∑ j : Fin b, |c j - e j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin b, NumStability.gamma fp k * m j :=
        Finset.sum_le_sum (by intro j _; exact hc j)
      _ = NumStability.gamma fp k * ∑ j : Fin b, m j := by rw [Finset.mul_sum]
  have hfl := NumStability.recursiveSum_forward_error_bound fp b c hvb
  calc
    |NumStability.fl_recursiveSum fp b c - ∑ j : Fin b, e j| =
        |(NumStability.fl_recursiveSum fp b c - ∑ j : Fin b, c j) +
          ((∑ j : Fin b, c j) - ∑ j : Fin b, e j)| := by ring
    _ ≤ |NumStability.fl_recursiveSum fp b c - ∑ j : Fin b, c j| +
          |(∑ j : Fin b, c j) - ∑ j : Fin b, e j| := abs_add_le _ _
    _ ≤ NumStability.gamma fp (b - 1) * (∑ j : Fin b, |c j|) +
          NumStability.gamma fp k * (∑ j : Fin b, m j) :=
      add_le_add hfl heSum
    _ ≤ NumStability.gamma fp (b - 1) *
          ((1 + NumStability.gamma fp k) * ∑ j : Fin b, m j) +
          NumStability.gamma fp k * ∑ j : Fin b, m j :=
      add_le_add (mul_le_mul_of_nonneg_left hcSum hg0) le_rfl
    _ = (NumStability.gamma fp k + NumStability.gamma fp (b - 1) +
          NumStability.gamma fp k * NumStability.gamma fp (b - 1)) *
          ∑ j : Fin b, m j := by ring
    _ ≤ NumStability.gamma fp (k + (b - 1)) * ∑ j : Fin b, m j :=
      mul_le_mul_of_nonneg_right
        (NumStability.gamma_sum_le fp k (b - 1) hv) hmSum

private theorem superblock_forward (b : ℕ) (_hb : 0 < b)
    (fp : NumStability.FPModel) :
    ∀ levels : ℕ, ∀ v : Fin (b ^ levels) → ℝ,
      NumStability.gammaValid fp (levels * (b - 1)) →
      |superblockSum fp b levels v - ∑ i : Fin (b ^ levels), v i| ≤
        NumStability.gamma fp (levels * (b - 1)) *
          ∑ i : Fin (b ^ levels), |v i| := by
  intro levels
  induction levels with
  | zero =>
      intro v _
      simp [superblockSum, NumStability.gamma]
  | succ levels ih =>
      intro v hv
      let c : Fin b → ℝ := fun j =>
        superblockSum fp b levels (fun i => v (blockIndex b levels j i))
      let e : Fin b → ℝ := fun j =>
        ∑ i : Fin (b ^ levels), v (blockIndex b levels j i)
      let m : Fin b → ℝ := fun j =>
        ∑ i : Fin (b ^ levels), |v (blockIndex b levels j i)|
      have hvk : NumStability.gammaValid fp (levels * (b - 1)) :=
        NumStability.gammaValid_mono fp
          (by rw [Nat.succ_mul]; exact Nat.le_add_right _ _)
          hv
      have hcomp :
          |NumStability.fl_recursiveSum fp b c - ∑ j : Fin b, e j| ≤
            NumStability.gamma fp (levels * (b - 1) + (b - 1)) *
              ∑ j : Fin b, m j := by
        apply recursive_composition_bound fp b (levels * (b - 1)) c e m
        · intro j; exact Finset.sum_nonneg (by intro i _; exact abs_nonneg _)
        · intro j; exact Finset.abs_sum_le_sum_abs _ _
        · intro j; exact ih _ hvk
        · simpa [Nat.succ_mul] using hv
      have heq : (∑ j : Fin b, e j) =
          ∑ i : Fin (b ^ (levels + 1)), v i := sum_blockIndex b levels v
      have hmq : (∑ j : Fin b, m j) =
          ∑ i : Fin (b ^ (levels + 1)), |v i| :=
        sum_blockIndex b levels (fun i => |v i|)
      simpa only [superblockSum, Nat.succ_mul, c, e, m, heq, hmq] using hcomp

private theorem integral_block_optimal (t b : ℕ) (ht : 0 < t) (hb : 0 < b)
    (factors : Fin t → ℕ) (hf : ∀ i, 0 < factors i)
    (hprod : (∏ i : Fin t, factors i) = b ^ t) :
    t * (b - 1) ≤ ∑ i : Fin t, (factors i - 1) := by
  have hgm :
      (∏ i : Fin t, (factors i : ℝ)) ^ (t : ℝ)⁻¹ ≤
        (∑ i : Fin t, (factors i : ℝ)) / (t : ℝ) := by
    simpa [Finset.sum_const, Finset.card_fin] using
      (Real.geom_mean_le_arith_mean
        (Finset.univ : Finset (Fin t))
        (fun _ => (1 : ℝ)) (fun i => (factors i : ℝ))
        (by intro i _; norm_num)
        (by simpa using (Nat.cast_pos.mpr ht : (0 : ℝ) < t))
        (by intro i _; exact Nat.cast_nonneg _))
  have hprodR : (∏ i : Fin t, (factors i : ℝ)) = (b : ℝ) ^ t := by
    simpa using congrArg (fun n : ℕ => (n : ℝ)) hprod
  rw [hprodR, Real.pow_rpow_inv_natCast (Nat.cast_nonneg _) (Nat.ne_of_gt ht)] at hgm
  have htR : (0 : ℝ) < t := Nat.cast_pos.mpr ht
  have hsumR : (t : ℝ) * (b : ℝ) ≤ ∑ i : Fin t, (factors i : ℝ) := by
    simpa [mul_comm] using (le_div_iff₀ htR).mp hgm
  have hsumEq : (∑ i : Fin t, (factors i : ℝ)) =
      (∑ i : Fin t, ((factors i - 1 : ℕ) : ℝ)) + t := by
    calc
      (∑ i : Fin t, (factors i : ℝ)) =
          ∑ i : Fin t, (((factors i - 1 : ℕ) : ℝ) + 1) := by
        apply Finset.sum_congr rfl
        intro i _
        have hi : factors i - 1 + 1 = factors i := Nat.sub_add_cancel (hf i)
        exact_mod_cast hi.symm
      _ = (∑ i : Fin t, ((factors i - 1 : ℕ) : ℝ)) + t := by simp [Finset.sum_add_distrib]
  have hcounterR : (t : ℝ) * ((b - 1 : ℕ) : ℝ) ≤
      ∑ i : Fin t, ((factors i - 1 : ℕ) : ℝ) := by
    have hbEq : ((b - 1 : ℕ) : ℝ) + 1 = (b : ℝ) := by
      exact_mod_cast Nat.sub_add_cancel hb
    rw [hsumEq] at hsumR
    nlinarith
  exact_mod_cast hcounterR


/-- Castaldo–Whaley–Chronopoulos, Proposition 3.1, for positive integral
equal blocking factors. The abstract standard relative-error model excludes
overflow and underflow; `gammaValid` is the paper's `t(b-1)u < 1` guard. -/
theorem target :
    ∀ (t b : ℕ),
      0 < t → 0 < b →
      (∀ (fp : NumStability.FPModel),
        NumStability.gammaValid fp (t * (b - 1)) →
        ∀ v : Fin (b ^ t) → ℝ,
          |superblockSum fp b t v - ∑ i : Fin (b ^ t), v i| ≤
            NumStability.gamma fp (t * (b - 1)) *
              ∑ i : Fin (b ^ t), |v i|) ∧
      (∀ factors : Fin t → ℕ,
        (∀ i, 0 < factors i) →
        (∏ i : Fin t, factors i) = b ^ t →
        t * (b - 1) ≤ ∑ i : Fin t, (factors i - 1)) ∧
      (∏ _i : Fin t, b) = b ^ t ∧
      (∑ _i : Fin t, (b - 1)) = t * (b - 1) := by
  intro t b ht hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro fp hv v
    exact superblock_forward b hb fp t v hv
  · intro factors hf hprod
    exact integral_block_optimal t b ht hb factors hf hprod
  · simp
  · simp [Finset.sum_const]

end HighamBenchCandidate
