import NumStability.Algorithms.Summation.Recursive.Core

namespace HighamBenchCandidate

open NumStability
open scoped BigOperators

/-- Equal contiguous blocks at each level, with `B` child totals combined
left to right. Level zero is a single already computed input product. -/
noncomputable def superblockSum (fp : FPModel) (B : ℕ) :
    (t : ℕ) → (Fin (B ^ t) → ℝ) → ℝ
  | 0, v => v ⟨0, by simp⟩
  | t + 1, v =>
      fl_recursiveSum fp B (fun j =>
        superblockSum fp B t (fun i =>
          v ⟨j.val * B ^ t + i.val, by
            have hj := j.isLt
            have hi := i.isLt
            rw [pow_succ]
            calc
              j.val * B ^ t + i.val < j.val * B ^ t + B ^ t :=
                Nat.add_lt_add_left hi _
              _ = (j.val + 1) * B ^ t := by ring
              _ ≤ B * B ^ t :=
                Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hj)
              _ = B ^ t * B := Nat.mul_comm _ _⟩))

/-- The equal-block superblock dot product: one rounded multiplication
per input, followed by `t` levels of rounded left-to-right sums. -/
noncomputable def superblockDot (fp : FPModel) (t B N : ℕ)
    (hN : B ^ t = N) (x y : Fin N → ℝ) : ℝ :=
  superblockSum fp B t (fun i =>
    fp.fl_mul (x (Fin.cast hN i)) (y (Fin.cast hN i)))

private def blockEquiv (B t : ℕ) :
    Fin B × Fin (B ^ t) ≃ Fin (B ^ (t + 1)) :=
  (finProdFinEquiv (m := B) (n := B ^ t)).trans
    (Fin.castOrderIso (by simp [pow_succ, Nat.mul_comm] :
      B * B ^ t = B ^ (t + 1))).toEquiv

private theorem blockEquiv_apply (B t : ℕ) (j : Fin B) (i : Fin (B ^ t)) :
    blockEquiv B t (j, i) =
      ⟨j.val * B ^ t + i.val, by
        have hj := j.isLt
        have hi := i.isLt
        rw [pow_succ]
        calc
          j.val * B ^ t + i.val < j.val * B ^ t + B ^ t :=
            Nat.add_lt_add_left hi _
          _ = (j.val + 1) * B ^ t := by ring
          _ ≤ B * B ^ t := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hj)
          _ = B ^ t * B := Nat.mul_comm _ _⟩ := by
  apply Fin.ext
  simp [blockEquiv, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

private theorem sum_blocks (B t : ℕ) (v : Fin (B ^ (t + 1)) → ℝ) :
    (∑ j : Fin B, ∑ i : Fin (B ^ t),
      v ⟨j.val * B ^ t + i.val, by
        have hj := j.isLt
        have hi := i.isLt
        rw [pow_succ]
        calc
          j.val * B ^ t + i.val < j.val * B ^ t + B ^ t :=
            Nat.add_lt_add_left hi _
          _ = (j.val + 1) * B ^ t := by ring
          _ ≤ B * B ^ t := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hj)
          _ = B ^ t * B := Nat.mul_comm _ _⟩) = ∑ k, v k := by
  calc
    _ = ∑ p : Fin B × Fin (B ^ t), v (blockEquiv B t p) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg v (blockEquiv_apply B t j i).symm
    _ = ∑ k, v k := Equiv.sum_comp (blockEquiv B t) v

private theorem superblockSum_backward_error (fp : FPModel) (B : ℕ) :
    ∀ (t : ℕ) (v : Fin (B ^ t) → ℝ),
      gammaValid fp (t * (B - 1)) →
      ∃ η : Fin (B ^ t) → ℝ,
        (∀ i, |η i| ≤ gamma fp (t * (B - 1))) ∧
          superblockSum fp B t v = ∑ i, v i * (1 + η i) := by
  intro t
  induction t with
  | zero =>
      intro v _
      refine ⟨fun _ => 0, ?_, ?_⟩
      · intro i
        simp [gamma]
      · simp [superblockSum]
  | succ t ih =>
      intro v hvalid
      let d := B - 1
      have hinner : gammaValid fp (t * d) :=
        gammaValid_mono fp (by simp [Nat.succ_mul, d]) hvalid
      have houter : gammaValid fp d :=
        gammaValid_mono fp (by simp [Nat.succ_mul, d]) hvalid
      have hcombined : gammaValid fp (t * d + d) := by
        simpa [Nat.succ_mul, d] using hvalid
      let e := blockEquiv B t
      let block (j : Fin B) (i : Fin (B ^ t)) : ℝ := v (e (j, i))
      have hdef : superblockSum fp B (t + 1) v =
          fl_recursiveSum fp B (fun j => superblockSum fp B t (block j)) := by
        change fl_recursiveSum fp B (fun j =>
          superblockSum fp B t (fun i => v ⟨j.val * B ^ t + i.val, by
            have hj := j.isLt
            have hi := i.isLt
            rw [pow_succ]
            calc
              j.val * B ^ t + i.val < j.val * B ^ t + B ^ t :=
                Nat.add_lt_add_left hi _
              _ = (j.val + 1) * B ^ t := by ring
              _ ≤ B * B ^ t := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hj)
              _ = B ^ t * B := Nat.mul_comm _ _⟩)) = _
        congr 1
        funext j
        congr 1
        funext i
        exact congrArg v (blockEquiv_apply B t j i).symm
      let z (j : Fin B) := superblockSum fp B t (block j)
      obtain ⟨α, hα, houterEq⟩ := recursiveSum_backward_error fp B z houter
      let ηInner (j : Fin B) : Fin (B ^ t) → ℝ :=
        Classical.choose (ih (block j) hinner)
      have hηInner (j : Fin B) :
          (∀ i, |ηInner j i| ≤ gamma fp (t * d)) ∧
            z j = ∑ i, block j i * (1 + ηInner j i) := by
        exact Classical.choose_spec (ih (block j) hinner)
      let ηBlock (j : Fin B) (i : Fin (B ^ t)) : ℝ :=
        Classical.choose (gamma_mul fp (t * d) d
          (ηInner j i) (α j) ((hηInner j).1 i) (hα j) hcombined)
      have hηBlock (j : Fin B) (i : Fin (B ^ t)) :
          |ηBlock j i| ≤ gamma fp (t * d + d) ∧
            (1 + ηInner j i) * (1 + α j) = 1 + ηBlock j i := by
        exact Classical.choose_spec (gamma_mul fp (t * d) d
          (ηInner j i) (α j) ((hηInner j).1 i) (hα j) hcombined)
      let η (k : Fin (B ^ (t + 1))) : ℝ :=
        ηBlock (e.symm k).1 (e.symm k).2
      refine ⟨η, ?_, ?_⟩
      · intro k
        simpa [η, Nat.succ_mul, d] using
          (hηBlock (e.symm k).1 (e.symm k).2).1
      · calc
          superblockSum fp B (t + 1) v = fl_recursiveSum fp B z := hdef
          _ = ∑ j, z j * (1 + α j) := houterEq
          _ = ∑ j : Fin B, ∑ i : Fin (B ^ t),
                block j i * (1 + ηBlock j i) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [(hηInner j).2, Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro i _
              calc
                block j i * (1 + ηInner j i) * (1 + α j) =
                    block j i * ((1 + ηInner j i) * (1 + α j)) := by ring
                _ = block j i * (1 + ηBlock j i) := by rw [(hηBlock j i).2]
          _ = ∑ k, v k * (1 + η k) := by
              calc
                _ = ∑ p : Fin B × Fin (B ^ t),
                      v (e p) * (1 + η (e p)) := by
                    rw [Fintype.sum_prod_type]
                    apply Finset.sum_congr rfl
                    intro j _
                    apply Finset.sum_congr rfl
                    intro i _
                    simp [block, η, e]
                _ = ∑ k, v k * (1 + η k) :=
                  Equiv.sum_comp e (fun k => v k * (1 + η k))

private theorem superblockDot_core (fp : FPModel) (t B : ℕ)
    (x y : Fin (B ^ t) → ℝ)
    (hvalid : gammaValid fp (t * (B - 1) + 1)) :
    |superblockSum fp B t (fun i => fp.fl_mul (x i) (y i)) -
        ∑ i, x i * y i| ≤
      gamma fp (t * (B - 1) + 1) * ∑ i, |x i * y i| := by
  let d := B - 1
  let k := t * d
  let z (i : Fin (B ^ t)) := fp.fl_mul (x i) (y i)
  have hinner : gammaValid fp k :=
    gammaValid_mono fp (by change t * (B - 1) ≤ t * (B - 1) + 1; omega) hvalid
  have hcombined : gammaValid fp (1 + k) := by
    simpa [k, d, add_comm] using hvalid
  have h1 : gammaValid fp 1 :=
    gammaValid_mono fp (by omega) hcombined
  obtain ⟨η, hη, hsum⟩ :=
    superblockSum_backward_error fp B t z (by simpa [k, d] using hinner)
  let δ (i : Fin (B ^ t)) : ℝ := Classical.choose (fp.model_mul (x i) (y i))
  have hδ (i : Fin (B ^ t)) :
      |δ i| ≤ fp.u ∧ z i = x i * y i * (1 + δ i) :=
    Classical.choose_spec (fp.model_mul (x i) (y i))
  let θ (i : Fin (B ^ t)) : ℝ :=
    Classical.choose (gamma_mul fp 1 k (δ i) (η i)
      ((hδ i).1.trans (u_le_gamma fp one_pos h1))
      (by simpa [k, d] using hη i) hcombined)
  have hθ (i : Fin (B ^ t)) :
      |θ i| ≤ gamma fp (1 + k) ∧
        (1 + δ i) * (1 + η i) = 1 + θ i := by
    exact Classical.choose_spec (gamma_mul fp 1 k (δ i) (η i)
      ((hδ i).1.trans (u_le_gamma fp one_pos h1))
      (by simpa [k, d] using hη i) hcombined)
  have hrep :
      superblockSum fp B t z = ∑ i, x i * y i * (1 + θ i) := by
    rw [hsum]
    apply Finset.sum_congr rfl
    intro i _
    rw [(hδ i).2]
    calc
      x i * y i * (1 + δ i) * (1 + η i) =
          x i * y i * ((1 + δ i) * (1 + η i)) := by ring
      _ = x i * y i * (1 + θ i) := by rw [(hθ i).2]
  have hdiff :
      superblockSum fp B t z - ∑ i, x i * y i =
        ∑ i, x i * y i * θ i := by
    rw [hrep, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  change |superblockSum fp B t z - ∑ i, x i * y i| ≤ _
  rw [hdiff]
  calc
    |∑ i, x i * y i * θ i| ≤ ∑ i, |x i * y i * θ i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |x i * y i| * |θ i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul]
    _ ≤ ∑ i, |x i * y i| * gamma fp (1 + k) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hθ i).1 (abs_nonneg _)
    _ = gamma fp (t * (B - 1) + 1) * ∑ i, |x i * y i| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp [k, d, add_comm, mul_comm]

/-- Castaldo–Whaley–Chronopoulos (2008), Proposition 3.2, equation (3.2).
The paper excludes overflow and underflow and uses the standard relative-error
model represented here by `FPModel`. The mathematical equal-block hierarchy
follows Section 3 and Figure 3.2; Figure 3.1(a)'s printed carry loop omits
level zero. -/
theorem target :
    ∀ (fp : FPModel) (t B N : ℕ)
      (ht : 0 < t) (hB : 0 < B) (hN : B ^ t = N)
      (x y : Fin N → ℝ),
      gammaValid fp (t * (B - 1) + 1) →
      |superblockDot fp t B N hN x y -
          ∑ i : Fin N, x i * y i| ≤
        gamma fp (t * (B - 1) + 1) *
          ∑ i : Fin N, |x i * y i| := by
  intro fp t B N ht hB hN x y hvalid
  let x' : Fin (B ^ t) → ℝ := fun i => x (Fin.cast hN i)
  let y' : Fin (B ^ t) → ℝ := fun i => y (Fin.cast hN i)
  have hcore := superblockDot_core fp t B x' y' hvalid
  have hsum (f : Fin N → ℝ) :
      (∑ i : Fin (B ^ t), f (Fin.cast hN i)) = ∑ i : Fin N, f i := by
    exact Equiv.sum_comp (Fin.castOrderIso hN).toEquiv f
  change |superblockDot fp t B N hN x y -
      ∑ i : Fin (B ^ t), x (Fin.cast hN i) * y (Fin.cast hN i)| ≤
    gamma fp (t * (B - 1) + 1) *
      ∑ i : Fin (B ^ t), |x (Fin.cast hN i) * y (Fin.cast hN i)| at hcore
  rw [hsum (fun i => x i * y i), hsum (fun i => |x i * y i|)] at hcore
  exact hcore

end HighamBenchCandidate
