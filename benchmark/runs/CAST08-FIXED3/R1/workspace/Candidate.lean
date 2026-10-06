import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.Summation.Recursive.Core
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Logic.Equiv.Fin.Basic

namespace HighamBenchCandidate

open NumStability
open scoped BigOperators

/-- Position `i` of block `j` in superblock `s`, in the original vector order. -/
def superblockIndex (b m : ℕ) (s j : Fin m) (i : Fin b) : Fin (b * m * m) :=
  ⟨(s.val * m + j.val) * b + i.val, by
    have hblock : s.val * m + j.val < m * m := by
      have hfirst : s.val * m + j.val < (s.val + 1) * m := by
        nlinarith [j.isLt]
      exact lt_of_lt_of_le hfirst
        (Nat.mul_le_mul_right m (Nat.succ_le_of_lt s.isLt))
    have hfirst : (s.val * m + j.val) * b + i.val <
        (s.val * m + j.val + 1) * b := by
      nlinarith [i.isLt]
    calc
      (s.val * m + j.val) * b + i.val <
          (s.val * m + j.val + 1) * b := hfirst
      _ ≤ (m * m) * b :=
        Nat.mul_le_mul_right b (Nat.succ_le_of_lt hblock)
      _ = b * m * m := by ring⟩

/-- Figure 3.1(b): rounded length-`b` inner dots, then `m` block totals per
superblock, then `m` superblock totals. Both outer levels start from zero. -/
noncomputable def fixedThreeLevelDot (fp : FPModel) (b m : ℕ)
    (x y : Fin (b * m * m) → ℝ) : ℝ :=
  fl_recursiveSum fp m (fun s =>
    fl_recursiveSum fp m (fun j =>
      fl_dotProduct fp b
        (fun i => x (superblockIndex b m s j i))
        (fun i => y (superblockIndex b m s j i))))

private def finCastEquiv {n k : ℕ} (h : n = k) : Fin n ≃ Fin k where
  toFun i := i.cast h
  invFun i := i.cast h.symm
  left_inv i := Fin.ext rfl
  right_inv i := Fin.ext rfl

private def threeIndexEquiv (b m : ℕ) :
    (Fin m × (Fin m × Fin b)) ≃ Fin (b * m * m) :=
  (Equiv.prodCongr (Equiv.refl (Fin m)) finProdFinEquiv).trans
    (finProdFinEquiv.trans (finCastEquiv (by ring)))

private theorem threeIndexEquiv_apply (b m : ℕ) (s j : Fin m) (i : Fin b) :
    threeIndexEquiv b m (s, (j, i)) = superblockIndex b m s j i := by
  apply Fin.ext
  simp [threeIndexEquiv, superblockIndex, finProdFinEquiv, finCastEquiv]
  ring

private theorem liftRecursive {α : Type} [Fintype α]
    (fp : FPModel) (n p : ℕ) (v : Fin n → ℝ) (a : Fin n → α → ℝ)
    (hvalid : gammaValid fp (p + (n - 1)))
    (hv : ∀ i : Fin n, ∃ η : α → ℝ,
      (∀ t, |η t| ≤ gamma fp p) ∧
        v i = ∑ t : α, a i t * (1 + η t)) :
    ∃ μ : Fin n → α → ℝ,
      (∀ i t, |μ i t| ≤ gamma fp (p + (n - 1))) ∧
        fl_recursiveSum fp n v =
          ∑ i : Fin n, ∑ t : α, a i t * (1 + μ i t) := by
  classical
  have hq : gammaValid fp (n - 1) :=
    gammaValid_mono fp (by omega) hvalid
  obtain ⟨θ, hθ, hsum⟩ := recursiveSum_backward_error fp n v hq
  let η : Fin n → α → ℝ := fun i => Classical.choose (hv i)
  have hη (i : Fin n) :
      (∀ t, |η i t| ≤ gamma fp p) ∧
        v i = ∑ t : α, a i t * (1 + η i t) :=
    Classical.choose_spec (hv i)
  let μ : Fin n → α → ℝ := fun i t =>
    Classical.choose
      (gamma_mul fp p (n - 1) (η i t) (θ i)
        ((hη i).1 t) (hθ i) hvalid)
  have hμ (i : Fin n) (t : α) :
      |μ i t| ≤ gamma fp (p + (n - 1)) ∧
        (1 + η i t) * (1 + θ i) = 1 + μ i t :=
    Classical.choose_spec
      (gamma_mul fp p (n - 1) (η i t) (θ i)
        ((hη i).1 t) (hθ i) hvalid)
  refine ⟨μ, (fun i t => (hμ i t).1), ?_⟩
  calc
    fl_recursiveSum fp n v = ∑ i : Fin n, v i * (1 + θ i) := hsum
    _ = ∑ i : Fin n, ∑ t : α,
          a i t * (1 + η i t) * (1 + θ i) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [(hη i).2, Finset.sum_mul]
    _ = ∑ i : Fin n, ∑ t : α, a i t * (1 + μ i t) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro t _
      calc
        a i t * (1 + η i t) * (1 + θ i) =
            a i t * ((1 + η i t) * (1 + θ i)) := by ring
        _ = a i t * (1 + μ i t) := by rw [(hμ i t).2]

private theorem sum_three_eq_flat (b m : ℕ)
    (f : Fin (b * m * m) → ℝ) :
    (∑ s : Fin m, ∑ j : Fin m, ∑ i : Fin b,
      f (superblockIndex b m s j i)) =
      ∑ k : Fin (b * m * m), f k := by
  classical
  calc
    (∑ s : Fin m, ∑ j : Fin m, ∑ i : Fin b,
        f (superblockIndex b m s j i)) =
        ∑ p : Fin m × (Fin m × Fin b),
          f (superblockIndex b m p.1 p.2.1 p.2.2) := by
            simp only [Fintype.sum_prod_type]
    _ = ∑ k : Fin (b * m * m), f k := by
      apply Fintype.sum_equiv (threeIndexEquiv b m)
      rintro ⟨s, ⟨j, i⟩⟩
      exact congrArg f (threeIndexEquiv_apply b m s j i).symm

private theorem nested_forward_bound {α : Type} [Fintype α]
    (n : ℕ) (a μ : Fin n → α → ℝ) (B : ℝ)
    (hμ : ∀ i t, |μ i t| ≤ B) :
    |(∑ i : Fin n, ∑ t : α, a i t * (1 + μ i t)) -
        ∑ i : Fin n, ∑ t : α, a i t| ≤
      B * ∑ i : Fin n, ∑ t : α, |a i t| := by
  classical
  have hdiff :
      (∑ i : Fin n, ∑ t : α, a i t * (1 + μ i t)) -
          (∑ i : Fin n, ∑ t : α, a i t) =
        ∑ i : Fin n, ∑ t : α, a i t * μ i t := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [hdiff]
  calc
    |∑ i : Fin n, ∑ t : α, a i t * μ i t| ≤
        ∑ i : Fin n, |∑ t : α, a i t * μ i t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n, ∑ t : α, |a i t * μ i t| := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n, ∑ t : α, B * |a i t| := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro t _
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hμ i t) (abs_nonneg _)
    _ = B * ∑ i : Fin n, ∑ t : α, |a i t| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]

/-- Castaldo–Whaley–Chronopoulos, §3.1, fixed three-level superblock bound.
`FPModel` supplies the paper's relative-error laws in the regime without
overflow or underflow. -/
theorem target (fp : FPModel) (b m : ℕ) (hb : 0 < b) (hm : 0 < m)
    (x y : Fin (b * m * m) → ℝ)
    (hvalid : gammaValid fp (b + 2 * (m - 1))) :
    |fixedThreeLevelDot fp b m x y -
      ∑ k : Fin (b * m * m), x k * y k| ≤
      gamma fp (b + 2 * (m - 1)) *
        ∑ k : Fin (b * m * m), |x k * y k| := by
  classical
  have hfirst : gammaValid fp (b + (m - 1)) :=
    gammaValid_mono fp (by omega) hvalid
  have hbvalid : gammaValid fp b :=
    gammaValid_mono fp (by omega) hvalid
  have htotal : gammaValid fp ((b + (m - 1)) + (m - 1)) := by
    convert hvalid using 1 <;> omega
  let a : Fin m → Fin m → Fin b → ℝ := fun s j i =>
    x (superblockIndex b m s j i) * y (superblockIndex b m s j i)
  let inner : Fin m → Fin m → ℝ := fun s j =>
    fl_dotProduct fp b
      (fun i => x (superblockIndex b m s j i))
      (fun i => y (superblockIndex b m s j i))
  let middle : Fin m → ℝ := fun s => fl_recursiveSum fp m (inner s)
  let ap : Fin m → (Fin m × Fin b) → ℝ :=
    fun s p => a s p.1 p.2
  have hinner (s j : Fin m) : ∃ η : Fin b → ℝ,
      (∀ i, |η i| ≤ gamma fp b) ∧
        inner s j = ∑ i : Fin b, a s j i * (1 + η i) := by
    simpa [inner, a] using
      (dotProduct_backward_error fp b
        (fun i => x (superblockIndex b m s j i))
        (fun i => y (superblockIndex b m s j i)) hbvalid)
  have hmid (s : Fin m) : ∃ η : Fin m → Fin b → ℝ,
      (∀ j i, |η j i| ≤ gamma fp (b + (m - 1))) ∧
        middle s = ∑ j : Fin m, ∑ i : Fin b,
          a s j i * (1 + η j i) := by
    simpa [middle] using
      (liftRecursive fp m b (inner s) (a s) hfirst (hinner s))
  have houter (s : Fin m) : ∃ η : Fin m × Fin b → ℝ,
      (∀ p, |η p| ≤ gamma fp (b + (m - 1))) ∧
        middle s = ∑ p : Fin m × Fin b,
          ap s p * (1 + η p) := by
    obtain ⟨η, hη, heq⟩ := hmid s
    refine ⟨fun p => η p.1 p.2, ?_, ?_⟩
    · rintro ⟨j, i⟩
      exact hη j i
    · simpa only [Fintype.sum_prod_type, ap] using heq
  obtain ⟨μ, hμ, hrepr⟩ :=
    liftRecursive fp m (b + (m - 1)) middle ap htotal houter
  have hfl : fixedThreeLevelDot fp b m x y =
      ∑ s : Fin m, ∑ p : Fin m × Fin b,
        ap s p * (1 + μ s p) := by
    simpa [fixedThreeLevelDot, middle, inner] using hrepr
  have hexact : (∑ s : Fin m, ∑ p : Fin m × Fin b, ap s p) =
      ∑ k : Fin (b * m * m), x k * y k := by
    simpa only [Fintype.sum_prod_type, ap, a] using
      (sum_three_eq_flat b m (fun k => x k * y k))
  have habs : (∑ s : Fin m, ∑ p : Fin m × Fin b, |ap s p|) =
      ∑ k : Fin (b * m * m), |x k * y k| := by
    simpa only [Fintype.sum_prod_type, ap, a] using
      (sum_three_eq_flat b m (fun k => |x k * y k|))
  calc
    |fixedThreeLevelDot fp b m x y -
        ∑ k : Fin (b * m * m), x k * y k| =
      |(∑ s : Fin m, ∑ p : Fin m × Fin b,
          ap s p * (1 + μ s p)) -
        ∑ s : Fin m, ∑ p : Fin m × Fin b, ap s p| := by
          rw [hfl, ← hexact]
    _ ≤ gamma fp (b + 2 * (m - 1)) *
        (∑ s : Fin m, ∑ p : Fin m × Fin b, |ap s p|) := by
          simpa only [show (b + (m - 1)) + (m - 1) =
              b + 2 * (m - 1) by omega] using
            (nested_forward_bound m ap μ
              (gamma fp ((b + (m - 1)) + (m - 1))) hμ)
    _ = gamma fp (b + 2 * (m - 1)) *
        ∑ k : Fin (b * m * m), |x k * y k| := by rw [habs]

end HighamBenchCandidate
