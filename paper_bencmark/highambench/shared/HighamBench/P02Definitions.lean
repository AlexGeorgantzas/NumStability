import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace HighamBench

open scoped BigOperators

structure StandardAddModel where
  u : ℝ
  u_nonneg : 0 ≤ u
  fl_add : ℝ → ℝ → ℝ
  fl_add_zero : ∀ x : ℝ, fl_add 0 x = x
  model_add :
    ∀ x y : ℝ, ∃ δ : ℝ,
      |δ| ≤ u ∧
      fl_add x y = (x + y) * (1 + δ)

noncomputable def gamma (u : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * u) / (1 - (n : ℝ) * u)

def GammaValid (u : ℝ) (n : ℕ) : Prop :=
  (n : ℝ) * u < 1

noncomputable def recursiveSum (flAdd : ℝ → ℝ → ℝ) :
    (n : ℕ) → (Fin n → ℝ) → ℝ
  | 0, _ => 0
  | n + 1, v =>
      if h : n = 0 then
        v ⟨0, by omega⟩
      else
        flAdd
          (recursiveSum flAdd n (fun i => v i.castSucc))
          (v (Fin.last n))

structure ErrorFreeAddModel extends StandardAddModel where
  twoSum : ℝ → ℝ → ℝ × ℝ
  twoSum_high :
    ∀ a b : ℝ, (twoSum a b).1 = fl_add a b
  twoSum_exact :
    ∀ a b : ℝ, (twoSum a b).1 + (twoSum a b).2 = a + b
  twoSum_low_le :
    ∀ a b : ℝ, |(twoSum a b).2| ≤ u * |(twoSum a b).1|

noncomputable def twoSumPrefix (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (k : ℕ) (hk : k ≤ n) : ℝ :=
  Fin.foldl k
    (fun s i =>
      (fp.twoSum s
        (v ⟨i.val + 1,
          Nat.succ_lt_succ (Nat.lt_of_lt_of_le i.isLt hk)⟩)).1)
    (v ⟨0, Nat.succ_pos n⟩)

noncomputable def twoSumCorrection (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (i : Fin n) : ℝ :=
  (fp.twoSum
    (twoSumPrefix fp v i.val (Nat.le_of_lt i.isLt))
    (v ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)).2

noncomputable def vecSum (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  Fin.lastCases
    (twoSumPrefix fp v n (Nat.le_refl n))
    (twoSumCorrection fp v)

noncomputable def iteratedVecSum (fp : ErrorFreeAddModel) {n : ℕ}
    (k : ℕ) (v : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  match k with
  | 0 => v
  | k + 1 => vecSum fp (iteratedVecSum fp k v)

noncomputable def sumK (fp : ErrorFreeAddModel) {n : ℕ}
    (K : ℕ) (v : Fin (n + 1) → ℝ) : ℝ :=
  recursiveSum fp.fl_add (n + 1) (iteratedVecSum fp (K - 1) v)

noncomputable def sum2 (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) : ℝ :=
  sumK fp 2 v

structure ErrorFreeDotModel extends ErrorFreeAddModel where
  twoProduct : ℝ → ℝ → ℝ × ℝ
  twoProduct_exact :
    ∀ a b : ℝ, (twoProduct a b).1 + (twoProduct a b).2 = a * b
  twoProduct_low_le_exact :
    ∀ a b : ℝ, |(twoProduct a b).2| ≤ u * |a * b|

noncomputable def exactDot {n : ℕ} (x y : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i : Fin (n + 1), x i * y i

noncomputable def dotMagnitude {n : ℕ} (x y : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i : Fin (n + 1), |x i| * |y i|

noncomputable def dotKTransform (fp : ErrorFreeDotModel) {n : ℕ}
    (x y : Fin (n + 1) → ℝ) : Fin ((2 * n + 1) + 1) → ℝ :=
  fun j =>
    Fin.addCases
      (fun i : Fin (n + 1) => (fp.twoProduct (x i) (y i)).2)
      (vecSum fp.toErrorFreeAddModel
        (fun i : Fin (n + 1) => (fp.twoProduct (x i) (y i)).1))
      (Fin.cast (by omega) j)

noncomputable def dotK (fp : ErrorFreeDotModel) {n : ℕ}
    (K : ℕ) (x y : Fin (n + 1) → ℝ) : ℝ :=
  sumK fp.toErrorFreeAddModel (K - 1) (dotKTransform fp x y)

end HighamBench
