import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LinearSystems.LU.NonsymmetricPositiveDefinite.Basic
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# CholeskyNonsym (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.Cholesky.CholeskyNonsym`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and
their users. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

open scoped BigOperators

namespace NumStability

/-- A full-range sum equals the truncated sum when the summand vanishes at
    and beyond index `k`. -/
private lemma sum_zero_off_lt {n k : ℕ} (hk : k ≤ n) (g : Fin n → ℝ)
    (hg : ∀ i : Fin n, k ≤ i.val → g i = 0) :
    ∑ i : Fin n, g i = ∑ i : Fin k, g ⟨i.val, by omega⟩ := by
  have himg : Finset.image (fun (t : Fin k) => (⟨t.val, by omega⟩ : Fin n))
      Finset.univ = Finset.filter (fun j : Fin n => j.val < k) Finset.univ := by
    ext j
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨t, rfl⟩; simp
    · intro hj
      exact ⟨⟨j.val, hj⟩, Fin.ext (by simp)⟩
  have hinj : ∀ a : Fin k, a ∈ Finset.univ →
      ∀ b : Fin k, b ∈ Finset.univ →
      (⟨a.val, by omega⟩ : Fin n) = ⟨b.val, by omega⟩ → a = b :=
    fun a _ b _ hab => Fin.ext (by simp only [Fin.mk.injEq] at hab; exact hab)
  rw [show ∑ i : Fin k, g ⟨i.val, by omega⟩ =
      ∑ j ∈ Finset.filter (fun j : Fin n => j.val < k) Finset.univ, g j from by
    rw [← himg, Finset.sum_image hinj]]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i _ hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Nat.not_lt] at hi
  exact hg i hi

/-- **Zero-padding preserves the quadratic form**: the full-matrix
quadratic form of a zero-padded vector equals the leading-principal-block
quadratic form of the original vector.  Shared engine for the
leading-principal transfer lemmas and the interlacing lower bound. -/
lemma quadForm_zero_pad_eq {n : ℕ} (M : Fin n → Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n) (y : Fin k → ℝ) :
    ∑ i : Fin n, ∑ j : Fin n,
      (if h : i.val < k then y ⟨i.val, h⟩ else 0) * M i j *
        (if h : j.val < k then y ⟨j.val, h⟩ else 0) =
    ∑ i : Fin k, ∑ j : Fin k,
      y i * M ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ * y j := by
  have houter : ∑ i : Fin n, ∑ j : Fin n,
      (if h : i.val < k then y ⟨i.val, h⟩ else 0) * M i j *
        (if h : j.val < k then y ⟨j.val, h⟩ else 0) =
      ∑ i : Fin k, ∑ j : Fin n,
        y i * M ⟨i.val, by omega⟩ j *
          (if h : j.val < k then y ⟨j.val, h⟩ else 0) := by
    rw [sum_zero_off_lt hk _ (fun i hi => by
      apply Finset.sum_eq_zero
      intro j _
      rw [dif_neg (Nat.not_lt.mpr hi), zero_mul, zero_mul])]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [dif_pos i.isLt]
  rw [houter]
  apply Finset.sum_congr rfl
  intro i _
  rw [sum_zero_off_lt hk _ (fun j hj => by
    rw [dif_neg (Nat.not_lt.mpr hj), mul_zero])]
  apply Finset.sum_congr rfl
  intro j _
  rw [dif_pos j.isLt]

/-- Zero-padding preserves the squared Euclidean norm. -/
lemma sum_sq_zero_pad_eq {n : ℕ} (k : ℕ) (hk : k ≤ n) (y : Fin k → ℝ) :
    ∑ i : Fin n, (if h : i.val < k then y ⟨i.val, h⟩ else 0) ^ 2 =
      ∑ i : Fin k, y i ^ 2 := by
  rw [sum_zero_off_lt hk _ (fun i hi => by
    rw [dif_neg (Nat.not_lt.mpr hi)]; ring)]
  apply Finset.sum_congr rfl
  intro i _
  rw [dif_pos i.isLt]

/-- Leading principal submatrices of a nonsymmetric positive definite matrix
    are nonsymmetric positive definite (Higham §10.4 prose; zero-pad the
    test vector). -/
lemma nonsymPosDef_leading_principal {n : ℕ} {A : Fin n → Fin n → ℝ}
    (hA : IsNonsymPosDef n A) (k : ℕ) (hk : k ≤ n) :
    IsNonsymPosDef k (fun i j => A ⟨i.val, by omega⟩ ⟨j.val, by omega⟩) := by
  intro y hy
  have hxval : ∀ i : Fin k,
      (fun i : Fin n => if h : i.val < k then y ⟨i.val, h⟩ else 0)
        ⟨i.val, by omega⟩ = y i := by
    intro i
    simp [i.isLt]
  set x : Fin n → ℝ := fun i => if h : i.val < k then y ⟨i.val, h⟩ else 0
    with hx_def
  have hx : ∃ i, x i ≠ 0 := by
    obtain ⟨i, hi⟩ := hy
    refine ⟨⟨i.val, by omega⟩, ?_⟩
    rw [hx_def]
    simpa [i.isLt] using hi
  have h := hA x hx
  have houter : ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j =
      ∑ i : Fin k, ∑ j : Fin n, y i * A ⟨i.val, by omega⟩ j * x j := by
    rw [sum_zero_off_lt hk _ (fun i hi => by
      apply Finset.sum_eq_zero
      intro j _
      rw [hx_def]
      simp [Nat.not_lt.mpr hi])]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hxval i]
  have hinner : ∀ i : Fin k,
      ∑ j : Fin n, y i * A ⟨i.val, by omega⟩ j * x j =
      ∑ j : Fin k, y i * A ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ * y j := by
    intro i
    rw [sum_zero_off_lt hk _ (fun j hj => by
      rw [hx_def]
      simp [Nat.not_lt.mpr hj])]
    apply Finset.sum_congr rfl
    intro j _
    rw [hxval j]
  calc (0:ℝ) < ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j := h
    _ = ∑ i : Fin k, ∑ j : Fin k,
        y i * A ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ * y j := by
        rw [houter]
        exact Finset.sum_congr rfl fun i _ => hinner i

end NumStability
