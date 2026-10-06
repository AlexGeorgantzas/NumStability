import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Analysis.MatrixAlgebra

/-!
# NumStability Algorithms NormEstimation PNorm Duality PNormPowerMethod

Canonical destination for material split out of
`NumStability.Algorithms.PNormPowerMethod` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Ch15

open scoped BigOperators

/-- Convex-analytic subgradient predicate used in equations (15.2) and (15.5):
`g ∈ ∂f(x)` iff `f(x) + gᵀ(v-x) ≤ f(v)` for every `v`. -/
def IsSubgradient {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (x g : Fin n → ℝ) : Prop :=
  ∀ v, f x + (∑ i : Fin n, g i * (v i - x i)) ≤ f v

/-- Fixed unit vector `e₀` (used as the `dualq`/`dualp` value at the zero vector,
    Higham's "extreme point of the unit ball" convention). -/
noncomputable def e0Vec {n : ℕ} (hn : 0 < n) : Fin n → ℝ :=
  fun i => if i = ⟨0, hn⟩ then 1 else 0

lemma vecNorm2_e0 {n : ℕ} (hn : 0 < n) : vecNorm2 (e0Vec hn) = 1 := by
  unfold vecNorm2 vecNorm2Sq e0Vec
  have hsum : (∑ i : Fin n, (if i = ⟨0, hn⟩ then (1:ℝ) else 0) ^ 2) = 1 := by
    have hcongr : (∑ i : Fin n, (if i = ⟨0, hn⟩ then (1:ℝ) else 0) ^ 2)
        = ∑ i : Fin n, (if i = ⟨0, hn⟩ then (1:ℝ) else 0) := by
      apply Finset.sum_congr rfl; intro i _; split_ifs <;> norm_num
    rw [hcongr]; simp
  rw [hsum]; exact Real.sqrt_one

lemma vecNorm2_pos_of_ne {n : ℕ} (v : Fin n → ℝ) (h : ¬ v = 0) :
    0 < vecNorm2 v := by
  rcases lt_or_eq_of_le (vecNorm2_nonneg v) with hlt | heq
  · exact hlt
  · exfalso; apply h; funext i
    exact (vecNorm2_eq_zero_iff v).mp heq.symm i

/-- The `dualp = dualq` map for `p = 2`: `v ↦ v/‖v‖₂` (a fixed unit vector at
    `v = 0`).  For the Euclidean norm the dual pair is `q = 2`, and the unique
    unit-norm Hölder-equality vector is the normalized `v`. -/
noncomputable def normalize2 {n : ℕ} (hn : 0 < n) (v : Fin n → ℝ) : Fin n → ℝ :=
  if v = 0 then e0Vec hn else fun i => (vecNorm2 v)⁻¹ * v i

lemma normalize2_unit {n : ℕ} (hn : 0 < n) (v : Fin n → ℝ) :
    vecNorm2 (normalize2 hn v) = 1 := by
  unfold normalize2
  split_ifs with h
  · exact vecNorm2_e0 hn
  · exact vecNorm2_inv_smul_self_of_pos v (vecNorm2_pos_of_ne v h)

lemma normalize2_attains {n : ℕ} (hn : 0 < n) (v : Fin n → ℝ) :
    (∑ i : Fin n, normalize2 hn v i * v i) = vecNorm2 v := by
  unfold normalize2
  split_ifs with h
  · subst h
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]
    symm
    have hz : (0 : Fin n → ℝ) = (fun _ : Fin n => (0:ℝ)) := rfl
    rw [hz, vecNorm2_zero]
  · exact vecInnerProduct_inv_smul_self_eq_norm v (vecNorm2_pos_of_ne v h)

/-- Cauchy-Schwarz as the Hölder inequality for `p = q = 2` (one-sided):
    `uᵀ v ≤ ‖u‖₂ ‖v‖₂`. -/
lemma holder_two {n : ℕ} (u v : Fin n → ℝ) :
    (∑ i : Fin n, u i * v i) ≤ vecNorm2 u * vecNorm2 v :=
  le_trans (le_abs_self _) (abs_vecInnerProduct_le_vecNorm2_mul u v)

/-- The `p = 2` operator bound in the `yof`-shape:
    `‖A v‖₂ ≤ ‖A‖₂ ‖v‖₂`, with `‖A‖₂ = opNorm2 A` the exact ℓ² operator norm. -/
lemma opBound_two {n : ℕ} (A : Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
    vecNorm2 (fun i => ∑ j : Fin n, A i j * v j) ≤ opNorm2 A * vecNorm2 v := by
  simpa [matMulVec] using opNorm2Le_opNorm2 A v

/-- A finite-dimensional scalar function has directional gradient `g` at `x`
when every line through `x` has derivative `gᵀh` in direction `h`.  This is the
exact content needed for Higham's displayed gradient formula (15.3). -/
def HasDirectionalGradientAt {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (g x : Fin n → ℝ) : Prop :=
  ∀ h : Fin n → ℝ, HasDerivAt (fun t : ℝ => f (fun i => x i + t * h i))
    (∑ i : Fin n, g i * h i) 0

/-- Away from zero, the Euclidean norm has directional gradient
`x / ‖x‖₂ = normalize2 x`. -/
theorem vecNorm2_hasDirectionalGradientAt {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (hx : x ≠ 0) :
    HasDirectionalGradientAt vecNorm2 (normalize2 hn x) x := by
  unfold HasDirectionalGradientAt
  intro h
  have hsq : HasDerivAt
      (fun t : ℝ => ∑ i : Fin n, (x i + t * h i) ^ 2)
      (2 * ∑ i : Fin n, x i * h i) 0 := by
    have hterms : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        HasDerivAt (fun t : ℝ => (x i + t * h i) ^ 2) (2 * x i * h i) 0 := by
      intro i _
      have ha : HasDerivAt (fun t : ℝ => x i + t * h i) (h i) 0 := by
        have ha' := (hasDerivAt_const (x := (0 : ℝ)) (x i)).add
          ((hasDerivAt_id (𝕜 := ℝ) 0).const_mul (h i))
        convert ha' using 1
        · funext t
          simp only [Pi.add_apply, id_eq]
          ring
        · ring
      simpa using ha.fun_pow 2
    convert HasDerivAt.fun_sum hterms using 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hnormpos : 0 < vecNorm2 x := vecNorm2_pos_of_ne x hx
  have hsum_ne : (∑ i : Fin n, x i ^ 2) ≠ 0 := by
    intro hzero
    unfold vecNorm2 vecNorm2Sq at hnormpos
    rw [hzero, Real.sqrt_zero] at hnormpos
    exact (lt_irrefl 0 hnormpos)
  have hsqrtAt : HasDerivAt (fun u : ℝ => Real.sqrt u)
      (1 / (2 * Real.sqrt (∑ i : Fin n, x i ^ 2)))
      (∑ i : Fin n, (x i + 0 * h i) ^ 2) := by
    simpa using Real.hasDerivAt_sqrt hsum_ne
  have hsqrt := hsqrtAt.comp 0 hsq
  change HasDerivAt
    (fun t : ℝ => Real.sqrt (∑ i : Fin n, (x i + t * h i) ^ 2))
    (∑ i : Fin n, normalize2 hn x i * h i) 0
  convert hsqrt using 1
  unfold normalize2 vecNorm2 vecNorm2Sq
  rw [if_neg hx]
  have hsqrtpos : 0 < Real.sqrt (∑ i : Fin n, x i ^ 2) := by
    simpa [vecNorm2, vecNorm2Sq] using hnormpos
  rw [show (∑ i : Fin n,
      (Real.sqrt (∑ j : Fin n, x j ^ 2))⁻¹ * x i * h i) =
      (Real.sqrt (∑ j : Fin n, x j ^ 2))⁻¹ *
        (∑ i : Fin n, x i * h i) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring]
  field_simp [ne_of_gt hsqrtpos]

/-- A global subgradient at a differentiability point is the gradient.

This finite-dimensional line-restriction lemma is the uniqueness step behind
the singleton subdifferential in Higham's equation (15.2). -/
theorem unique_subgradient_of_directional_gradient {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (x grad g : Fin n → ℝ)
    (hgrad : HasDirectionalGradientAt f grad x)
    (hg : IsSubgradient f x g) :
    g = grad := by
  have hdot : ∀ d : Fin n → ℝ,
      (∑ i : Fin n, g i * d i) = ∑ i : Fin n, grad i * d i := by
    intro d
    let gd : ℝ := ∑ i : Fin n, g i * d i
    let hd : ℝ := ∑ i : Fin n, grad i * d i
    let φ : ℝ → ℝ := fun t =>
      f (fun i => x i + t * d i) - f x - t * gd
    have hφ_nonneg : ∀ t, 0 ≤ φ t := by
      intro t
      have hsub := hg (fun i => x i + t * d i)
      have hsum : (∑ i : Fin n, g i * ((x i + t * d i) - x i)) = t * gd := by
        dsimp [gd]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      dsimp [φ]
      rw [hsum] at hsub
      linarith
    have hφ0 : φ 0 = 0 := by simp [φ]
    have hlocal : IsLocalMin φ 0 := by
      unfold IsLocalMin IsMinFilter
      exact Filter.Eventually.of_forall (fun t => by
        rw [hφ0]
        exact hφ_nonneg t)
    have hline := hgrad d
    have hlinear : HasDerivAt (fun t : ℝ => t * gd) gd 0 := by
      simpa using (hasDerivAt_id (𝕜 := ℝ) 0).mul_const gd
    have hφderiv : HasDerivAt φ (hd - gd) 0 := by
      dsimp [φ, hd]
      exact (hline.sub_const (f x)).sub hlinear
    have hzero : hd - gd = 0 := hlocal.hasDerivAt_eq_zero hφderiv
    dsimp [gd, hd] at hzero ⊢
    linarith
  funext j
  have hj := hdot (fun i => if i = j then 1 else 0)
  simpa using hj

end Ch15
end NumStability
