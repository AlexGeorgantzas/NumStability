/-
Ch14HymanDeterminant.lean

Higham, "Accuracy and Stability of Numerical Algorithms", 2nd ed.,
Chapter 14 ("Matrix Inversion"), Section 14.6.1 ("Hyman's Method", p. 280)
and Problem 14.14 (p. 285).

Problem 14.14 asks to show that Hyman's method for `det(H)`, `H` an unreduced
upper Hessenberg matrix, computes the *exact* determinant of a nearby matrix
`H + ΔH` with `|ΔH| ≤ γ_{2n-1} |H|` (barring underflow/overflow), and to
describe the effect of a diagonal similarity `H → D⁻¹ H D`.

This file supplies the *floating-point foundation* that the exact Hyman
block-LU / determinant transport wrappers in
`NumStability.Algorithms.MatrixInversion` consume, namely a source-faithful
back-substitution + inner-product + determinant-product rounding model for the
Hyman recurrence.  Concretely, for the cyclically permuted Hessenberg block
`H₁ = [[T, y], [hᵀ, η]]` (dimension `n + 1`, so `N = n + 1` is Higham's matrix
size) it proves that the computed Hyman determinant
`ch14ext_flHymanDet` equals `det(H₁ + ΔH)` for an explicit componentwise
perturbation with `|ΔH| ≤ γ_{2n+1} |H₁| = γ_{2N-1} |H₁|`.

All declarations live in the fresh namespace `NumStability.Ch14Ext` with a
`ch14ext_` prefix.  This file is IMPORT-ONLY: it never edits the co-owned
`MatrixInversion.lean`/`GaussJordan.lean`, only reusing their public
declarations (`higham14_hymanBlockMatrix`, `higham14_hymanSchur`, the
`higham14_problem14_14_*` transport wrappers, `higham14_problem14_14_diagonal*`).

Reused floating-point machinery (all in `NumStability`):
* `fl_backSub`, `BackSubRowSpec`, `fl_backSub_satisfies_spec`  (Higham §8.1 / Thm 8.5)
* `fl_dotProduct`, `dotProduct_backward_stable_x`               (Higham §3.1, eq. 3.4)
* `gamma`, `gammaValid`, `gamma_mul`, `gamma_mono`, `prod_error_bound` (Higham §3.1)
* `IsLeftInverse`, `nonsingInv`, `exists_isLeftInverse_of_det_ne_zero` (matrix algebra)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Rounding
import NumStability.Analysis.MatrixAlgebra
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.MatrixInversion

namespace NumStability.Ch14Ext

open scoped BigOperators
open NumStability

/-! ## Part 1a. Zero-diagonal back-substitution certificate (Higham Thm 8.5)

The repository's `backSub_backward_error_perturbed` produces a perturbation
`ΔU` whose diagonal *is* zero by construction (the division error `(1+ρ)` is
absorbed into the off-diagonal entries and into `Δb`), but the public theorem
does not expose that structural fact.  The Hyman determinant wrapper requires
`ΔT` to have zero diagonal (so that `det(T + ΔT) = det T` exactly).  We
therefore re-derive the perturbed system from `BackSubRowSpec`, exposing the
zero-diagonal property.  The proof mirrors `backSub_backward_error_perturbed`
with the extra conclusion added. -/

/-- Back substitution backward error with the **zero-diagonal** property
exposed.  For the computed solution `x̂ = fl_backSub fp n U b` of an upper
triangular system `U x = b`, there exist `ΔU` (with zero diagonal) and `Δb`
such that `(U + ΔU) x̂ = b + Δb`, `|ΔU| ≤ γ_{n+1} |U|`, `|Δb| ≤ γ_n |b|`. -/
theorem ch14ext_backSub_zeroDiag_perturbed (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hU : ∀ i, U i i ≠ 0)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hn : gammaValid fp (n + 1)) :
    ∃ (ΔU : Matrix (Fin n) (Fin n) ℝ) (Δb : Fin n → ℝ),
      (∀ i j, |ΔU i j| ≤ gamma fp (n + 1) * |U i j|) ∧
      (∀ i, |Δb i| ≤ gamma fp n * |b i|) ∧
      (∀ i, ΔU i i = 0) ∧
      ∀ i, ∑ j : Fin n, (U i j + ΔU i j) * fl_backSub fp n U b j = b i + Δb i := by
  have hspec : BackSubRowSpec fp n U b (fl_backSub fp n U b) :=
    fl_backSub_satisfies_spec fp n U b hU (gammaValid_mono fp (by omega) hn)
  set x_hat := fl_backSub fp n U b with hx_hat
  unfold BackSubRowSpec at hspec
  let above (i : Fin n) := Finset.filter (fun j : Fin n => i.val < j.val) Finset.univ
  let Θ_data : Fin n → ℝ := fun i => Classical.choose (hspec i)
  let ρ_data : Fin n → ℝ := fun i => Classical.choose (Classical.choose_spec (hspec i))
  let θ_data : Fin n → Fin n → ℝ := fun i =>
    Classical.choose (Classical.choose_spec (Classical.choose_spec (hspec i)))
  have hΘ_bound : ∀ i, |Θ_data i| ≤ gamma fp (n - 1 - i.val) := fun i =>
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hspec i)))).1
  have hρ_bound : ∀ i, |ρ_data i| ≤ fp.u := fun i =>
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hspec i)))).2.1
  have hθ_bound : ∀ i j, |θ_data i j| ≤ gamma fp (n - i.val) := fun i j =>
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hspec i)))).2.2.1 j
  have hrow_eq : ∀ i, U i i * x_hat i =
      (b i * (1 + Θ_data i) -
       Finset.sum (above i)
         (fun j => U i j * x_hat j * (1 + θ_data i j))) * (1 + ρ_data i) := fun i =>
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hspec i)))).2.2.2
  let ΔU : Matrix (Fin n) (Fin n) ℝ := fun i j =>
    if i.val < j.val then U i j * ((1 + θ_data i j) * (1 + ρ_data i) - 1) else 0
  let Δb : Fin n → ℝ := fun i => b i * ((1 + Θ_data i) * (1 + ρ_data i) - 1)
  refine ⟨ΔU, Δb, ?_, ?_, ?_, ?_⟩
  -- Bound 1: |ΔU i j| ≤ γ(n+1) |U i j|
  · intro i j
    show |ΔU i j| ≤ gamma fp (n + 1) * |U i j|
    simp only [ΔU]
    by_cases hij : i.val < j.val
    · simp only [hij, ite_true]
      have hmi : n - i.val + 1 ≤ n + 1 := by omega
      have h1valid : gammaValid fp 1 := gammaValid_mono fp (by omega) hn
      have hρ_1 : |ρ_data i| ≤ gamma fp 1 :=
        le_trans (hρ_bound i) (u_le_gamma fp one_pos h1valid)
      obtain ⟨η, hη, heq_η⟩ := gamma_mul fp (n - i.val) 1 (θ_data i j)
        (ρ_data i) (hθ_bound i j) hρ_1 (gammaValid_mono fp hmi hn)
      have hη_eq : η = (1 + θ_data i j) * (1 + ρ_data i) - 1 := by linarith
      rw [← hη_eq]
      have hη_n : |η| ≤ gamma fp (n + 1) := le_trans hη (gamma_mono fp hmi hn)
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right hη_n (abs_nonneg _)
    · simp only [hij, ite_false, abs_zero]
      exact mul_nonneg (gamma_nonneg fp (gammaValid_mono fp (by omega) hn)) (abs_nonneg _)
  -- Bound 2: |Δb i| ≤ γ(n) |b i|
  · intro i
    show |Δb i| ≤ gamma fp n * |b i|
    simp only [Δb]
    have hn' : gammaValid fp n := gammaValid_mono fp (by omega) hn
    have hmi : n - 1 - i.val + 1 ≤ n := by omega
    have h1valid : gammaValid fp 1 := gammaValid_mono fp (by omega) hn
    have hρ_1 : |ρ_data i| ≤ gamma fp 1 :=
      le_trans (hρ_bound i) (u_le_gamma fp one_pos h1valid)
    obtain ⟨ψ, hψ, heq_ψ⟩ := gamma_mul fp (n - 1 - i.val) 1 (Θ_data i)
      (ρ_data i) (hΘ_bound i) hρ_1 (gammaValid_mono fp hmi hn')
    have hψ_eq : ψ = (1 + Θ_data i) * (1 + ρ_data i) - 1 := by linarith
    rw [← hψ_eq]
    have hψ_n : |ψ| ≤ gamma fp n := le_trans hψ (gamma_mono fp hmi hn')
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hψ_n (abs_nonneg _)
  -- Zero diagonal: ΔU i i = 0
  · intro i
    simp only [ΔU, lt_irrefl, ite_false]
  -- Equation: ∑ j (U + ΔU) x̂ = b + Δb
  · intro i
    show ∑ j : Fin n, (U i j + ΔU i j) * x_hat j = b i + Δb i
    have hΔU_below : ∀ j : Fin n, j.val < i.val → ΔU i j = 0 := by
      intro j hj; simp only [ΔU, show ¬(i.val < j.val) by omega, ite_false]
    have hΔU_diag : ΔU i i = 0 := by
      simp only [ΔU, lt_irrefl, ite_false]
    have hΔU_above : ∀ j : Fin n, i.val < j.val →
        ΔU i j = U i j * ((1 + θ_data i j) * (1 + ρ_data i) - 1) := by
      intro j hj; simp only [ΔU, show i.val < j.val from hj, ite_true]
    have hterm_below : ∀ j : Fin n, j.val < i.val →
        (U i j + ΔU i j) * x_hat j = 0 := by
      intro j hj
      rw [hUT i j hj, hΔU_below j hj, add_zero, zero_mul]
    have hterm_diag : (U i i + ΔU i i) * x_hat i = U i i * x_hat i := by
      rw [hΔU_diag, add_zero]
    have hterm_above : ∀ j : Fin n, i.val < j.val →
        (U i j + ΔU i j) * x_hat j =
          U i j * x_hat j * ((1 + θ_data i j) * (1 + ρ_data i)) := by
      intro j hj
      rw [hΔU_above j hj]; ring
    have hΔb_expand : b i + Δb i = b i * ((1 + Θ_data i) * (1 + ρ_data i)) := by
      simp only [Δb]; ring
    have hexpand : U i i * x_hat i +
        Finset.sum (above i)
          (fun j => U i j * x_hat j * ((1 + θ_data i j) * (1 + ρ_data i))) =
        b i * ((1 + Θ_data i) * (1 + ρ_data i)) := by
      have heq := hrow_eq i
      have hrhs : (b i * (1 + Θ_data i) -
         Finset.sum (above i)
           (fun j => U i j * x_hat j * (1 + θ_data i j))) * (1 + ρ_data i) =
         b i * (1 + Θ_data i) * (1 + ρ_data i) -
         Finset.sum (above i)
           (fun j => U i j * x_hat j * (1 + θ_data i j) * (1 + ρ_data i)) := by
        rw [sub_mul]; congr 1; rw [Finset.sum_mul]
      rw [heq, hrhs]
      have hmul_assoc :
          Finset.sum (above i)
            (fun j => U i j * x_hat j * (1 + θ_data i j) * (1 + ρ_data i)) =
          Finset.sum (above i)
            (fun j => U i j * x_hat j * ((1 + θ_data i j) * (1 + ρ_data i))) := by
        apply Finset.sum_congr rfl; intro j _; ring
      rw [hmul_assoc]
      have := mul_comm (b i * (1 + Θ_data i)) (1 + ρ_data i)
      linarith
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    rw [hterm_diag]
    have herase_eq : Finset.sum (Finset.univ.erase i)
        (fun j => (U i j + ΔU i j) * x_hat j) =
      Finset.sum (above i)
        (fun j => U i j * x_hat j * ((1 + θ_data i j) * (1 + ρ_data i))) := by
      have h_above_sub : above i ⊆ Finset.univ.erase i := by
        intro j hj
        simp only [above, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq]
        intro heq; subst heq; exact absurd hj (lt_irrefl _)
      rw [← Finset.sum_sdiff h_above_sub]
      have hsdiff_zero : Finset.sum (Finset.univ.erase i \ above i)
          (fun j => (U i j + ΔU i j) * x_hat j) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        simp only [above, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, and_true,
          ne_eq, Finset.mem_filter, true_and, not_lt] at hj
        have : j.val < i.val := by
          rcases Nat.lt_or_ge j.val i.val with h | h
          · exact h
          · exfalso; apply hj.1; exact Fin.ext (Nat.le_antisymm hj.2 h)
        exact hterm_below j this
      rw [hsdiff_zero, zero_add]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [above, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact hterm_above j hj
    rw [herase_eq, hΔb_expand]
    exact hexpand

/-! ## Part 1b. Floating-point determinant product model

Hyman's method forms `det(T) = h₂₁ h₃₂ … hₙ,ₙ₋₁` (Higham p. 280), i.e. the
product of the `n` diagonal entries of the triangular block `T`, computed with
`n - 1` floating-point multiplications.  We model this product and bound its
relative error by `γ_{n-1}` (Higham §3.1). -/

/-- Accumulating fold for the floating-point product of a list of scalars. -/
noncomputable def ch14ext_flDiagProdAux (fp : FPModel) :
    (k : ℕ) → ℝ → (Fin k → ℝ) → ℝ
  | 0, acc, _ => acc
  | (k + 1), acc, d => ch14ext_flDiagProdAux fp k (fp.fl_mul acc (d 0)) (fun i => d i.succ)

/-- Floating-point product of the `n` scalars `d 0, …, d (n-1)`, computed with
`n - 1` multiplications (the first scalar seeds the accumulator, so it carries
no rounding error). -/
noncomputable def ch14ext_flDiagProd (fp : FPModel) :
    (n : ℕ) → (Fin n → ℝ) → ℝ
  | 0, _ => 1
  | (m + 1), d => ch14ext_flDiagProdAux fp m (d 0) (fun i => d i.succ)

/-- Expansion of the accumulating product fold: the result is the accumulator
times the exact product of the `k` factors, times a product of `k` local
relative rounding factors each bounded by `u`. -/
theorem ch14ext_flDiagProdAux_expand (fp : FPModel) :
    ∀ (k : ℕ) (acc : ℝ) (d : Fin k → ℝ),
      ∃ ε : Fin k → ℝ, (∀ i, |ε i| ≤ fp.u) ∧
        ch14ext_flDiagProdAux fp k acc d =
          acc * (∏ i : Fin k, d i) * ∏ i : Fin k, (1 + ε i) := by
  intro k
  induction k with
  | zero =>
      intro acc d
      exact ⟨fun i => i.elim0, fun i => i.elim0, by simp [ch14ext_flDiagProdAux]⟩
  | succ k ih =>
      intro acc d
      obtain ⟨δ0, hδ0, hmul0⟩ := fp.model_mul acc (d 0)
      obtain ⟨ε', hε', hexp⟩ := ih (fp.fl_mul acc (d 0)) (fun i => d i.succ)
      refine ⟨Fin.cons δ0 ε', ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ ?_ i
        · simpa using hδ0
        · intro j; simpa using hε' j
      · show ch14ext_flDiagProdAux fp (k + 1) acc d = _
        have hcons : (∏ i : Fin (k + 1), (1 + Fin.cons δ0 ε' i)) =
            (1 + δ0) * ∏ i : Fin k, (1 + ε' i) := by
          rw [Fin.prod_univ_succ]
          simp [Fin.cons_zero, Fin.cons_succ]
        have hdprod : (∏ i : Fin (k + 1), d i) = d 0 * ∏ i : Fin k, d i.succ :=
          Fin.prod_univ_succ (fun i => d i)
        simp only [ch14ext_flDiagProdAux]
        rw [hexp, hmul0, hcons, hdprod]
        ring

/-- Relative-error bound for the floating-point diagonal product (Higham §3.1):
for a nonempty index set the computed product is `(∏ d) · (1 + θ)` with
`|θ| ≤ γ_{n-1}`. -/
theorem ch14ext_flDiagProd_relError (fp : FPModel) (n : ℕ) (d : Fin n → ℝ)
    (hn : 0 < n) (hvalid : gammaValid fp (n - 1)) :
    ∃ θ : ℝ, |θ| ≤ gamma fp (n - 1) ∧
      ch14ext_flDiagProd fp n d = (∏ i : Fin n, d i) * (1 + θ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  obtain ⟨ε, hε, hexp⟩ :=
    ch14ext_flDiagProdAux_expand fp m (d 0) (fun i => d i.succ)
  have hmvalid : gammaValid fp m := by simpa using hvalid
  obtain ⟨θ, hθ, hprod⟩ := prod_error_bound fp m ε hε hmvalid
  refine ⟨θ, by simpa using hθ, ?_⟩
  show ch14ext_flDiagProdAux fp m (d 0) (fun i => d i.succ) = _
  rw [hexp, hprod, Fin.prod_univ_succ (fun i => d i)]

/-! ## Part 2. The Hyman Schur scalar equals the computed value

For a genuine left inverse `TpertInv` of the perturbed block `Tpert = T + ΔT`
and the back-substitution equation `Tpert x̂ = yp`, the Schur scalar
`η - (hp)ᵀ TpertInv yp` collapses to `η - (hp)ᵀ x̂`. -/

/-- `higham14_hymanSchur hp yp TpertInv η = η - Σ_k hp_k x̂_k`
whenever `TpertInv` is a left inverse of `Tpert` and `Tpert x̂ = yp`. -/
theorem ch14ext_hymanSchur_eq_of_leftInverse (n : ℕ)
    (Tpert TpertInv : Matrix (Fin n) (Fin n) ℝ) (yp hp xhat : Fin n → ℝ) (η : ℝ)
    (hInv : IsLeftInverse n Tpert TpertInv)
    (hsolve : ∀ i, ∑ j : Fin n, Tpert i j * xhat j = yp i) :
    higham14_hymanSchur hp yp TpertInv η = η - ∑ k : Fin n, hp k * xhat k := by
  have hkey : ∀ k : Fin n, ∑ j : Fin n, TpertInv k j * yp j = xhat k := by
    intro k
    have hstep : ∀ j : Fin n,
        TpertInv k j * yp j = ∑ l : Fin n, TpertInv k j * Tpert j l * xhat l := by
      intro j
      rw [← hsolve j, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro l _; ring
    calc
      ∑ j : Fin n, TpertInv k j * yp j
          = ∑ j : Fin n, ∑ l : Fin n, TpertInv k j * Tpert j l * xhat l := by
            apply Finset.sum_congr rfl; intro j _; rw [hstep j]
      _ = ∑ l : Fin n, ∑ j : Fin n, TpertInv k j * Tpert j l * xhat l := Finset.sum_comm
      _ = ∑ l : Fin n, (if k = l then (1 : ℝ) else 0) * xhat l := by
            apply Finset.sum_congr rfl; intro l _
            rw [← Finset.sum_mul, hInv k l]
      _ = xhat k := by simp
  unfold higham14_hymanSchur higham14_hymanRowTimesInv
  congr 1
  have hstep2 : ∀ j : Fin n,
      (∑ k : Fin n, hp k * TpertInv k j) * yp j
        = ∑ k : Fin n, hp k * (TpertInv k j * yp j) := by
    intro j
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro k _; ring
  calc
    ∑ j : Fin n, (∑ k : Fin n, hp k * TpertInv k j) * yp j
        = ∑ j : Fin n, ∑ k : Fin n, hp k * (TpertInv k j * yp j) := by
          apply Finset.sum_congr rfl; intro j _; rw [hstep2 j]
    _ = ∑ k : Fin n, ∑ j : Fin n, hp k * (TpertInv k j * yp j) := Finset.sum_comm
    _ = ∑ k : Fin n, hp k * (∑ j : Fin n, TpertInv k j * yp j) := by
          apply Finset.sum_congr rfl; intro k _; rw [Finset.mul_sum]
    _ = ∑ k : Fin n, hp k * xhat k := by
          apply Finset.sum_congr rfl; intro k _; rw [hkey k]

/-! ## Part 3. Headline backward-error theorem for Hyman's method (Problem 14.14)

For the cyclically permuted Hessenberg block `H₁ = [[T, y], [hᵀ, η]]` of
dimension `n + 1 = N`, the floating-point Hyman determinant
`ch14ext_flHymanDet` is the *exact* determinant of a componentwise-perturbed
`H₁ + ΔH` with `|ΔH| ≤ γ_{2n+1} |H₁| = γ_{2N-1} |H₁|`.  This is Problem 14.14
at printed strength (`γ_{2N-1}`), with all rounding budgets derived, not
assumed. -/

/-- The floating-point Hyman determinant of the triangular block `T`, upper
Hessenberg data `y, h, η`:  computed determinant product of the diagonal of
`T`, times the computed Schur scalar `fl(η − fl(hᵀ x̂))`, where
`x̂ = fl_backSub fp n T y`. -/
noncomputable def ch14ext_flHymanDet (fp : FPModel) (n : ℕ)
    (T : Matrix (Fin n) (Fin n) ℝ) (y h : Fin n → ℝ) (η : ℝ) : ℝ :=
  fp.fl_mul (ch14ext_flDiagProd fp n (fun i => T i i))
            (fp.fl_sub η (fl_dotProduct fp n h (fl_backSub fp n T y)))

set_option maxHeartbeats 1600000 in
theorem ch14ext_hyman_flDet_backward_error (fp : FPModel) (n : ℕ)
    (T : Matrix (Fin n) (Fin n) ℝ) (y h : Fin n → ℝ) (η : ℝ)
    (hn : 0 < n)
    (hTupper : T.BlockTriangular id)
    (hTdiag : ∀ i, T i i ≠ 0)
    (hvalid : gammaValid fp (2 * n + 1)) :
    ∃ ΔH : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ,
      (∀ p q, |ΔH p q| ≤ gamma fp (2 * n + 1) *
        |higham14_hymanBlockMatrix T y h η p q|) ∧
      Matrix.det (higham14_hymanBlockMatrix T y h η + ΔH) =
        ch14ext_flHymanDet fp n T y h η := by
  classical
  set x_hat := fl_backSub fp n T y with hx_hat
  set H1 := higham14_hymanBlockMatrix T y h η with hH1
  -- gammaValid monotonicity facts
  have hv_n1 : gammaValid fp (n + 1) := gammaValid_mono fp (by omega) hvalid
  have hv_n : gammaValid fp n := gammaValid_mono fp (by omega) hvalid
  have hv_pred : gammaValid fp (n - 1) := gammaValid_mono fp (by omega) hvalid
  have hv_1 : gammaValid fp 1 := gammaValid_mono fp (by omega) hvalid
  have hUT : ∀ i j : Fin n, j.val < i.val → T i j = 0 := fun i j hji => hTupper hji
  -- (1) back-substitution zero-diagonal certificate
  obtain ⟨ΔT, Δb, hΔT_bound, hΔb_bound, hΔT_diag, hsolve0⟩ :=
    ch14ext_backSub_zeroDiag_perturbed fp n T y hTdiag hUT hv_n1
  -- (2) T + ΔT is invertible (zero-diagonal ⟹ det unchanged)
  have hdetTpert : Matrix.det (T + ΔT) = Matrix.det T :=
    higham14_problem14_14_det_upper_add_zero_diag_of_abs_bound T ΔT (gamma fp (n + 1))
      hTupper hΔT_diag hΔT_bound
  have hdetT_ne : Matrix.det T ≠ 0 := by
    rw [Matrix.det_of_upperTriangular hTupper]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hTdiag i)
  have hdetTpert_ne : Matrix.det (T + ΔT) ≠ 0 := by rw [hdetTpert]; exact hdetT_ne
  obtain ⟨TpertInv, hTpertInv⟩ := exists_isLeftInverse_of_det_ne_zero n (T + ΔT) hdetTpert_ne
  -- (3) inner-product backward stability for hᵀ x̂
  obtain ⟨Δh, hΔh_bound, hdot⟩ := dotProduct_backward_stable_x fp n h x_hat hv_n
  -- perturbed block and its determinant via the Hyman transport wrapper
  set Hpert := higham14_hymanBlockMatrix (T + ΔT) (y + Δb) (h + Δh) η with hHpert
  have hsolve : ∀ i, ∑ j : Fin n, (T + ΔT) i j * x_hat j = (y + Δb) i := by
    intro i
    have := hsolve0 i
    simpa [Matrix.add_apply, Pi.add_apply] using this
  have hschur :
      higham14_hymanSchur (h + Δh) (y + Δb) TpertInv η =
        η - fl_dotProduct fp n h x_hat := by
    rw [ch14ext_hymanSchur_eq_of_leftInverse n (T + ΔT) TpertInv (y + Δb) (h + Δh) x_hat η
      hTpertInv hsolve, hdot]
    simp only [Pi.add_apply]
  have hdetHpert :
      Matrix.det Hpert = Matrix.det T * (η - fl_dotProduct fp n h x_hat) := by
    rw [hHpert,
      higham14_problem14_14_hyman_det_cyclic_block_of_upper_add_zero_diag
        T ΔT TpertInv (y + Δb) (h + Δh) η (gamma fp (n + 1))
        hTupper hΔT_diag hΔT_bound hTpertInv, hschur]
  -- outer rounding factor: scale = (1+θp)(1+δs)(1+δm), |scale - 1| ≤ γ(n+1)
  set s := fl_dotProduct fp n h x_hat with hs
  obtain ⟨δs, hδs, hsub⟩ := fp.model_sub η s
  obtain ⟨δm, hδm, hmul⟩ :=
    fp.model_mul (ch14ext_flDiagProd fp n (fun i => T i i)) (fp.fl_sub η s)
  obtain ⟨θp, hθp, hDiag⟩ := ch14ext_flDiagProd_relError fp n (fun i => T i i) hn hv_pred
  have hδs_1 : |δs| ≤ gamma fp 1 := le_trans hδs (u_le_gamma fp one_pos hv_1)
  have hδm_1 : |δm| ≤ gamma fp 1 := le_trans hδm (u_le_gamma fp one_pos hv_1)
  obtain ⟨ω1, hω1, heq1⟩ := gamma_mul fp (n - 1) 1 θp δs hθp hδs_1
    (by have : n - 1 + 1 = n := by omega
        rw [this]; exact hv_n)
  have hω1n : |ω1| ≤ gamma fp n := by
    simpa [Nat.sub_add_cancel hn] using hω1
  obtain ⟨ω, hω, heq2⟩ := gamma_mul fp n 1 ω1 δm hω1n hδm_1 hv_n1
  set scale := (1 + θp) * (1 + δs) * (1 + δm) with hscaleDef
  have hscale_eq : scale = 1 + ω := by
    have h1 : (1 + θp) * (1 + δs) = 1 + ω1 := by linarith [heq1]
    have h2 : (1 + ω1) * (1 + δm) = 1 + ω := by linarith [heq2]
    rw [hscaleDef, h1, h2]
  have hscale_sub : |scale - 1| ≤ gamma fp (n + 1) := by
    rw [hscale_eq]; simpa using hω
  have hdetT_prod : ch14ext_flDiagProd fp n (fun i => T i i) = Matrix.det T * (1 + θp) := by
    rw [hDiag, Matrix.det_of_upperTriangular hTupper]
  -- flHymanDet expansion
  have hflHyman : ch14ext_flHymanDet fp n T y h η = Matrix.det Hpert * scale := by
    rw [hdetHpert]
    show fp.fl_mul (ch14ext_flDiagProd fp n (fun i => T i i)) (fp.fl_sub η s) = _
    rw [hmul, hsub, hdetT_prod, hscaleDef]; ring
  -- scaling diagonal on the Unit block
  set dω : Fin n ⊕ Unit → ℝ := Sum.elim (fun _ => (1 : ℝ)) (fun _ => scale) with hdω
  set Hfinal := Hpert * Matrix.diagonal dω with hHfinal
  have hprod_dω : (∏ x : Fin n ⊕ Unit, dω x) = scale := by
    rw [Fintype.prod_sum_type]
    simp [hdω]
  have hdetHfinal : Matrix.det Hfinal = Matrix.det Hpert * scale := by
    rw [hHfinal, Matrix.det_mul, Matrix.det_diagonal, hprod_dω]
  -- final perturbation
  refine ⟨Hfinal - H1, ?_, ?_⟩
  · -- componentwise bound  |ΔH| ≤ γ_{2n+1} |H1|
    intro p q
    have hmono_n1 : gamma fp (n + 1) ≤ gamma fp (2 * n + 1) :=
      gamma_mono fp (by omega) hvalid
    have hmono_n : gamma fp n ≤ gamma fp (2 * n + 1) :=
      gamma_mono fp (by omega) hvalid
    have hentry : (Hfinal - H1) p q = Hpert p q * dω q - H1 p q := by
      rw [hHfinal]
      simp [Matrix.sub_apply, Matrix.mul_diagonal]
    -- y-column bound helper
    have hycol : ∀ i : Fin n, |(y i + Δb i) * scale - y i| ≤ gamma fp (2 * n + 1) * |y i| := by
      intro i
      have hrewrite : (y i + Δb i) * scale - y i = y i * (scale - 1) + Δb i * scale := by ring
      have habs_n : |gamma fp n| ≤ gamma fp n := le_of_eq (abs_of_nonneg (gamma_nonneg fp hv_n))
      have habs_n1 : |gamma fp (n + 1)| ≤ gamma fp (n + 1) :=
        le_of_eq (abs_of_nonneg (gamma_nonneg fp hv_n1))
      obtain ⟨ζ, hζ, heqζ⟩ := gamma_mul fp n (n + 1) (gamma fp n) (gamma fp (n + 1))
        habs_n habs_n1
        (by rw [show n + (n + 1) = 2 * n + 1 from by ring]; exact hvalid)
      have hζ_val : gamma fp n + gamma fp (n + 1) + gamma fp n * gamma fp (n + 1) = ζ := by
        nlinarith [heqζ]
      have hζ_le : ζ ≤ gamma fp (2 * n + 1) := by
        have : ζ ≤ gamma fp (n + (n + 1)) := le_trans (le_abs_self ζ) hζ
        rwa [show n + (n + 1) = 2 * n + 1 from by ring] at this
      have hbound_scale : |scale| ≤ 1 + gamma fp (n + 1) := by
        rw [hscale_eq, abs_le]
        refine ⟨?_, ?_⟩
        · linarith [neg_abs_le ω, hω, gamma_nonneg fp hv_n1]
        · linarith [le_abs_self ω, hω]
      calc
        |(y i + Δb i) * scale - y i|
            = |y i * (scale - 1) + Δb i * scale| := by rw [hrewrite]
        _ ≤ |y i * (scale - 1)| + |Δb i * scale| := abs_add_le _ _
        _ = |y i| * |scale - 1| + |Δb i| * |scale| := by rw [abs_mul, abs_mul]
        _ ≤ |y i| * gamma fp (n + 1) + (gamma fp n * |y i|) * (1 + gamma fp (n + 1)) :=
              add_le_add
                (mul_le_mul_of_nonneg_left hscale_sub (abs_nonneg _))
                (mul_le_mul (hΔb_bound i) hbound_scale (abs_nonneg _)
                  (mul_nonneg (gamma_nonneg fp hv_n) (abs_nonneg _)))
        _ = |y i| * (gamma fp n + gamma fp (n + 1) + gamma fp n * gamma fp (n + 1)) := by ring
        _ = |y i| * ζ := by rw [hζ_val]
        _ ≤ |y i| * gamma fp (2 * n + 1) :=
              mul_le_mul_of_nonneg_left hζ_le (abs_nonneg _)
        _ = gamma fp (2 * n + 1) * |y i| := by ring
    rw [hentry]
    rcases p with i | u <;> rcases q with j | v
    · -- (inl i, inl j): T-block, ΔT
      have hHpert_e : Hpert (Sum.inl i) (Sum.inl j) = T i j + ΔT i j := by
        rw [hHpert]; simp [higham14_hymanBlockMatrix, Matrix.add_apply]
      have hH1_e : H1 (Sum.inl i) (Sum.inl j) = T i j := by
        rw [hH1]; simp [higham14_hymanBlockMatrix]
      rw [hHpert_e, hH1_e]
      simp only [hdω, Sum.elim_inl, mul_one]
      rw [add_sub_cancel_left]
      exact le_trans (hΔT_bound i j) (mul_le_mul_of_nonneg_right hmono_n1 (abs_nonneg _))
    · -- (inl i, inr v): y-column
      have hHpert_e : Hpert (Sum.inl i) (Sum.inr v) = y i + Δb i := by
        rw [hHpert]; simp [higham14_hymanBlockMatrix, Pi.add_apply]
      have hH1_e : H1 (Sum.inl i) (Sum.inr v) = y i := by
        rw [hH1]; simp [higham14_hymanBlockMatrix]
      rw [hHpert_e, hH1_e]
      simp only [hdω, Sum.elim_inr]
      exact hycol i
    · -- (inr u, inl j): h-row, Δh
      have hHpert_e : Hpert (Sum.inr u) (Sum.inl j) = h j + Δh j := by
        rw [hHpert]; simp [higham14_hymanBlockMatrix, Pi.add_apply]
      have hH1_e : H1 (Sum.inr u) (Sum.inl j) = h j := by
        rw [hH1]; simp [higham14_hymanBlockMatrix]
      rw [hHpert_e, hH1_e]
      simp only [hdω, Sum.elim_inl, mul_one]
      rw [add_sub_cancel_left]
      exact le_trans (hΔh_bound j) (mul_le_mul_of_nonneg_right hmono_n (abs_nonneg _))
    · -- (inr u, inr v): η-corner
      have hHpert_e : Hpert (Sum.inr u) (Sum.inr v) = η := by
        rw [hHpert]; simp [higham14_hymanBlockMatrix]
      have hH1_e : H1 (Sum.inr u) (Sum.inr v) = η := by
        rw [hH1]; simp [higham14_hymanBlockMatrix]
      rw [hHpert_e, hH1_e]
      simp only [hdω, Sum.elim_inr]
      have : η * scale - η = η * (scale - 1) := by ring
      rw [this, abs_mul]
      calc |η| * |scale - 1| ≤ |η| * gamma fp (n + 1) :=
              mul_le_mul_of_nonneg_left hscale_sub (abs_nonneg _)
        _ ≤ |η| * gamma fp (2 * n + 1) :=
              mul_le_mul_of_nonneg_left hmono_n1 (abs_nonneg _)
        _ = gamma fp (2 * n + 1) * |η| := by ring
  · -- determinant identity:  det (H1 + (Hfinal - H1)) = flHymanDet
    have hadd : H1 + (Hfinal - H1) = Hfinal := by
      ext p q; simp [Matrix.add_apply, Matrix.sub_apply]
    rw [hadd, hdetHfinal, hflHyman]

/-- Genuine-Hessenberg form of Problem 14.14.  If the original unreduced upper
Hessenberg matrix `H` has the cyclically permuted Hyman block form
`H₁ = [[T, y], [hᵀ, η]] = Hσ` (Higham p. 280, `det H₁ = (-1)^{N-1} det H`), then
Hyman's method computes the exact determinant of `H + ΔH` for a componentwise
perturbation with `|ΔH| ≤ γ_{2n+1} |H| = γ_{2N-1} |H|`, `N = n + 1`.  The
row-permutation sign is the exact `(-1)^{N-1}` factor of (14.36); no rounding
enters it. -/
theorem ch14ext_hyman_flDet_backward_error_original (fp : FPModel) (n : ℕ)
    (H : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ)
    (T : Matrix (Fin n) (Fin n) ℝ) (y h : Fin n → ℝ) (η : ℝ)
    (σ : Equiv.Perm (Fin n ⊕ Unit))
    (hn : 0 < n)
    (hTupper : T.BlockTriangular id)
    (hTdiag : ∀ i, T i i ≠ 0)
    (hvalid : gammaValid fp (2 * n + 1))
    (hH : higham14_hymanBlockMatrix T y h η =
        Matrix.submatrix H σ (Equiv.refl (Fin n ⊕ Unit))) :
    ∃ ΔH : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ,
      (∀ p q, |ΔH p q| ≤ gamma fp (2 * n + 1) * |H p q|) ∧
      Matrix.det (H + ΔH) =
        (Equiv.Perm.sign σ : ℝ) * ch14ext_flHymanDet fp n T y h η := by
  obtain ⟨ΔH₁, hbound, hdet⟩ :=
    ch14ext_hyman_flDet_backward_error fp n T y h η hn hTupper hTdiag hvalid
  refine ⟨Matrix.submatrix ΔH₁ σ.symm (Equiv.refl (Fin n ⊕ Unit)), ?_, ?_⟩
  · intro p q
    have hb := hbound (σ.symm p) q
    rw [hH] at hb
    simpa [Matrix.submatrix_apply, Equiv.apply_symm_apply] using hb
  · have hsub_eq :
        Matrix.submatrix (H + Matrix.submatrix ΔH₁ σ.symm (Equiv.refl (Fin n ⊕ Unit)))
            σ (Equiv.refl (Fin n ⊕ Unit)) =
          higham14_hymanBlockMatrix T y h η + ΔH₁ := by
      ext p q
      rw [hH]
      simp [Matrix.submatrix_apply, Matrix.add_apply, Equiv.symm_apply_apply]
    have hperm :
        Matrix.det (higham14_hymanBlockMatrix T y h η + ΔH₁) =
          (Equiv.Perm.sign σ : ℝ) *
            Matrix.det (H + Matrix.submatrix ΔH₁ σ.symm (Equiv.refl (Fin n ⊕ Unit))) := by
      rw [← hsub_eq]
      simpa using
        Matrix.det_permute σ (H + Matrix.submatrix ΔH₁ σ.symm (Equiv.refl (Fin n ⊕ Unit)))
    have hsq : (Equiv.Perm.sign σ : ℝ) * (Equiv.Perm.sign σ : ℝ) = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]
    rw [hdet] at hperm
    calc
      Matrix.det (H + Matrix.submatrix ΔH₁ σ.symm (Equiv.refl (Fin n ⊕ Unit)))
          = 1 * Matrix.det (H + Matrix.submatrix ΔH₁ σ.symm (Equiv.refl (Fin n ⊕ Unit))) := by
            ring
      _ = ((Equiv.Perm.sign σ : ℝ) * (Equiv.Perm.sign σ : ℝ)) *
            Matrix.det (H + Matrix.submatrix ΔH₁ σ.symm (Equiv.refl (Fin n ⊕ Unit))) := by
            rw [hsq]
      _ = (Equiv.Perm.sign σ : ℝ) *
            ((Equiv.Perm.sign σ : ℝ) *
              Matrix.det (H + Matrix.submatrix ΔH₁ σ.symm (Equiv.refl (Fin n ⊕ Unit)))) := by
            ring
      _ = (Equiv.Perm.sign σ : ℝ) * ch14ext_flHymanDet fp n T y h η := by
            rw [← hperm]

/-! ## Part 4. Effect of a diagonal similarity `H → D⁻¹ H D` (Problem 14.14)

Problem 14.14 also asks for the effect on the error bound of a diagonal
similarity `H → D⁻¹ H D`, `D = diag(dᵢ)`, `dᵢ ≠ 0`.  The answer is that the
relative componentwise error bound is **invariant**: any backward-error
certificate for the scaled matrix `Hscaled = D⁻¹ H D` transports back to the
original `H` with the *same* relative bound `γ_{2n+1}` and the *same* exact
determinant.  The `dᵢ` factors cancel in the relative bound, and diagonal
similarity preserves the determinant.  This reuses the repository's
diagonal-scaling transport lemma
`higham14_problem14_14_unscale_deltaH_det_of_diagonal_scaled_det`. -/

/-- Diagonal-similarity invariance of the Hyman error bound (Problem 14.14).
If the diagonally scaled Hessenberg `Hscaled = D⁻¹ H D` admits a backward-error
perturbation `ΔHscaled` with `|ΔHscaled| ≤ γ_{2n+1} |Hscaled|` and
`det(Hscaled + ΔHscaled) = v`, then the original `H` admits a perturbation
`ΔH` with the *same* relative bound `|ΔH| ≤ γ_{2n+1} |H|` and
`det(H + ΔH) = v`.  Hence a diagonal similarity leaves the Hyman error bound
unchanged. -/
theorem ch14ext_hyman_diagonalSimilarity_bound_invariant (fp : FPModel) (n : ℕ)
    (H Hscaled ΔHscaled : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ)
    (d : Fin n ⊕ Unit → ℝ) (v : ℝ)
    (hd : ∀ i, d i ≠ 0)
    (hHscaled : Hscaled = higham14_problem14_14_diagonalSimilarity d H)
    (hΔbound : ∀ p q, |ΔHscaled p q| ≤ gamma fp (2 * n + 1) * |Hscaled p q|)
    (hdet : Matrix.det (Hscaled + ΔHscaled) = v) :
    ∃ ΔH : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ,
      (∀ p q, |ΔH p q| ≤ gamma fp (2 * n + 1) * |H p q|) ∧
      Matrix.det (H + ΔH) = v :=
  higham14_problem14_14_unscale_deltaH_det_of_diagonal_scaled_det
    H Hscaled ΔHscaled d (gamma fp (2 * n + 1)) v hd hHscaled hΔbound hdet

/-- Combined statement: Hyman's method applied to the diagonally scaled block
`Hscaled = D⁻¹ H₁ D` (itself presented in Hyman block form
`Hscaled = [[T', y'], [h'ᵀ, η']]` with `T'` upper triangular, nonzero diagonal)
computes the exact determinant of `H₁ + ΔH`, `|ΔH| ≤ γ_{2n+1} |H₁|`, with the
*same* constant as the unscaled problem — an explicit witness that the diagonal
similarity does not degrade the Hyman error bound.  `H₁ = hymanBlockMatrix T y h η`
is the original block and `T', y', h', η'` the scaled block data. -/
theorem ch14ext_hyman_flDet_diagonalSimilarity (fp : FPModel) (n : ℕ)
    (T : Matrix (Fin n) (Fin n) ℝ) (y h : Fin n → ℝ) (η : ℝ)
    (Tsc : Matrix (Fin n) (Fin n) ℝ) (ysc hsc : Fin n → ℝ) (ηsc : ℝ)
    (d : Fin n ⊕ Unit → ℝ)
    (hn : 0 < n)
    (hd : ∀ i, d i ≠ 0)
    (hTscUpper : Tsc.BlockTriangular id)
    (hTscDiag : ∀ i, Tsc i i ≠ 0)
    (hvalid : gammaValid fp (2 * n + 1))
    (hscaled : higham14_problem14_14_diagonalSimilarity d
        (higham14_hymanBlockMatrix T y h η) =
        higham14_hymanBlockMatrix Tsc ysc hsc ηsc) :
    ∃ ΔH : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ,
      (∀ p q, |ΔH p q| ≤ gamma fp (2 * n + 1) *
        |higham14_hymanBlockMatrix T y h η p q|) ∧
      Matrix.det (higham14_hymanBlockMatrix T y h η + ΔH) =
        ch14ext_flHymanDet fp n Tsc ysc hsc ηsc := by
  obtain ⟨ΔHsc, hΔsc_bound, hΔsc_det⟩ :=
    ch14ext_hyman_flDet_backward_error fp n Tsc ysc hsc ηsc hn hTscUpper hTscDiag hvalid
  refine ch14ext_hyman_diagonalSimilarity_bound_invariant fp n
    (higham14_hymanBlockMatrix T y h η)
    (higham14_hymanBlockMatrix Tsc ysc hsc ηsc) ΔHsc d _ hd hscaled.symm
    hΔsc_bound hΔsc_det

end NumStability.Ch14Ext
