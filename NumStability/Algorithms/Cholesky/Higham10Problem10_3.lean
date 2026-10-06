-- Algorithms/Cholesky/Higham10Problem10_3.lean
--
-- Higham, "Accuracy and Stability of Numerical Algorithms", 2nd ed.,
-- Problem 10.3 (p. 211; used in the proof of Theorem 10.3 on p. 197).

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.TriangularArbitraryOrder

namespace NumStability

open scoped BigOperators

/-- **Higham, 2nd ed., Problem 10.3 (arbitrary evaluation order).**

Let `ŝ` be the floating-point evaluation, in any order, of

`c - ∑ i, a i * b i`

and let `ŷ = fl(sqrt(ŝ))`.  Provided `ŝ ≥ 0`, there are relative
perturbations satisfying the printed sharp constants

`|theta₀| ≤ γ_(m+2)` and `|eta i| ≤ γ_m`

such that

`ŷ² (1 + theta₀) = c - ∑ i, a i * b i * (1 + eta i)`.

Here `m = k - 1` in the book's notation, so the two bounds are exactly
`γ_(k+1)` and `γ_(k-1)`.  The proof retains the operation counters from
the no-division clause of Lemma 8.4 and adds the two inverse square-root
rounding factors. -/
theorem higham10_problem10_3_anyOrder_sqrt (fp : FPModel) {m : ℕ}
    (t : SumTree (m + 1)) (hm2 : gammaValid fp (m + 2))
    (c : ℝ) (a b : Fin m → ℝ)
    (hs : 0 ≤ t.eval fp
      (Fin.cases c (fun q => - fp.fl_mul (a q) (b q)))) :
    let w : Fin (m + 1) → ℝ :=
      Fin.cases c (fun q => - fp.fl_mul (a q) (b q))
    ∃ (θ₀ : ℝ) (η : Fin m → ℝ),
      |θ₀| ≤ gamma fp (m + 2) ∧
      (∀ q, |η q| ≤ gamma fp m) ∧
      (fp.fl_sqrt (t.eval fp w)) ^ 2 * (1 + θ₀) =
        c - ∑ q : Fin m, a q * b q * (1 + η q) := by
  intro w
  have hm : gammaValid fp m := gammaValid_mono fp (by omega) hm2
  have h1 : gammaValid fp 1 := gammaValid_mono fp (by omega) hm2
  have hu : fp.u < 1 := by
    unfold gammaValid at h1
    simpa using h1
  obtain ⟨α, η, hαcounter, hαbd, hηcounter, hηbd, hinner⟩ :=
    higham8_4_anyOrder_mulSub_noDiv_counter fp t hm hu c a b
  obtain ⟨δ, hδ, hsqrt⟩ := fp.model_sqrt (t.eval fp w) hs
  have hδcounter : relErrorCounter fp 1 (1 + δ) :=
    higham8_relErrorCounter_single fp hδ
  have hδinv : relErrorCounter fp 1 (1 / (1 + δ)) :=
    relErrorCounter_inv fp 1 (1 + δ) hδcounter hu
  let H : ℝ := (1 + α) * (1 / (1 + δ)) * (1 / (1 + δ))
  have hHcounter : relErrorCounter fp (m + 2) H := by
    have hfirst := relErrorCounter_mul fp m 1
      (1 + α) (1 / (1 + δ)) hαcounter hδinv
    have hsecond := relErrorCounter_mul fp (m + 1) 1
      ((1 + α) * (1 / (1 + δ))) (1 / (1 + δ)) hfirst hδinv
    simpa [H, Nat.add_assoc] using hsecond
  have hHbd : |H - 1| ≤ gamma fp (m + 2) :=
    relErrorCounter_abs_sub_one_le_gamma fp (m + 2) H hHcounter hm2
  refine ⟨H - 1, η, hHbd, hηbd, ?_⟩
  have hδpos : 0 < 1 + δ := by
    have hneg := (abs_le.mp hδ).1
    linarith
  have hsquare : (fp.fl_sqrt (t.eval fp w)) ^ 2 =
      t.eval fp w * (1 + δ) ^ 2 := by
    rw [hsqrt, mul_pow, Real.sq_sqrt hs]
  rw [hsquare]
  have hHfactor : 1 + (H - 1) = H := by ring
  rw [hHfactor]
  have hcancel :
      (t.eval fp w * (1 + δ) ^ 2) * H =
        t.eval fp w * (1 + α) := by
    dsimp [H]
    field_simp [ne_of_gt hδpos]
  rw [hcancel]
  exact hinner

end NumStability
