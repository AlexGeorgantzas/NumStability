import NumStability.Algorithms.LinearSystems.QR.HouseholderApply
import NumStability.Algorithms.LinearSystems.QR.Householder.PanelApplication
import NumStability.Algorithms.LinearSystems.QR.HouseholderSpec
import NumStability.Analysis.MatrixAlgebra
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter19.Theorem06.CoxHigham

namespace NumStability

open scoped BigOperators

/-!
# TraceKernel

Canonical reusable module extracted without change from Higham20Theorem20_7, Higham20Theorem20_7ActualTrace, Higham20Theorem20_7QdR, Higham20Theorem20_7Runtime, Higham20Theorem20_7SourceTrace.
-/

namespace Theorem20_7

/-- Append one matrix at the inner end of `applyProd`.

`applyProd P a len` is defined by recursion at the outer end; this companion
identity is what connects it to the right-growing `Qacc` trace. -/
theorem applyProd_snoc {m : ℕ} (P : ℕ → Fin m → Fin m → ℝ)
    (a len : ℕ) (x : Fin m → ℝ) :
    Wave19.applyProd P a (len + 1) x =
      Wave19.applyProd P a len (matMulVec m (P (a + len)) x) := by
  induction len generalizing a x with
  | zero => simp [Wave19.applyProd]
  | succ len ih =>
      calc
        Wave19.applyProd P a ((len + 1) + 1) x =
            matMulVec m (P a) (Wave19.applyProd P (a + 1) (len + 1) x) := rfl
        _ = matMulVec m (P a)
            (Wave19.applyProd P (a + 1) len
              (matMulVec m (P ((a + 1) + len)) x)) := by
              rw [ih]
        _ = matMulVec m (P a)
            (Wave19.applyProd P (a + 1) len
              (matMulVec m (P (a + (len + 1))) x)) := by
              rw [show (a + 1) + len = a + (len + 1) by omega]
        _ = Wave19.applyProd P a (len + 1)
            (matMulVec m (P (a + (len + 1))) x) := rfl
/-- Rank-one vector subtracted by one raw Householder reflector. -/
noncomputable def rawHouseholderDirectTerm {m : ℕ}
    (v : ℕ → Fin m → ℝ) (β : ℕ → ℝ) (f : Fin m → ℝ)
    (k : ℕ) : Fin m → ℝ :=
  fun r => β k * (∑ s : Fin m, v k s * f s) * v k r
/-- Ordered matrix products are linear in their vector argument. -/
theorem applyProd_sub {m : ℕ} (P : ℕ → Fin m → Fin m → ℝ)
    (a len : ℕ) (f g : Fin m → ℝ) :
    Wave19.applyProd P a len (fun r => f r - g r) =
      fun r => Wave19.applyProd P a len f r -
        Wave19.applyProd P a len g r := by
  induction len generalizing a f g with
  | zero => simp [Wave19.applyProd]
  | succ len ih =>
      simp only [Wave19.applyProd]
      rw [ih]
      funext i
      simp only [matMulVec, mul_sub, Finset.sum_sub_distrib]
/-- One source-stored panel step.  Completed columns and completed rows are
copied, the active pivot column stores `alpha` followed by exact zeros, and
only the genuinely active trailing rectangle uses the rounded compact update. -/
noncomputable def fl_householderCoxHighamStoredPanelStep
    (fp : FPModel) (m n k : ℕ) (alpha : ℝ)
    (v : Fin m → ℝ) (beta : ℝ) (A : Fin m → Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  let raw := fl_householderApplyCompactPanel fp m n v beta A
  fun i j =>
    if j.val < k then
      A i j
    else if i.val < k then
      A i j
    else if j.val = k then
      if i.val = k then alpha else 0
    else
      raw i j
/-- Ordered matrix products commute with scalar multiplication. -/
theorem applyProd_smul {m : ℕ} (P : ℕ → Fin m → Fin m → ℝ)
    (a len : ℕ) (c : ℝ) (f : Fin m → ℝ) :
    Wave19.applyProd P a len (fun r => c * f r) =
      fun r => c * Wave19.applyProd P a len f r := by
  induction len generalizing a f with
  | zero => simp [Wave19.applyProd]
  | succ len ih =>
      simp only [Wave19.applyProd]
      rw [ih]
      funext i
      simp only [matMulVec, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
theorem fl_householderCoxHighamStoredPanelStep_prevColumn_eq
    (fp : FPModel) {m n k : ℕ} (alpha : ℝ)
    (v : Fin m → ℝ) (beta : ℝ) (A : Fin m → Fin n → ℝ)
    {i : Fin m} {j : Fin n} (hj : j.val < k) :
    fl_householderCoxHighamStoredPanelStep fp m n k alpha v beta A i j =
      A i j := by
  simp [fl_householderCoxHighamStoredPanelStep, hj]
theorem fl_householderCoxHighamStoredPanelStep_prevRow_eq
    (fp : FPModel) {m n k : ℕ} (alpha : ℝ)
    (v : Fin m → ℝ) (beta : ℝ) (A : Fin m → Fin n → ℝ)
    {i : Fin m} {j : Fin n} (hi : i.val < k) :
    fl_householderCoxHighamStoredPanelStep fp m n k alpha v beta A i j =
      A i j := by
  by_cases hj : j.val < k
  · simp [fl_householderCoxHighamStoredPanelStep, hj]
  · simp [fl_householderCoxHighamStoredPanelStep, hj, hi]
/-- Transporting a direct Householder term transports only its raw vector;
the scalar multiplier remains outside the prefix product. -/
theorem applyProd_rawHouseholderDirectTerm {m : ℕ}
    (v : ℕ → Fin m → ℝ) (β : ℕ → ℝ) (f : Fin m → ℝ)
    (k : ℕ) (r : Fin m) :
    Wave19.applyProd (fun q => householder m (v q) (β q)) 0 k
        (rawHouseholderDirectTerm v β f k) r =
      (β k * (∑ s : Fin m, v k s * f s)) *
        Wave19.applyProd (fun q => householder m (v q) (β q)) 0 k (v k) r := by
  have h := applyProd_smul
    (fun q => householder m (v q) (β q)) 0 k
    (β k * (∑ s : Fin m, v k s * f s)) (v k)
  simpa [rawHouseholderDirectTerm] using congrFun h r
theorem fl_householderCoxHighamStoredPanelStep_pivot_eq
    (fp : FPModel) {m n k : ℕ} (alpha : ℝ)
    (v : Fin m → ℝ) (beta : ℝ) (A : Fin m → Fin n → ℝ)
    {i : Fin m} {j : Fin n} (hi : i.val = k) (hj : j.val = k) :
    fl_householderCoxHighamStoredPanelStep fp m n k alpha v beta A i j =
      alpha := by
  have hni : ¬ i.val < k := by omega
  have hnj : ¬ j.val < k := by omega
  simp [fl_householderCoxHighamStoredPanelStep, hni, hnj, hi, hj]
/-- Cox--Higham (3.7), in the prefix-transport orientation.

`applyProd P 0 len f` equals `f` minus the sum of the direct rank-one
Householder corrections, with the correction created at stage `k` transported
through stages `0,...,k-1`. -/
theorem applyProd_rawHouseholder_direct_expansion {m : ℕ}
    (v : ℕ → Fin m → ℝ) (β : ℕ → ℝ) (f : Fin m → ℝ)
    (len : ℕ) (r : Fin m) :
    Wave19.applyProd (fun k => householder m (v k) (β k)) 0 len f r =
      f r - ∑ k ∈ Finset.range len,
        Wave19.applyProd (fun q => householder m (v q) (β q)) 0 k
          (rawHouseholderDirectTerm v β f k) r := by
  induction len with
  | zero => simp [Wave19.applyProd]
  | succ len ih =>
      rw [applyProd_snoc]
      let P : ℕ → Fin m → Fin m → ℝ :=
        fun k => householder m (v k) (β k)
      let t := rawHouseholderDirectTerm v β f len
      have hPf : matMulVec m (P len) f = fun r => f r - t r := by
        funext i
        simp only [P, householder_matMulVec_eq]
        simp [t, rawHouseholderDirectTerm]
        ring
      simp only [Nat.zero_add]
      change Wave19.applyProd P 0 len (matMulVec m (P len) f) r = _
      rw [hPf, applyProd_sub]
      rw [show (fun k => householder m (v k) (β k)) = P by rfl] at ih
      change Wave19.applyProd P 0 len f r - Wave19.applyProd P 0 len t r =
        f r - ∑ k ∈ Finset.range (len + 1),
          Wave19.applyProd P 0 k (rawHouseholderDirectTerm v β f k) r
      rw [ih]
      simp only [Finset.sum_range_succ]
      simp [P, t]
      ring
theorem fl_householderCoxHighamStoredPanelStep_pivotTail_eq_zero
    (fp : FPModel) {m n k : ℕ} (alpha : ℝ)
    (v : Fin m → ℝ) (beta : ℝ) (A : Fin m → Fin n → ℝ)
    {i : Fin m} {j : Fin n} (hi : k < i.val) (hj : j.val = k) :
    fl_householderCoxHighamStoredPanelStep fp m n k alpha v beta A i j =
      0 := by
  have hni : ¬ i.val < k := by omega
  have hnj : ¬ j.val < k := by omega
  have hine : ¬ i.val = k := by omega
  simp [fl_householderCoxHighamStoredPanelStep, hni, hnj, hine, hj]

/-! ## Executed active-max trace and named reflector data -/
/-- Conjugating a Householder vector and its argument by an involutive row
permutation conjugates the resulting matrix-vector product. -/
theorem matMulVec_householder_vecPermute_involution {m : ℕ}
    (S : Equiv.Perm (Fin m)) (v b : Fin m → ℝ) (beta : ℝ)
    (hS : ∀ q, S (S q) = q) (i : Fin m) :
    matMulVec m (householder m (vecPermute S v) beta) b i =
      matMulVec m (householder m v beta) (vecPermute S b) (S i) := by
  rw [householder_matMulVec_eq, householder_matMulVec_eq]
  have hsum : (∑ q : Fin m, v (S q) * b q) =
      ∑ q : Fin m, v q * b (S q) := by
    calc
      (∑ q : Fin m, v (S q) * b q) =
          ∑ q : Fin m, (fun r => v r * b (S r)) (S q) := by
            apply Finset.sum_congr rfl
            intro q _
            change v (S q) * b q = v (S q) * b (S (S q))
            rw [hS q]
      _ = ∑ q : Fin m, v q * b (S q) := by
        simpa using (Equiv.sum_comp S (fun r => v r * b (S r)))
  simp only [vecPermute]
  rw [hS, hsum]
/-- Two Householder products agree at a coordinate when the coordinate and
every weighted dot-product summand agree. -/
theorem matMulVec_householder_eq_of_coordinate_weighted_eq {m : ℕ}
    (v b c : Fin m → ℝ) (beta : ℝ) (i : Fin m)
    (hcoord : b i = c i)
    (hweighted : ∀ q, v q * b q = v q * c q) :
    matMulVec m (householder m v beta) b i =
      matMulVec m (householder m v beta) c i := by
  rw [householder_matMulVec_eq, householder_matMulVec_eq]
  change b i - beta * v i * (∑ q : Fin m, v q * b q) =
    c i - beta * v i * (∑ q : Fin m, v q * c q)
  rw [hcoord]
  congr 2
  apply Finset.sum_congr rfl
  intro q _
  exact hweighted q
theorem one_le_natCast_sq_of_pos {n : Nat} (hn : 0 < n) :
    (1 : Real) <= (n : Real) ^ 2 := by
  have hn1 : (1 : Real) <= (n : Real) := by exact_mod_cast hn
  nlinarith

end Theorem20_7

end NumStability
