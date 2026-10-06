import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Analysis.FloatingPointArithmetic.IeeeSpecialValueOperations.Results
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter05.Section03.DividedDifferences.Basic

/-!
# Chapter05 Section03 ResidualUnwind Basic

Canonical destination for material split out of
`NumStability.Algorithms.Ch5SourceClosure` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- One active entry of the actual rounded divided-difference recurrence has
both the forward `G_k` factor from (5.9) and its inverse factor used when the
analysis is unwound.  Both are genuine three-operation Stewart counters, so
both deviations from one are bounded by `gamma_3`; the inverse factor is not
obtained by the weaker estimate `gamma_3 / (1-gamma_3)`. -/
theorem fl_dividedDifferenceStep_entry_forward_inverse_gamma3
    (fp : FPModel) (nodes coeffs : ℕ → ℝ) {k j : ℕ}
    (hj : k < j)
    (hden : nodes j - nodes (j - k - 1) ≠ 0)
    (hdenHat : fp.fl_sub (nodes j) (nodes (j - k - 1)) ≠ 0)
    (hγ : gammaValid fp 3) :
    ∃ eta rho : ℝ,
      |eta - 1| ≤ gamma fp 3 ∧
      |rho - 1| ≤ gamma fp 3 ∧
      rho * eta = 1 ∧
      fl_dividedDifferenceStep fp nodes coeffs k j =
        eta * dividedDifferenceStep nodes coeffs k j := by
  rcases fl_dividedDifferenceStep_entry_error_factors
      fp nodes coeffs hj hden hdenHat with
    ⟨δnum, δden, δdiv, hδnum, hδden, hδdiv, hstep⟩
  let δ : Fin 3 → ℝ := fun i =>
    if i = 0 then δnum else if i = 1 then δden else δdiv
  let forwardNeg : Fin 3 → Bool := fun i => if i = 1 then true else false
  let inverseNeg : Fin 3 → Bool := fun i => if i = 1 then false else true
  have hδ : ∀ i : Fin 3, |δ i| ≤ fp.u := by
    intro i
    fin_cases i <;> simp [δ, hδnum, hδden, hδdiv]
  rcases prod_signed_error_bound fp 3 δ forwardNeg hδ hγ with
    ⟨thetaF, hthetaF, hforward⟩
  rcases prod_signed_error_bound fp 3 δ inverseNeg hδ hγ with
    ⟨thetaI, hthetaI, hinverse⟩
  let eta := ∏ i : Fin 3,
    (if forwardNeg i then 1 / (1 + δ i) else 1 + δ i)
  let rho := ∏ i : Fin 3,
    (if inverseNeg i then 1 / (1 + δ i) else 1 + δ i)
  have heta : eta =
      (1 + δnum) * (1 / (1 + δden)) * (1 + δdiv) := by
    simp [eta, forwardNeg, δ, Fin.prod_univ_three]
  have hrho : rho =
      (1 / (1 + δnum)) * (1 + δden) * (1 / (1 + δdiv)) := by
    simp [rho, inverseNeg, δ, Fin.prod_univ_three]
  have h1valid : gammaValid fp 1 :=
    gammaValid_mono fp (by omega) hγ
  have hu : fp.u < 1 := by
    unfold gammaValid at h1valid
    simpa using h1valid
  have hnum : 1 + δnum ≠ 0 := by
    have : 0 < 1 + δnum := by linarith [neg_abs_le δnum]
    exact this.ne'
  have hdenFactor : 1 + δden ≠ 0 := by
    have : 0 < 1 + δden := by linarith [neg_abs_le δden]
    exact this.ne'
  have hdiv : 1 + δdiv ≠ 0 := by
    have : 0 < 1 + δdiv := by linarith [neg_abs_le δdiv]
    exact this.ne'
  refine ⟨eta, rho, ?_, ?_, ?_, ?_⟩
  · have : eta = 1 + thetaF := by simpa [eta] using hforward
    rw [this]
    simpa using hthetaF
  · have : rho = 1 + thetaI := by simpa [rho] using hinverse
    rw [this]
    simpa using hthetaI
  · rw [heta, hrho]
    field_simp [hnum, hdenFactor, hdiv]
  · rw [hstep, heta]
    simp [div_eq_mul_inv]
    ring

/-- Higham, 2nd ed., Chapter 5, Section 5.3, equation (5.12), one active
entry of the inverse unwind.  The inverse factor is extracted from the three
rounded operations that produced the entry; it is not a caller-supplied
perturbation certificate. -/
theorem fl_dividedDifferenceStep_entry_inverse_gamma3
    (fp : FPModel) (nodes coeffs : ℕ → ℝ) {k j : ℕ}
    (hj : k < j)
    (hden : nodes j - nodes (j - k - 1) ≠ 0)
    (hdenHat : fp.fl_sub (nodes j) (nodes (j - k - 1)) ≠ 0)
    (hγ : gammaValid fp 3) :
    ∃ rho : ℝ,
      |rho - 1| ≤ gamma fp 3 ∧
      rho * fl_dividedDifferenceStep fp nodes coeffs k j =
        dividedDifferenceStep nodes coeffs k j := by
  rcases fl_dividedDifferenceStep_entry_forward_inverse_gamma3
      fp nodes coeffs hj hden hdenHat hγ with
    ⟨eta, rho, _heta, hrho, hinv, hstep⟩
  refine ⟨rho, hrho, ?_⟩
  rw [hstep]
  calc
    rho * (eta * dividedDifferenceStep nodes coeffs k j) =
        (rho * eta) * dividedDifferenceStep nodes coeffs k j := by ring
    _ = dividedDifferenceStep nodes coeffs k j := by rw [hinv]; ring

/-- The source inverse step `L_k⁻¹ G_k⁻¹`.  The supplied `rho j`
is the concrete inverse Stewart factor for active row `j`; inactive rows are
left unchanged by `dividedDifferenceGMatrixAction`. -/
noncomputable def flDividedDifferenceUnwindStep
    (nodes : ℕ → ℝ) (rho : ℕ → ℝ) (n : ℕ)
    (k : ℕ) (v : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  dividedDifferenceLInvAction nodes n k
    (dividedDifferenceGMatrixAction rho n k v)

/-- `L_k⁻¹ G_k⁻¹` differs componentwise from `L_k⁻¹` by at
most `gamma |L_k⁻¹|`.  This is the literal local perturbation premise
used in Higham's unwind leading to (5.12), now derived from inverse factors. -/
theorem flDividedDifferenceUnwindStep_abs_error
    (nodes : ℕ → ℝ) (rho : ℕ → ℝ) (n k : ℕ)
    (gamma : ℝ) (hgamma : 0 ≤ gamma)
    (hrho : ∀ i : Fin (n + 1), k < i.val →
      |rho i.val - 1| ≤ gamma) :
    ∀ (v : Fin (n + 1) → ℝ) (i : Fin (n + 1)),
      |flDividedDifferenceUnwindStep nodes rho n k v i -
          dividedDifferenceLInvAction nodes n k v i| ≤
        gamma * dividedDifferenceAbsLInvAction nodes n k
          (fun j => |v j|) i := by
  intro v i
  let gv := dividedDifferenceGMatrixAction rho n k v
  have hpoint : ∀ j : Fin (n + 1), |gv j - v j| ≤ gamma * |v j| := by
    intro j
    by_cases hj : j.val ≤ k
    · rw [show gv j = v j by
          simpa [gv] using
            dividedDifferenceGMatrixAction_of_le rho v hj]
      simp [mul_nonneg hgamma (abs_nonneg (v j))]
    · have hgt : k < j.val := Nat.lt_of_not_ge hj
      rw [show gv j = rho j.val * v j by
          simpa [gv] using
            dividedDifferenceGMatrixAction_of_gt rho v hgt]
      have hfactor : rho j.val * v j - v j =
          (rho j.val - 1) * v j := by ring
      rw [hfactor, abs_mul]
      exact mul_le_mul_of_nonneg_right (hrho j hgt) (abs_nonneg (v j))
  have hbase :=
    abs_dividedDifferenceLInvAction_sub_le_absLInvAction
      nodes n k gv v i
  have hmono := dividedDifferenceAbsLInvAction_mono nodes n k
    (fun j => |gv j - v j|) (fun j => gamma * |v j|) hpoint i
  have hsmul := dividedDifferenceAbsLInvAction_smul nodes n k gamma
    (fun j => |v j|) i
  calc
    |flDividedDifferenceUnwindStep nodes rho n k v i -
        dividedDifferenceLInvAction nodes n k v i|
        = |dividedDifferenceLInvAction nodes n k gv i -
            dividedDifferenceLInvAction nodes n k v i| := rfl
    _ ≤ dividedDifferenceAbsLInvAction nodes n k
          (fun j => |gv j - v j|) i := hbase
    _ ≤ dividedDifferenceAbsLInvAction nodes n k
          (fun j => gamma * |v j|) i := hmono
    _ = gamma * dividedDifferenceAbsLInvAction nodes n k
          (fun j => |v j|) i := hsmul

/-- One complete rounded divided-difference sweep can be undone exactly by
`L_k⁻¹ G_k⁻¹`, where every active diagonal entry of `G_k⁻¹` is within
`gamma_3` of one. Both the inverse factors and the equality are constructed
from the actual rounded sweep. -/
theorem fl_dividedDifferenceFiniteCoeffs_succ_exists_unwind_gamma3
    (fp : FPModel) (nodes f : ℕ → ℝ) {n k : ℕ}
    (hden : ∀ j, k < j → j < n + 1 →
      nodes j - nodes (j - k - 1) ≠ 0)
    (hdenHat : ∀ j, k < j → j < n + 1 →
      fp.fl_sub (nodes j) (nodes (j - k - 1)) ≠ 0)
    (hγ : gammaValid fp 3) :
    ∃ rho : ℕ → ℝ,
      (∀ i : Fin (n + 1), k < i.val →
        |rho i.val - 1| ≤ gamma fp 3) ∧
      flDividedDifferenceUnwindStep nodes rho n k
          (fl_dividedDifferenceFiniteCoeffs fp nodes f n (k + 1)) =
        fl_dividedDifferenceFiniteCoeffs fp nodes f n k := by
  classical
  let prev := fl_dividedDifferenceFiniteCoeffs fp nodes f n k
  let rho : ℕ → ℝ := fun j =>
    if hjk : k < j then
      if hjn : j < n + 1 then
        Classical.choose
          (fl_dividedDifferenceStep_entry_inverse_gamma3 fp nodes
            (dividedDifferenceFinToNat prev) hjk
            (hden j hjk hjn) (hdenHat j hjk hjn) hγ)
      else
        1
    else
      1
  have hrho : ∀ i : Fin (n + 1), k < i.val →
      |rho i.val - 1| ≤ gamma fp 3 := by
    intro i hi
    have hspec := Classical.choose_spec
      (fl_dividedDifferenceStep_entry_inverse_gamma3 fp nodes
        (dividedDifferenceFinToNat prev) hi
        (hden i.val hi i.isLt) (hdenHat i.val hi i.isLt) hγ)
    have hile : i.val ≤ n := Nat.lt_succ_iff.mp i.isLt
    simpa [rho, hi, hile] using hspec.1
  have hG :
      dividedDifferenceGMatrixAction rho n k
          (fl_dividedDifferenceFiniteCoeffs fp nodes f n (k + 1)) =
        dividedDifferenceLMatrixAction nodes n k prev := by
    funext i
    by_cases hi : i.val ≤ k
    · rw [dividedDifferenceGMatrixAction_of_le rho _ hi,
        dividedDifferenceLMatrixAction_of_le nodes prev hi]
      change fl_dividedDifferenceStep fp nodes
          (dividedDifferenceFinToNat prev) k i.val = prev i
      rw [fl_dividedDifferenceStep_of_le fp nodes _ hi]
      simp [dividedDifferenceFinToNat, i.isLt]
    · have hgt : k < i.val := Nat.lt_of_not_ge hi
      rw [dividedDifferenceGMatrixAction_of_gt rho _ hgt]
      have hspec := Classical.choose_spec
        (fl_dividedDifferenceStep_entry_inverse_gamma3 fp nodes
          (dividedDifferenceFinToNat prev) hgt
          (hden i.val hgt i.isLt) (hdenHat i.val hgt i.isLt) hγ)
      have hrhoChoose :
          rho i.val = Classical.choose
            (fl_dividedDifferenceStep_entry_inverse_gamma3 fp nodes
              (dividedDifferenceFinToNat prev) hgt
              (hden i.val hgt i.isLt) (hdenHat i.val hgt i.isLt) hγ) := by
        have hile : i.val ≤ n := Nat.lt_succ_iff.mp i.isLt
        simp [rho, hgt, hile]
      rw [hrhoChoose]
      calc
        Classical.choose
              (fl_dividedDifferenceStep_entry_inverse_gamma3 fp nodes
                (dividedDifferenceFinToNat prev) hgt
                (hden i.val hgt i.isLt) (hdenHat i.val hgt i.isLt) hγ) *
            fl_dividedDifferenceFiniteCoeffs fp nodes f n (k + 1) i =
            dividedDifferenceStep nodes (dividedDifferenceFinToNat prev)
              k i.val := by simpa [prev] using hspec.2
        _ = dividedDifferenceLMatrixAction nodes n k prev i := by
          symm
          exact dividedDifferenceLMatrixAction_eq_step nodes prev i
  refine ⟨rho, hrho, ?_⟩
  unfold flDividedDifferenceUnwindStep
  rw [hG]
  funext i
  exact dividedDifferenceLInvAction_LMatrixAction_eq nodes prev
    (fun j hj => hden j.val hj j.isLt) i

/-- The actual rounded divided-difference computation is the reverse product
of the constructed `L_k⁻¹ G_k⁻¹` unwind steps. This is the missing producer
identity behind the formerly conditional residual theorem for (5.12). -/
theorem fl_dividedDifferenceFiniteCoeffs_exists_inverse_unwind_gamma3
    (fp : FPModel) (nodes f : ℕ → ℝ) {n : ℕ} (m : ℕ)
    (hden : ∀ k j, k < j → j < n + 1 →
      nodes j - nodes (j - k - 1) ≠ 0)
    (hdenHat : ∀ k j, k < j → j < n + 1 →
      fp.fl_sub (nodes j) (nodes (j - k - 1)) ≠ 0)
    (hγ : gammaValid fp 3) :
    ∃ rho : ℕ → ℕ → ℝ,
      (∀ k, ∀ i : Fin (n + 1), k < i.val →
        |rho k i.val - 1| ≤ gamma fp 3) ∧
      (fun i : Fin (n + 1) => f i.val) =
        dividedDifferencePerturbedLInvProductAction
          (fun k v => flDividedDifferenceUnwindStep nodes (rho k) n k v)
          m (fl_dividedDifferenceFiniteCoeffs fp nodes f n m) := by
  classical
  let rho : ℕ → ℕ → ℝ := fun k => Classical.choose
    (fl_dividedDifferenceFiniteCoeffs_succ_exists_unwind_gamma3
      fp nodes f (n := n)
      (fun j hj hjn => hden k j hj hjn)
      (fun j hj hjn => hdenHat k j hj hjn) hγ)
  have hrho : ∀ k, ∀ i : Fin (n + 1), k < i.val →
      |rho k i.val - 1| ≤ gamma fp 3 := by
    intro k i hi
    exact (Classical.choose_spec
      (fl_dividedDifferenceFiniteCoeffs_succ_exists_unwind_gamma3
        fp nodes f (n := n)
        (fun j hj hjn => hden k j hj hjn)
        (fun j hj hjn => hdenHat k j hj hjn) hγ)).1 i hi
  have hunwind : ∀ k,
      flDividedDifferenceUnwindStep nodes (rho k) n k
          (fl_dividedDifferenceFiniteCoeffs fp nodes f n (k + 1)) =
        fl_dividedDifferenceFiniteCoeffs fp nodes f n k := by
    intro k
    exact (Classical.choose_spec
      (fl_dividedDifferenceFiniteCoeffs_succ_exists_unwind_gamma3
        fp nodes f (n := n)
        (fun j hj hjn => hden k j hj hjn)
        (fun j hj hjn => hdenHat k j hj hjn) hγ)).2
  refine ⟨rho, hrho, ?_⟩
  induction m with
  | zero => rfl
  | succ m ih =>
      simp only [dividedDifferencePerturbedLInvProductAction]
      rw [hunwind m]
      exact ih

end NumStability
