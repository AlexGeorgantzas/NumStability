import NumStability.Algorithms.Summation.Compensated.FiniteFormat
import NumStability.Analysis.FirstOrder.AsymptoticFamilies
import NumStability.Analysis.Conditioning.LinearSystems.InversePerturbation
import NumStability.Source.Higham.Chapter07.Corollary06.Equilibration.Basic
import NumStability.Source.Higham.Chapter09.DoolittleClosure
import NumStability.Source.Higham.Chapter19.Theorem06.ColumnPivot

/-!
# Chapter07 Equation25 SourceEndpoint Basic

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapters1To9SourceClosure` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open Filter Asymptotics
open scoped BigOperators
open scoped Topology
open scoped Matrix.Norms.Operator

namespace NumStability

/-- The first derivative of inversion at `A`, written using its inverse:
`D(inv)_A[ΔA] = -A⁻¹ ΔA A⁻¹`. -/
noncomputable def higham7_25_inverseLinearizedChange
    (n : ℕ) (Ainv ΔA : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => -matMul n (matMul n Ainv ΔA) Ainv i j

/-- The nonnegative matrix `|A⁻¹| E |A⁻¹|` in the numerator of
Higham's equation (7.25). -/
noncomputable def higham7_25_inverseSensitivity
    (n : ℕ) (Ainv E : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  matMul n (matMul n (absMatrix n Ainv) E) (absMatrix n Ainv)

/-- Unit-radius componentwise perturbations for equation (7.25). -/
def Higham7_25AdmissiblePerturbation
    {n : ℕ} (E ΔA : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, |ΔA i j| ≤ E i j

/-- The sensitivity matrix in (7.25) is componentwise nonnegative. -/
lemma higham7_25_inverseSensitivity_nonneg
    (n : ℕ) (Ainv E : Fin n → Fin n → ℝ)
    (hE : ∀ i j : Fin n, 0 ≤ E i j) :
    ∀ i j : Fin n, 0 ≤ higham7_25_inverseSensitivity n Ainv E i j := by
  have hfirst : ∀ i j : Fin n,
      0 ≤ matMul n (absMatrix n Ainv) E i j :=
    ch7_matMul_nonneg n (absMatrix n Ainv) E
      (by intro i j; exact abs_nonneg _) hE
  exact ch7_matMul_nonneg n
    (matMul n (absMatrix n Ainv) E) (absMatrix n Ainv)
    hfirst (by intro i j; exact abs_nonneg _)

/-- Componentwise derivative domination behind the upper bound in (7.25). -/
theorem higham7_25_inverseLinearizedChange_abs_le
    (n : ℕ) (Ainv E ΔA : Fin n → Fin n → ℝ)
    (hE : ∀ i j : Fin n, 0 ≤ E i j)
    (hΔ : Higham7_25AdmissiblePerturbation E ΔA) :
    ∀ i j : Fin n,
      |higham7_25_inverseLinearizedChange n Ainv ΔA i j| ≤
        higham7_25_inverseSensitivity n Ainv E i j := by
  let M : Fin n → Fin n → ℝ := matMul n Ainv ΔA
  let P : Fin n → Fin n → ℝ := matMul n (absMatrix n Ainv) E
  have hP : ∀ i j : Fin n, 0 ≤ P i j :=
    ch7_matMul_nonneg n (absMatrix n Ainv) E
      (by intro i j; exact abs_nonneg _) hE
  have hM : ∀ i j : Fin n, |M i j| ≤ P i j := by
    intro i j
    have h := ch7_matMul_abs_le_of_scaled_abs_le
      n Ainv ΔA (absMatrix n Ainv) E 1 1
      (by norm_num) (by norm_num)
      (by intro a b; exact abs_nonneg _) hE
      (by intro a b; simp [absMatrix])
      (by intro a b; simpa using hΔ a b) i j
    simpa [M, P] using h
  intro i j
  have h := ch7_matMul_abs_le_of_scaled_abs_le
    n M Ainv P (absMatrix n Ainv) 1 1
    (by norm_num) (by norm_num) hP
    (by intro a b; exact abs_nonneg _)
    (by intro a b; simpa using hM a b)
    (by intro a b; simp [absMatrix]) i j
  simpa [higham7_25_inverseLinearizedChange,
    higham7_25_inverseSensitivity, M, P, abs_neg] using h

/-- Matrix-infinity-norm form of the derivative upper bound in (7.25). -/
theorem higham7_25_inverseLinearizedChange_infNorm_le
    (n : ℕ) (Ainv E ΔA : Fin n → Fin n → ℝ)
    (hE : ∀ i j : Fin n, 0 ≤ E i j)
    (hΔ : Higham7_25AdmissiblePerturbation E ΔA) :
    infNorm (higham7_25_inverseLinearizedChange n Ainv ΔA) ≤
      infNorm (higham7_25_inverseSensitivity n Ainv E) := by
  apply infNorm_le_of_row_sum_le
  · intro i
    calc
      ∑ j : Fin n, |higham7_25_inverseLinearizedChange n Ainv ΔA i j| ≤
          ∑ j : Fin n, higham7_25_inverseSensitivity n Ainv E i j :=
        Finset.sum_le_sum (fun j _ =>
          higham7_25_inverseLinearizedChange_abs_le n Ainv E ΔA hE hΔ i j)
      _ = ∑ j : Fin n, |higham7_25_inverseSensitivity n Ainv E i j| := by
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_of_nonneg
          (higham7_25_inverseSensitivity_nonneg n Ainv E hE i j)]
      _ ≤ infNorm (higham7_25_inverseSensitivity n Ainv E) :=
        row_sum_le_infNorm (higham7_25_inverseSensitivity n Ainv E) i
  · exact infNorm_nonneg _

/-- The displayed normalized upper bound in Higham equation (7.25).  The
denominator is written exactly as in the source; `infNorm_absMatrix` identifies
it with `‖A⁻¹‖∞`. -/
theorem higham7_25_inverseLinearized_ratio_le
    {n : ℕ} (hn : 0 < n)
    (Ainv E ΔA : Fin n → Fin n → ℝ)
    (hE : ∀ i j : Fin n, 0 ≤ E i j)
    (hΔ : Higham7_25AdmissiblePerturbation E ΔA) :
    infNorm (higham7_25_inverseLinearizedChange n Ainv ΔA) /
        infNorm Ainv ≤
      infNorm (higham7_25_inverseSensitivity n Ainv E) /
        infNorm (absMatrix n Ainv) := by
  rw [infNorm_absMatrix hn Ainv]
  exact div_le_div_of_nonneg_right
    (higham7_25_inverseLinearizedChange_infNorm_le n Ainv E ΔA hE hΔ)
    (infNorm_nonneg Ainv)

/-- The source equality hypothesis `|A⁻¹| = D₁ A⁻¹ D₂`, with
`D₁,D₂` diagonal sign matrices. -/
def Higham7_25InverseSignEquivalent
    {n : ℕ} (Ainv : Fin n → Fin n → ℝ) : Prop :=
  ∃ r c : Fin n → ℝ,
    (∀ i : Fin n, r i ^ 2 = 1) ∧
      (∀ j : Fin n, c j ^ 2 = 1) ∧
      ∀ i j : Fin n, |Ainv i j| = r i * Ainv i j * c j

/-- The perturbation that realizes equality in (7.25) under sign
equivalence. -/
def higham7_25_signAttainingPerturbation
    {n : ℕ} (E : Fin n → Fin n → ℝ) (r c : Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => c i * E i j * r j

lemma higham7_25_signAttainingPerturbation_admissible
    {n : ℕ} (E : Fin n → Fin n → ℝ) (r c : Fin n → ℝ)
    (hE : ∀ i j : Fin n, 0 ≤ E i j)
    (hr : ∀ i : Fin n, r i ^ 2 = 1)
    (hc : ∀ j : Fin n, c j ^ 2 = 1) :
    Higham7_25AdmissiblePerturbation E
      (higham7_25_signAttainingPerturbation E r c) := by
  intro i j
  rw [show |higham7_25_signAttainingPerturbation E r c i j| = E i j by
    simp [higham7_25_signAttainingPerturbation, abs_mul,
      higham7_abs_eq_one_of_sq_eq_one (hr j),
      higham7_abs_eq_one_of_sq_eq_one (hc i), abs_of_nonneg (hE i j)]]

/-- The sign perturbation makes every triangle inequality in the derivative
bound an equality. -/
theorem higham7_25_signAttainingPerturbation_abs_eq
    {n : ℕ} (Ainv E : Fin n → Fin n → ℝ) (r c : Fin n → ℝ)
    (hE : ∀ i j : Fin n, 0 ≤ E i j)
    (hr : ∀ i : Fin n, r i ^ 2 = 1)
    (hc : ∀ j : Fin n, c j ^ 2 = 1)
    (hsign : ∀ i j : Fin n, |Ainv i j| = r i * Ainv i j * c j) :
    ∀ i j : Fin n,
      |higham7_25_inverseLinearizedChange n Ainv
          (higham7_25_signAttainingPerturbation E r c) i j| =
        higham7_25_inverseSensitivity n Ainv E i j := by
  intro i j
  have hleft : ∀ k : Fin n,
      Ainv i k * c k = r i * |Ainv i k| := by
    intro k
    calc
      Ainv i k * c k = r i ^ 2 * (Ainv i k * c k) := by
        rw [hr i]
        ring
      _ = r i * (r i * Ainv i k * c k) := by ring
      _ = r i * |Ainv i k| := by rw [← hsign i k]
  have hright : ∀ l : Fin n,
      r l * Ainv l j = |Ainv l j| * c j := by
    intro l
    calc
      r l * Ainv l j = (r l * Ainv l j) * c j ^ 2 := by
        rw [hc j]
        ring
      _ = (r l * Ainv l j * c j) * c j := by ring
      _ = |Ainv l j| * c j := by rw [← hsign l j]
  have hcore :
      matMul n
          (matMul n Ainv (higham7_25_signAttainingPerturbation E r c))
          Ainv i j =
        r i * higham7_25_inverseSensitivity n Ainv E i j * c j := by
    simp only [matMul, higham7_25_signAttainingPerturbation,
      higham7_25_inverseSensitivity, absMatrix]
    calc
      ∑ l : Fin n, (∑ k : Fin n, Ainv i k * (c k * E k l * r l)) * Ainv l j =
          ∑ l : Fin n,
            (r i * (∑ k : Fin n, |Ainv i k| * E k l) * r l) * Ainv l j := by
        apply Finset.sum_congr rfl
        intro l _
        congr 1
        calc
          ∑ k : Fin n, Ainv i k * (c k * E k l * r l) =
              ∑ k : Fin n, r i * (|Ainv i k| * E k l) * r l := by
            apply Finset.sum_congr rfl
            intro k _
            rw [show Ainv i k * (c k * E k l * r l) =
                (Ainv i k * c k) * E k l * r l by ring,
              hleft k]
            ring
          _ = r i * (∑ k : Fin n, |Ainv i k| * E k l) * r l := by
            rw [Finset.mul_sum, Finset.sum_mul]
      _ = ∑ l : Fin n,
          r i * ((∑ k : Fin n, |Ainv i k| * E k l) * |Ainv l j|) * c j := by
        apply Finset.sum_congr rfl
        intro l _
        rw [show
            (r i * (∑ k : Fin n, |Ainv i k| * E k l) * r l) * Ainv l j =
              r i * (∑ k : Fin n, |Ainv i k| * E k l) *
                (r l * Ainv l j) by ring,
          hright l]
        ring
      _ = r i *
          (∑ l : Fin n,
            (∑ k : Fin n, |Ainv i k| * E k l) * |Ainv l j|) * c j := by
        rw [Finset.mul_sum, Finset.sum_mul]
  rw [higham7_25_inverseLinearizedChange, hcore, abs_neg,
    abs_mul, abs_mul,
    higham7_abs_eq_one_of_sq_eq_one (hr i),
    higham7_abs_eq_one_of_sq_eq_one (hc j),
    abs_of_nonneg (higham7_25_inverseSensitivity_nonneg n Ainv E hE i j)]
  ring

/-- Equality of matrix infinity norms for the sign-attaining perturbation. -/
theorem higham7_25_signAttainingPerturbation_infNorm_eq
    {n : ℕ} (hn : 0 < n)
    (Ainv E : Fin n → Fin n → ℝ) (r c : Fin n → ℝ)
    (hE : ∀ i j : Fin n, 0 ≤ E i j)
    (hr : ∀ i : Fin n, r i ^ 2 = 1)
    (hc : ∀ j : Fin n, c j ^ 2 = 1)
    (hsign : ∀ i j : Fin n, |Ainv i j| = r i * Ainv i j * c j) :
    infNorm (higham7_25_inverseLinearizedChange n Ainv
        (higham7_25_signAttainingPerturbation E r c)) =
      infNorm (higham7_25_inverseSensitivity n Ainv E) := by
  have habsMatrix :
      absMatrix n (higham7_25_inverseLinearizedChange n Ainv
          (higham7_25_signAttainingPerturbation E r c)) =
        higham7_25_inverseSensitivity n Ainv E := by
    funext i j
    exact higham7_25_signAttainingPerturbation_abs_eq
      Ainv E r c hE hr hc hsign i j
  calc
    infNorm (higham7_25_inverseLinearizedChange n Ainv
        (higham7_25_signAttainingPerturbation E r c)) =
        infNorm (absMatrix n (higham7_25_inverseLinearizedChange n Ainv
          (higham7_25_signAttainingPerturbation E r c))) :=
      (infNorm_absMatrix hn _).symm
    _ = infNorm (higham7_25_inverseSensitivity n Ainv E) := by
      rw [habsMatrix]

/-- Unit-ball values of the matrix-infinity norm of the inversion derivative.
This is the standard first-order characterization of the source limit
defining `μ_E(A)` in equation (7.25). -/
def Higham7_25InverseLinearizedConditionSet
    {n : ℕ} (Ainv E : Fin n → Fin n → ℝ) : Set ℝ :=
  {q | ∃ ΔA : Fin n → Fin n → ℝ,
    Higham7_25AdmissiblePerturbation E ΔA ∧
      q = infNorm (higham7_25_inverseLinearizedChange n Ainv ΔA) /
        infNorm Ainv}

/-- Matrix-infinity relative condition number of inversion in the componentwise
perturbation direction `E`, expressed through the derivative unit ball. -/
noncomputable def higham7_25_inverseLinearizedCondition
    {n : ℕ} (Ainv E : Fin n → Fin n → ℝ) : ℝ :=
  sSup (Higham7_25InverseLinearizedConditionSet Ainv E)

/-- Upper-bound half of equation (7.25), now at the actual derivative
condition-number supremum. -/
theorem higham7_25_inverseLinearizedCondition_le
    {n : ℕ} (hn : 0 < n) (Ainv E : Fin n → Fin n → ℝ)
    (hE : ∀ i j : Fin n, 0 ≤ E i j) :
    higham7_25_inverseLinearizedCondition Ainv E ≤
      infNorm (higham7_25_inverseSensitivity n Ainv E) /
        infNorm (absMatrix n Ainv) := by
  let S : Set ℝ := Higham7_25InverseLinearizedConditionSet Ainv E
  let K : ℝ := infNorm (higham7_25_inverseSensitivity n Ainv E) /
    infNorm (absMatrix n Ainv)
  let Δzero : Fin n → Fin n → ℝ := 0
  let qzero : ℝ :=
    infNorm (higham7_25_inverseLinearizedChange n Ainv Δzero) / infNorm Ainv
  have hΔzero : Higham7_25AdmissiblePerturbation E Δzero := by
    intro i j
    simpa [Δzero] using hE i j
  have hqzero : qzero ∈ S := by
    exact ⟨Δzero, hΔzero, rfl⟩
  have hupper : ∀ q : ℝ, q ∈ S → q ≤ K := by
    intro q hq
    rcases hq with ⟨ΔA, hΔ, rfl⟩
    exact higham7_25_inverseLinearized_ratio_le hn Ainv E ΔA hE hΔ
  change sSup S ≤ K
  exact csSup_le ⟨qzero, hqzero⟩ hupper

/-- Under `|A⁻¹| = D₁ A⁻¹ D₂`, the sign perturbation belongs to
the unit ball and attains the displayed right-hand side of (7.25). -/
theorem higham7_25_inverseLinearizedCondition_eq_of_signEquivalent
    {n : ℕ} (hn : 0 < n) (Ainv E : Fin n → Fin n → ℝ)
    (hE : ∀ i j : Fin n, 0 ≤ E i j)
    (hsign : Higham7_25InverseSignEquivalent Ainv) :
    higham7_25_inverseLinearizedCondition Ainv E =
      infNorm (higham7_25_inverseSensitivity n Ainv E) /
        infNorm (absMatrix n Ainv) := by
  rcases hsign with ⟨r, c, hr, hc, hentries⟩
  let S : Set ℝ := Higham7_25InverseLinearizedConditionSet Ainv E
  let K : ℝ := infNorm (higham7_25_inverseSensitivity n Ainv E) /
    infNorm (absMatrix n Ainv)
  let ΔA : Fin n → Fin n → ℝ :=
    higham7_25_signAttainingPerturbation E r c
  have hΔ : Higham7_25AdmissiblePerturbation E ΔA :=
    higham7_25_signAttainingPerturbation_admissible E r c hE hr hc
  have hratio :
      infNorm (higham7_25_inverseLinearizedChange n Ainv ΔA) /
          infNorm Ainv = K := by
    rw [higham7_25_signAttainingPerturbation_infNorm_eq
      hn Ainv E r c hE hr hc hentries]
    exact congrArg
      (fun d : ℝ => infNorm (higham7_25_inverseSensitivity n Ainv E) / d)
      (infNorm_absMatrix hn Ainv).symm
  have hKmem : K ∈ S := ⟨ΔA, hΔ, hratio.symm⟩
  have hupper : ∀ q : ℝ, q ∈ S → q ≤ K := by
    intro q hq
    rcases hq with ⟨Δ, hΔ', rfl⟩
    exact higham7_25_inverseLinearized_ratio_le hn Ainv E Δ hE hΔ'
  have hbdd : BddAbove S := ⟨K, hupper⟩
  change sSup S = K
  exact le_antisymm (csSup_le ⟨K, hKmem⟩ hupper)
    (le_csSup hbdd hKmem)

/-- Higham equation (7.25), source-facing endpoint.  `Ainv` is required to be
the genuine inverse of `A`; the derivative condition is bounded by the
printed ratio, and the book's diagonal-sign hypothesis upgrades that bound to
equality. -/
theorem higham7_25_source_inverseCondition_upper_and_sign_equality
    {n : ℕ} (hn : 0 < n)
    (A Ainv E : Fin n → Fin n → ℝ)
    (hInv : IsInverse n A Ainv)
    (hE : ∀ i j : Fin n, 0 ≤ E i j) :
    IsInverse n A Ainv ∧
      higham7_25_inverseLinearizedCondition Ainv E ≤
        infNorm (higham7_25_inverseSensitivity n Ainv E) /
          infNorm (absMatrix n Ainv) ∧
      (Higham7_25InverseSignEquivalent Ainv →
        higham7_25_inverseLinearizedCondition Ainv E =
          infNorm (higham7_25_inverseSensitivity n Ainv E) /
            infNorm (absMatrix n Ainv)) := by
  exact ⟨hInv, higham7_25_inverseLinearizedCondition_le hn Ainv E hE,
    higham7_25_inverseLinearizedCondition_eq_of_signEquivalent
      hn Ainv E hE⟩

end NumStability
