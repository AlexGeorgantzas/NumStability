import NumStability.Algorithms.HighamChapter9
import NumStability.Algorithms.HighamChapter11
import NumStability.Analysis.FirstOrder

namespace NumStability

open scoped BigOperators

/-!
# Higham Chapter 11 / Chapter 9 forward-error bridge

This module supplies the bridge that is printed immediately before (11.7).
The old Chapter 11 entry point only recorded a scalar inequality.  Here the
factorization term is the literal

`P^T |L_hat| |D_hat| |L_hat^T| P`,

the perturbation estimate is derived from two componentwise backward-error
certificates, and `O(u^2)` is represented by `FirstOrderLe`.
-/

/-- The entry of `P^T |L_hat| |D_hat| |L_hat^T| P` occurring in (11.7).

`sigma` maps factor coordinates to the original coordinates.  Consequently,
`sigma.symm i` pulls an original coordinate back to the factor coordinates.
-/
noncomputable def higham11_7_permutedAbsLDLT {n : ℕ} (sigma : Fin n ≃ Fin n)
    (L_hat D_hat : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  ∑ p : Fin n, ∑ q : Fin n,
    |L_hat (sigma.symm i) p| * |D_hat p q| * |L_hat (sigma.symm j) q|

theorem higham11_7_permutedAbsLDLT_nonneg {n : ℕ} (sigma : Fin n ≃ Fin n)
    (L_hat D_hat : Fin n → Fin n → ℝ) (i j : Fin n) :
    0 ≤ higham11_7_permutedAbsLDLT sigma L_hat D_hat i j := by
  unfold higham11_7_permutedAbsLDLT
  exact Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ =>
    mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)

/-- The source matrix envelope
`|A| + P^T |L_hat| |D_hat| |L_hat^T| P` in (11.7). -/
noncomputable def higham11_7_totalBackwardEnvelope {n : ℕ}
    (A : Fin n → Fin n → ℝ) (sigma : Fin n ≃ Fin n)
    (L_hat D_hat : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  |A i j| + higham11_7_permutedAbsLDLT sigma L_hat D_hat i j

theorem higham11_7_totalBackwardEnvelope_nonneg {n : ℕ}
    (A : Fin n → Fin n → ℝ) (sigma : Fin n ≃ Fin n)
    (L_hat D_hat : Fin n → Fin n → ℝ) (i j : Fin n) :
    0 ≤ higham11_7_totalBackwardEnvelope A sigma L_hat D_hat i j :=
  add_nonneg (abs_nonneg _) (higham11_7_permutedAbsLDLT_nonneg sigma L_hat D_hat i j)

/-- For a nonnegative componentwise matrix envelope `H`, the infinity norm of
`|A⁻¹|H`, written directly as a finite maximum of row sums. -/
noncomputable def higham11_7_envelopeCondition {n : ℕ} (hn : 0 < n)
    (A_inv H : Fin n → Fin n → ℝ) : ℝ :=
  Finset.sup' Finset.univ
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
    (fun i => ∑ j : Fin n, |A_inv i j| * (∑ k : Fin n, H j k))

/-- The literal norm
`‖ |A⁻¹| P^T |L_hat| |D_hat| |L_hat^T| P ‖_∞` from (11.7),
written as the maximum of its nonnegative row sums. -/
noncomputable def higham11_7_factorCondition {n : ℕ} (hn : 0 < n)
    (A_inv : Fin n → Fin n → ℝ) (sigma : Fin n ≃ Fin n)
    (L_hat D_hat : Fin n → Fin n → ℝ) : ℝ :=
  higham11_7_envelopeCondition hn A_inv
    (higham11_7_permutedAbsLDLT sigma L_hat D_hat)

theorem higham11_7_factorCondition_row_le {n : ℕ} (hn : 0 < n)
    (A_inv : Fin n → Fin n → ℝ) (sigma : Fin n ≃ Fin n)
    (L_hat D_hat : Fin n → Fin n → ℝ) (i : Fin n) :
    (∑ j : Fin n, |A_inv i j| *
      (∑ k : Fin n, higham11_7_permutedAbsLDLT sigma L_hat D_hat j k)) ≤
      higham11_7_factorCondition hn A_inv sigma L_hat D_hat := by
  unfold higham11_7_factorCondition
  unfold higham11_7_envelopeCondition
  exact Finset.le_sup'
    (fun i : Fin n => ∑ j : Fin n, |A_inv i j| *
      (∑ k : Fin n, higham11_7_permutedAbsLDLT sigma L_hat D_hat j k))
    (Finset.mem_univ i)

theorem higham11_7_factorCondition_nonneg {n : ℕ} (hn : 0 < n)
    (A_inv : Fin n → Fin n → ℝ) (sigma : Fin n ≃ Fin n)
    (L_hat D_hat : Fin n → Fin n → ℝ) :
    0 ≤ higham11_7_factorCondition hn A_inv sigma L_hat D_hat := by
  let i0 : Fin n := ⟨0, hn⟩
  have hrow : 0 ≤ ∑ j : Fin n, |A_inv i0 j| *
      (∑ k : Fin n, higham11_7_permutedAbsLDLT sigma L_hat D_hat j k) := by
    exact Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _)
      (Finset.sum_nonneg fun k _ =>
        higham11_7_permutedAbsLDLT_nonneg sigma L_hat D_hat j k)
  exact hrow.trans
    (higham11_7_factorCondition_row_le hn A_inv sigma L_hat D_hat i0)

/-- The Neumann-series condition used by the exact denominator form of
(11.7).  Its first summand is Chapter 9's global Skeel condition, and its
second summand is the new factorization term. -/
noncomputable def higham11_7_totalGlobalCondition {n : ℕ} (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (sigma : Fin n ≃ Fin n)
    (L_hat D_hat : Fin n → Fin n → ℝ) : ℝ :=
  condSkeel n hn A A_inv +
    higham11_7_factorCondition hn A_inv sigma L_hat D_hat

theorem higham11_7_totalGlobalCondition_nonneg {n : ℕ} (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (sigma : Fin n ≃ Fin n)
    (L_hat D_hat : Fin n → Fin n → ℝ) :
    0 ≤ higham11_7_totalGlobalCondition hn A A_inv sigma L_hat D_hat :=
  add_nonneg (higham9_23_condSkeel_nonneg n hn A A_inv)
    (higham11_7_factorCondition_nonneg hn A_inv sigma L_hat D_hat)

/-- Each row of `|A⁻¹|` times the total Chapter 11 envelope is bounded by the
global condition used in the exact perturbation theorem. -/
theorem higham11_7_totalBackwardEnvelope_row_le_globalCondition {n : ℕ}
    (hn : 0 < n) (A A_inv : Fin n → Fin n → ℝ)
    (sigma : Fin n ≃ Fin n) (L_hat D_hat : Fin n → Fin n → ℝ)
    (i : Fin n) :
    (∑ j : Fin n, |A_inv i j| *
      (∑ k : Fin n, higham11_7_totalBackwardEnvelope
        A sigma L_hat D_hat j k)) ≤
      higham11_7_totalGlobalCondition hn A A_inv sigma L_hat D_hat := by
  have hA :
      (∑ j : Fin n, |A_inv i j| * (∑ k : Fin n, |A j k|)) ≤
        condSkeel n hn A A_inv := by
    unfold condSkeel
    exact Finset.le_sup'
      (fun i : Fin n =>
        ∑ j : Fin n, |A_inv i j| * (∑ k : Fin n, |A j k|))
      (Finset.mem_univ i)
  have hF := higham11_7_factorCondition_row_le hn A_inv sigma L_hat D_hat i
  unfold higham11_7_totalBackwardEnvelope higham11_7_totalGlobalCondition
  simp_rw [Finset.sum_add_distrib, mul_add, Finset.sum_add_distrib]
  exact add_le_add hA hF

/-- The total solution-dependent Chapter 11 condition is bounded by the two
terms printed on the first line of (11.7). -/
theorem higham11_7_totalConditionAtSolution_le {n : ℕ} (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (sigma : Fin n ≃ Fin n)
    (L_hat D_hat : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hx : 0 < infNormVec x) :
    ch7ForwardBoundEF n hn A_inv
        (higham11_7_totalBackwardEnvelope A sigma L_hat D_hat)
        (fun _ => 0) x / infNormVec x ≤
      ch7SkeelCondAtSolutionInf n hn A A_inv x +
        higham11_7_factorCondition hn A_inv sigma L_hat D_hat := by
  let H := higham11_7_permutedAbsLDLT sigma L_hat D_hat
  let CA := ch7ForwardBoundEF n hn A_inv (fun i j => |A i j|) (fun _ => 0) x
  let CF := higham11_7_factorCondition hn A_inv sigma L_hat D_hat
  have hCArow : ∀ i : Fin n,
      ch7AmplifiedRhsEF n A_inv (fun i j => |A i j|) (fun _ => 0) x i ≤ CA := by
    intro i
    dsimp [CA, ch7ForwardBoundEF]
    exact Finset.le_sup' _ (Finset.mem_univ i)
  have hHrow : ∀ i : Fin n,
      (∑ j : Fin n, |A_inv i j| * (∑ k : Fin n, H j k * |x k|)) ≤
        infNormVec x * CF := by
    intro i
    have hinner : ∀ j : Fin n,
        (∑ k : Fin n, H j k * |x k|) ≤
          (∑ k : Fin n, H j k) * infNormVec x := by
      intro j
      calc
        (∑ k : Fin n, H j k * |x k|)
            ≤ ∑ k : Fin n, H j k * infNormVec x := by
              apply Finset.sum_le_sum
              intro k _
              exact mul_le_mul_of_nonneg_left (abs_le_infNormVec x k)
                (higham11_7_permutedAbsLDLT_nonneg sigma L_hat D_hat j k)
        _ = (∑ k : Fin n, H j k) * infNormVec x := by
              rw [Finset.sum_mul]
    calc
      (∑ j : Fin n, |A_inv i j| * (∑ k : Fin n, H j k * |x k|))
          ≤ ∑ j : Fin n, |A_inv i j| *
              ((∑ k : Fin n, H j k) * infNormVec x) := by
            apply Finset.sum_le_sum
            intro j _
            exact mul_le_mul_of_nonneg_left (hinner j) (abs_nonneg _)
      _ = infNormVec x *
          (∑ j : Fin n, |A_inv i j| * (∑ k : Fin n, H j k)) := by
            rw [mul_comm (infNormVec x), Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ ≤ infNormVec x * CF := by
            apply mul_le_mul_of_nonneg_left
            · simpa [H, CF] using
                higham11_7_factorCondition_row_le hn A_inv sigma L_hat D_hat i
            · exact infNormVec_nonneg x
  have htotal : ch7ForwardBoundEF n hn A_inv
      (higham11_7_totalBackwardEnvelope A sigma L_hat D_hat)
      (fun _ => 0) x ≤ CA + infNormVec x * CF := by
    unfold ch7ForwardBoundEF
    apply Finset.sup'_le
    intro i _
    calc
      ch7AmplifiedRhsEF n A_inv
          (higham11_7_totalBackwardEnvelope A sigma L_hat D_hat)
          (fun _ => 0) x i =
          ch7AmplifiedRhsEF n A_inv (fun i j => |A i j|) (fun _ => 0) x i +
            ∑ j : Fin n, |A_inv i j| * (∑ k : Fin n, H j k * |x k|) := by
              simp [ch7AmplifiedRhsEF, higham11_7_totalBackwardEnvelope, H,
                mul_add, add_mul, Finset.sum_add_distrib]
      _ ≤ CA + infNormVec x * CF := add_le_add (hCArow i) (hHrow i)
  have hx0 : infNormVec x ≠ 0 := ne_of_gt hx
  calc
    ch7ForwardBoundEF n hn A_inv
        (higham11_7_totalBackwardEnvelope A sigma L_hat D_hat)
        (fun _ => 0) x / infNormVec x
        ≤ (CA + infNormVec x * CF) / infNormVec x :=
          div_le_div_of_nonneg_right htotal (le_of_lt hx)
    _ = CA / infNormVec x + CF := by field_simp
    _ = ch7SkeelCondAtSolutionInf n hn A A_inv x +
        higham11_7_factorCondition hn A_inv sigma L_hat D_hat := by
          rfl

/-- Exact denominator form behind the first line of (11.7).

The two componentwise hypotheses are the solve error (`eta |A|`) and the
block-LDLT factorization error (`eta P^T|L_hat||D_hat||L_hat^T|P`).  The
conclusion is derived from Chapter 7's exact componentwise perturbation
theorem; no forward-error conclusion is assumed.
-/
theorem higham11_7_forwardError_exact_from_backward_errors {n : ℕ}
    (hn : 0 < n) (A A_inv : Fin n → Fin n → ℝ)
    (sigma : Fin n ≃ Fin n) (L_hat D_hat : Fin n → Fin n → ℝ)
    (x x_hat b : Fin n → ℝ)
    (DeltaSolve DeltaFactor : Fin n → Fin n → ℝ) (eta : ℝ)
    (heta : 0 ≤ eta)
    (hSolve : ∀ i j : Fin n, |DeltaSolve i j| ≤ eta * |A i j|)
    (hFactor : ∀ i j : Fin n, |DeltaFactor i j| ≤
      eta * higham11_7_permutedAbsLDLT sigma L_hat D_hat i j)
    (hInv : IsLeftInverse n A A_inv)
    (hAx : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hPerturbed : ∀ i : Fin n,
      ∑ j : Fin n, (A i j + (DeltaSolve i j + DeltaFactor i j)) * x_hat j = b i)
    (hsmall : eta * higham11_7_totalGlobalCondition
      hn A A_inv sigma L_hat D_hat < 1)
    (hx : 0 < infNormVec x) :
    infNormVec (fun i => x i - x_hat i) / infNormVec x ≤
      eta / (1 - eta * higham11_7_totalGlobalCondition
        hn A A_inv sigma L_hat D_hat) *
        (ch7SkeelCondAtSolutionInf n hn A A_inv x +
          higham11_7_factorCondition hn A_inv sigma L_hat D_hat) := by
  let Delta : Fin n → Fin n → ℝ := fun i j => DeltaSolve i j + DeltaFactor i j
  let E := higham11_7_totalBackwardEnvelope A sigma L_hat D_hat
  let M := higham11_7_totalGlobalCondition hn A A_inv sigma L_hat D_hat
  have hDelta : ∀ i j : Fin n, |Delta i j| ≤ eta * E i j := by
    intro i j
    calc
      |Delta i j| ≤ |DeltaSolve i j| + |DeltaFactor i j| := abs_add_le _ _
      _ ≤ eta * |A i j| +
          eta * higham11_7_permutedAbsLDLT sigma L_hat D_hat i j :=
            add_le_add (hSolve i j) (hFactor i j)
      _ = eta * E i j := by
            simp [E, higham11_7_totalBackwardEnvelope, mul_add]
  have hraw := componentwise_forward_error_exact_relative_infNorm
    n hn A A_inv x x_hat b Delta (fun _ => 0) E (fun _ => 0) eta heta
    hDelta (fun i => by simp)
    (fun i j => by
      simpa [E] using higham11_7_totalBackwardEnvelope_nonneg
        A sigma L_hat D_hat i j)
    (fun _ => le_rfl) hInv hAx (by
      intro i
      simpa [Delta] using hPerturbed i)
    M (by
      intro i
      simpa [E, M] using
        higham11_7_totalBackwardEnvelope_row_le_globalCondition
          hn A A_inv sigma L_hat D_hat i)
    (by simpa [M] using hsmall) hx
  have hcoef_nonneg :
      0 ≤ eta / (1 - eta * M) := by
    have hden : 0 < 1 - eta * M := by simpa [M] using sub_pos.mpr hsmall
    exact div_nonneg heta (le_of_lt hden)
  exact hraw.trans (mul_le_mul_of_nonneg_left
    (higham11_7_totalConditionAtSolution_le
      hn A A_inv sigma L_hat D_hat x hx) hcoef_nonneg)

/-- Exact denominator form of (11.7) from the *total* solve backward error.

The concrete block-LDLT executor in Theorem 11.3 produces a single
perturbation `DeltaTotal` satisfying `(A + DeltaTotal) x_hat = b`; it does not
present that perturbation as an artificial sum of independently bounded solve
and factor terms.  This theorem is the source-faithful adapter for that output:
the total perturbation is bounded directly by
`eta * (|A| + P^T|L_hat||D_hat||L_hat^T|P)`.
-/
theorem higham11_7_forwardError_exact_from_total_backward_error {n : ℕ}
    (hn : 0 < n) (A A_inv : Fin n → Fin n → ℝ)
    (sigma : Fin n ≃ Fin n) (L_hat D_hat : Fin n → Fin n → ℝ)
    (x x_hat b : Fin n → ℝ)
    (DeltaTotal : Fin n → Fin n → ℝ) (eta : ℝ)
    (heta : 0 ≤ eta)
    (hTotal : ∀ i j : Fin n, |DeltaTotal i j| ≤
      eta * higham11_7_totalBackwardEnvelope A sigma L_hat D_hat i j)
    (hInv : IsLeftInverse n A A_inv)
    (hAx : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hPerturbed : ∀ i : Fin n,
      ∑ j : Fin n, (A i j + DeltaTotal i j) * x_hat j = b i)
    (hsmall : eta * higham11_7_totalGlobalCondition
      hn A A_inv sigma L_hat D_hat < 1)
    (hx : 0 < infNormVec x) :
    infNormVec (fun i => x i - x_hat i) / infNormVec x ≤
      eta / (1 - eta * higham11_7_totalGlobalCondition
        hn A A_inv sigma L_hat D_hat) *
        (ch7SkeelCondAtSolutionInf n hn A A_inv x +
          higham11_7_factorCondition hn A_inv sigma L_hat D_hat) := by
  let E := higham11_7_totalBackwardEnvelope A sigma L_hat D_hat
  let M := higham11_7_totalGlobalCondition hn A A_inv sigma L_hat D_hat
  have hraw := componentwise_forward_error_exact_relative_infNorm
    n hn A A_inv x x_hat b DeltaTotal (fun _ => 0) E (fun _ => 0) eta heta
    (by simpa [E] using hTotal) (fun i => by simp)
    (fun i j => by
      simpa [E] using higham11_7_totalBackwardEnvelope_nonneg
        A sigma L_hat D_hat i j)
    (fun _ => le_rfl) hInv hAx (by
      intro i
      simpa using hPerturbed i)
    M (by
      intro i
      simpa [E, M] using
        higham11_7_totalBackwardEnvelope_row_le_globalCondition
          hn A A_inv sigma L_hat D_hat i)
    (by simpa [M] using hsmall) hx
  have hcoef_nonneg : 0 ≤ eta / (1 - eta * M) := by
    have hden : 0 < 1 - eta * M := by simpa [M] using sub_pos.mpr hsmall
    exact div_nonneg heta (le_of_lt hden)
  exact hraw.trans (mul_le_mul_of_nonneg_left
    (higham11_7_totalConditionAtSolution_le
      hn A A_inv sigma L_hat D_hat x hx) hcoef_nonneg)

/-- Generalized denominator expansion used by (11.7).

Compared with (9.23), `denCond` controls the Neumann denominator while
`displayCond` is the sharper solution-dependent quantity in the displayed
leading term.  They need not be equal.
-/
theorem higham11_7_firstOrderLe_of_denominator
    {u eta p_n denCond displayCond value : ℝ}
    (hu : 0 ≤ u) (heta : 0 ≤ eta) (hp : 0 ≤ p_n)
    (hdenCond : 0 ≤ denCond) (hdisplay : 0 ≤ displayCond)
    (heta_le : eta ≤ p_n * u) (hsmall : eta * denCond < 1)
    (hvalue : value ≤ eta / (1 - eta * denCond) * displayCond) :
    FirstOrderLe u (p_n * u * displayCond) value := by
  let b : ℝ := p_n * u
  let a : ℝ := eta * denCond
  have hb : 0 ≤ b := mul_nonneg hp hu
  have heta_b : eta ≤ b := by simpa [b] using heta_le
  have ha : 0 ≤ a := mul_nonneg heta hdenCond
  have hden : 0 < 1 - a := by dsimp [a]; linarith
  have heta_sq : eta ^ 2 ≤ b ^ 2 := by nlinarith
  let K : ℝ := p_n ^ 2 * denCond * displayCond / (1 - a)
  refine ⟨K, ?_, ?_⟩
  · dsimp [K]
    exact div_nonneg
      (mul_nonneg (mul_nonneg (sq_nonneg p_n) hdenCond) hdisplay)
      (le_of_lt hden)
  · have hmain : eta / (1 - eta * denCond) * displayCond ≤
        p_n * u * displayCond + K * u ^ 2 := by
      calc
        eta / (1 - eta * denCond) * displayCond
            = eta * displayCond +
                (eta ^ 2 * denCond * displayCond) / (1 - a) := by
                  have hden' : 1 - eta * denCond ≠ 0 := by
                    dsimp [a] at hden
                    linarith
                  dsimp [a]
                  field_simp [hden']
                  ring
        _ ≤ b * displayCond +
              (b ^ 2 * denCond * displayCond) / (1 - a) := by
                apply add_le_add
                · exact mul_le_mul_of_nonneg_right heta_b hdisplay
                · exact div_le_div_of_nonneg_right
                    (mul_le_mul_of_nonneg_right
                      (mul_le_mul_of_nonneg_right heta_sq hdenCond) hdisplay)
                    (le_of_lt hden)
        _ = p_n * u * displayCond + K * u ^ 2 := by
              dsimp [b, K]
              field_simp [ne_of_gt hden]
    exact hvalue.trans hmain

/-- Literal Chapter 9 `(9.23)` handoff: when the denominator and displayed
conditions coincide, the Chapter 11 expansion is exactly the existing
`higham9_23_firstOrderLe_of_backward_error_coeff`, at the same matrix dimension
and with `condU = p_n / (3n)`. -/
theorem higham11_7_firstOrderLe_from_higham9_23
    {n : ℕ} (hn : 0 < n) {u eta p_n cond value : ℝ}
    (hu : 0 ≤ u) (heta : 0 ≤ eta) (hp : 0 ≤ p_n) (hcond : 0 ≤ cond)
    (heta_le : eta ≤ p_n * u) (hsmall : eta * cond < 1)
    (hvalue : value ≤ eta / (1 - eta * cond) * cond) :
    FirstOrderLe u (p_n * u * cond) value := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hden : (3 : ℝ) * n ≠ 0 := mul_ne_zero (by norm_num) (ne_of_gt hnR)
  have hcondU : 0 ≤ p_n / ((3 : ℝ) * n) :=
    div_nonneg hp (mul_nonneg (by norm_num) (le_of_lt hnR))
  have hscale :
      (3 : ℝ) * n * u * (p_n / ((3 : ℝ) * n)) = p_n * u := by
    field_simp [hden]
  have hcoeff : eta ≤ 3 * (n : ℝ) * u * (p_n / ((3 : ℝ) * n)) := by
    rw [hscale]
    exact heta_le
  have h := higham9_23_firstOrderLe_of_backward_error_coeff
    (n := n) hu heta hcond hcondU hcoeff hsmall hvalue
  convert h using 1
  field_simp [hden]

/-- The first line of (11.7), with its `O(u^2)` term made explicit by
`FirstOrderLe`.  All hypotheses are factorization/solve backward-error data,
inverse and exact-system certificates, and the standard smallness condition.
-/
theorem higham11_7_forwardError_firstOrder_from_backward_errors {n : ℕ}
    (hn : 0 < n) (A A_inv : Fin n → Fin n → ℝ)
    (sigma : Fin n ≃ Fin n) (L_hat D_hat : Fin n → Fin n → ℝ)
    (x x_hat b : Fin n → ℝ)
    (DeltaSolve DeltaFactor : Fin n → Fin n → ℝ) (eta p_n u : ℝ)
    (hu : 0 ≤ u) (heta : 0 ≤ eta) (hp : 0 ≤ p_n)
    (heta_le : eta ≤ p_n * u)
    (hSolve : ∀ i j : Fin n, |DeltaSolve i j| ≤ eta * |A i j|)
    (hFactor : ∀ i j : Fin n, |DeltaFactor i j| ≤
      eta * higham11_7_permutedAbsLDLT sigma L_hat D_hat i j)
    (hInv : IsLeftInverse n A A_inv)
    (hAx : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hPerturbed : ∀ i : Fin n,
      ∑ j : Fin n, (A i j + (DeltaSolve i j + DeltaFactor i j)) * x_hat j = b i)
    (hsmall : eta * higham11_7_totalGlobalCondition
      hn A A_inv sigma L_hat D_hat < 1)
    (hx : 0 < infNormVec x) :
    FirstOrderLe u
      (p_n * u *
        (ch7SkeelCondAtSolutionInf n hn A A_inv x +
          higham11_7_factorCondition hn A_inv sigma L_hat D_hat))
      (infNormVec (fun i => x i - x_hat i) / infNormVec x) := by
  have hsolution_nonneg :
      0 ≤ ch7SkeelCondAtSolutionInf n hn A A_inv x := by
    unfold ch7SkeelCondAtSolutionInf ch7CondEFAtSolutionInf
    exact div_nonneg
      (ch7ForwardBoundEF_nonneg n hn A_inv (fun i j => |A i j|)
        (fun _ => 0) x (fun _ _ => abs_nonneg _) (fun _ => le_rfl))
      (le_of_lt hx)
  exact higham11_7_firstOrderLe_of_denominator hu heta hp
    (higham11_7_totalGlobalCondition_nonneg hn A A_inv sigma L_hat D_hat)
    (add_nonneg hsolution_nonneg
      (higham11_7_factorCondition_nonneg hn A_inv sigma L_hat D_hat))
    heta_le hsmall
    (higham11_7_forwardError_exact_from_backward_errors hn A A_inv sigma
      L_hat D_hat x x_hat b DeltaSolve DeltaFactor eta heta hSolve hFactor
      hInv hAx hPerturbed hsmall hx)

/-! ## The condition-product second line of (11.7) -/

theorem higham11_7_envelopeCondition_row_le {n : ℕ} (hn : 0 < n)
    (A_inv H : Fin n → Fin n → ℝ) (i : Fin n) :
    (∑ j : Fin n, |A_inv i j| * (∑ k : Fin n, H j k)) ≤
      higham11_7_envelopeCondition hn A_inv H := by
  unfold higham11_7_envelopeCondition
  exact Finset.le_sup'
    (fun i : Fin n => ∑ j : Fin n, |A_inv i j| * (∑ k : Fin n, H j k))
    (Finset.mem_univ i)

theorem higham11_7_envelopeCondition_nonneg {n : ℕ} (hn : 0 < n)
    (A_inv H : Fin n → Fin n → ℝ) (hH : ∀ i j, 0 ≤ H i j) :
    0 ≤ higham11_7_envelopeCondition hn A_inv H := by
  let i0 : Fin n := ⟨0, hn⟩
  have hrow : 0 ≤ ∑ j : Fin n, |A_inv i0 j| * (∑ k : Fin n, H j k) := by
    exact Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _)
      (Finset.sum_nonneg fun k _ => hH j k)
  exact hrow.trans (higham11_7_envelopeCondition_row_le hn A_inv H i0)

theorem higham11_7_matMul_nonneg {n : ℕ} (X Y : Fin n → Fin n → ℝ)
    (hX : ∀ i j, 0 ≤ X i j) (hY : ∀ i j, 0 ≤ Y i j) :
    ∀ i j, 0 ≤ matMul n X Y i j := by
  intro i j
  unfold matMul
  exact Finset.sum_nonneg fun k _ => mul_nonneg (hX i k) (hY k j)

theorem higham11_7_matMul_mono_left_factor {n : ℕ}
    (X Y Z : Fin n → Fin n → ℝ)
    (hXY : ∀ i j, X i j ≤ Y i j) (hZ : ∀ i j, 0 ≤ Z i j) :
    ∀ i j, matMul n X Z i j ≤ matMul n Y Z i j := by
  intro i j
  unfold matMul
  apply Finset.sum_le_sum
  intro k _
  exact mul_le_mul_of_nonneg_right (hXY i k) (hZ k j)

theorem higham11_7_matMul_mono_right_factor {n : ℕ}
    (X Y Z : Fin n → Fin n → ℝ)
    (hX : ∀ i j, 0 ≤ X i j) (hYZ : ∀ i j, Y i j ≤ Z i j) :
    ∀ i j, matMul n X Y i j ≤ matMul n X Z i j := by
  intro i j
  unfold matMul
  apply Finset.sum_le_sum
  intro k _
  exact mul_le_mul_of_nonneg_left (hYZ k j) (hX i k)

theorem higham11_7_abs_matMul_le {n : ℕ}
    (X Y : Fin n → Fin n → ℝ) (i j : Fin n) :
    |matMul n X Y i j| ≤ matMul n (absMatrix n X) (absMatrix n Y) i j := by
  unfold matMul absMatrix
  calc
    |∑ k : Fin n, X i k * Y k j| ≤
        ∑ k : Fin n, |X i k * Y k j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin n, |X i k| * |Y k j| := by
      apply Finset.sum_congr rfl
      intro k _
      exact abs_mul _ _

/-- In original coordinates, the left factor in
`A = (Pᵀ L_hat P) (Pᵀ D_hat L_hatᵀ P)`. -/
noncomputable def higham11_7_permutedLeftFactor {n : ℕ}
    (sigma : Fin n ≃ Fin n) (L_hat : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => L_hat (sigma.symm i) (sigma.symm j)

/-- In original coordinates, the right factor `Pᵀ D_hat L_hatᵀ P`. -/
noncomputable def higham11_7_permutedRightFactor {n : ℕ}
    (sigma : Fin n ≃ Fin n) (L_hat D_hat : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => ∑ q : Fin n, D_hat (sigma.symm i) q * L_hat (sigma.symm j) q

/-- The componentwise solve envelope `Pᵀ |D_hat| |L_hatᵀ| P` for the right
factor in the Chapter 11 product split. -/
noncomputable def higham11_7_permutedRightEnvelope {n : ℕ}
    (sigma : Fin n ≃ Fin n) (L_hat D_hat : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => ∑ q : Fin n, |D_hat (sigma.symm i) q| * |L_hat (sigma.symm j) q|

theorem higham11_7_permutedRightFactor_abs_le_envelope {n : ℕ}
    (sigma : Fin n ≃ Fin n) (L_hat D_hat : Fin n → Fin n → ℝ)
    (i j : Fin n) :
    |higham11_7_permutedRightFactor sigma L_hat D_hat i j| ≤
      higham11_7_permutedRightEnvelope sigma L_hat D_hat i j := by
  unfold higham11_7_permutedRightFactor higham11_7_permutedRightEnvelope
  calc
    |∑ q : Fin n, D_hat (sigma.symm i) q * L_hat (sigma.symm j) q| ≤
        ∑ q : Fin n, |D_hat (sigma.symm i) q * L_hat (sigma.symm j) q| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ q : Fin n, |D_hat (sigma.symm i) q| *
        |L_hat (sigma.symm j) q| := by
      apply Finset.sum_congr rfl
      intro q _
      exact abs_mul _ _

/-- Multiplying the literal permuted left factor by the literal right-factor
envelope gives exactly the matrix `Pᵀ|L_hat||D_hat||L_hatᵀ|P` used on the first
line of (11.7). -/
theorem higham11_7_permutedLeft_mul_rightEnvelope_eq_permutedAbsLDLT {n : ℕ}
    (sigma : Fin n ≃ Fin n) (L_hat D_hat : Fin n → Fin n → ℝ) :
    matMul n (absMatrix n (higham11_7_permutedLeftFactor sigma L_hat))
        (higham11_7_permutedRightEnvelope sigma L_hat D_hat) =
      higham11_7_permutedAbsLDLT sigma L_hat D_hat := by
  ext i j
  unfold matMul absMatrix higham11_7_permutedLeftFactor
    higham11_7_permutedRightEnvelope higham11_7_permutedAbsLDLT
  let f : Fin n → ℝ := fun p =>
    |L_hat (sigma.symm i) p| *
      (∑ q : Fin n, |D_hat p q| * |L_hat (sigma.symm j) q|)
  calc
    (∑ k : Fin n, |L_hat (sigma.symm i) (sigma.symm k)| *
        (∑ q : Fin n, |D_hat (sigma.symm k) q| * |L_hat (sigma.symm j) q|))
        = ∑ p : Fin n, f p := by
          simpa [f] using (Equiv.sum_comp sigma.symm f)
    _ = ∑ p : Fin n, ∑ q : Fin n,
        |L_hat (sigma.symm i) p| * |D_hat p q| *
          |L_hat (sigma.symm j) q| := by
      apply Finset.sum_congr rfl
      intro p _
      dsimp [f]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring

/-- A source `BlockLDLTSpec` identifies the literal Chapter 11 factors above
with an exact product `A = (PᵀLP)(PᵀDLᵀP)`. -/
theorem higham11_7_permutedLeft_mul_rightFactor_eq_of_BlockLDLTSpec {n : ℕ}
    (A L_hat D_hat : Fin n → Fin n → ℝ) (sigma : Fin n ≃ Fin n)
    (hspec : higham11_1_BlockLDLTSpec n A L_hat D_hat sigma) :
    matMul n (higham11_7_permutedLeftFactor sigma L_hat)
        (higham11_7_permutedRightFactor sigma L_hat D_hat) = A := by
  ext i j
  unfold matMul higham11_7_permutedLeftFactor higham11_7_permutedRightFactor
  let f : Fin n → ℝ := fun p =>
    L_hat (sigma.symm i) p *
      (∑ q : Fin n, D_hat p q * L_hat (sigma.symm j) q)
  calc
    (∑ k : Fin n, L_hat (sigma.symm i) (sigma.symm k) *
        (∑ q : Fin n, D_hat (sigma.symm k) q * L_hat (sigma.symm j) q))
        = ∑ p : Fin n, f p := by
          simpa [f] using (Equiv.sum_comp sigma.symm f)
    _ = ∑ p : Fin n, ∑ q : Fin n,
        L_hat (sigma.symm i) p * D_hat p q * L_hat (sigma.symm j) q := by
      apply Finset.sum_congr rfl
      intro p _
      dsimp [f]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ = A i j := by
      simpa using hspec.product_eq (sigma.symm i) (sigma.symm j)

theorem higham11_7_infNorm_mono_of_nonneg {n : ℕ}
    (X Y : Fin n → Fin n → ℝ)
    (hX : ∀ i j, 0 ≤ X i j) (hY : ∀ i j, 0 ≤ Y i j)
    (hXY : ∀ i j, X i j ≤ Y i j) :
    infNorm X ≤ infNorm Y := by
  apply infNorm_le_of_row_sum_le X
  · intro i
    calc
      (∑ j : Fin n, |X i j|) = ∑ j : Fin n, X i j := by
        apply Finset.sum_congr rfl
        intro j _
        exact abs_of_nonneg (hX i j)
      _ ≤ ∑ j : Fin n, Y i j := by
        exact Finset.sum_le_sum fun j _ => hXY i j
      _ = ∑ j : Fin n, |Y i j| := by
        apply Finset.sum_congr rfl
        intro j _
        exact (abs_of_nonneg (hY i j)).symm
      _ ≤ infNorm Y := row_sum_le_infNorm Y i
  · exact infNorm_nonneg Y

/-- The row-sum definition used in (11.7) is exactly the repository infinity
norm of `|A⁻¹|H` whenever `H` is nonnegative. -/
theorem higham11_7_envelopeCondition_eq_infNorm_abs_product {n : ℕ}
    (hn : 0 < n) (A_inv H : Fin n → Fin n → ℝ)
    (hH : ∀ i j, 0 ≤ H i j) :
    higham11_7_envelopeCondition hn A_inv H =
      infNorm (matMul n (absMatrix n A_inv) H) := by
  let G := matMul n (absMatrix n A_inv) H
  have hG : ∀ i j, 0 ≤ G i j :=
    higham11_7_matMul_nonneg (absMatrix n A_inv) H
      (fun i j => abs_nonneg _) hH
  have hrow : ∀ i : Fin n,
      (∑ k : Fin n, |G i k|) =
        ∑ j : Fin n, |A_inv i j| * (∑ k : Fin n, H j k) := by
    intro i
    calc
      (∑ k : Fin n, |G i k|) = ∑ k : Fin n, G i k := by
        apply Finset.sum_congr rfl
        intro k _
        exact abs_of_nonneg (hG i k)
      _ = ∑ k : Fin n, ∑ j : Fin n, |A_inv i j| * H j k := by
        rfl
      _ = ∑ j : Fin n, ∑ k : Fin n, |A_inv i j| * H j k :=
        Finset.sum_comm
      _ = ∑ j : Fin n, |A_inv i j| * (∑ k : Fin n, H j k) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
  apply le_antisymm
  · unfold higham11_7_envelopeCondition
    apply Finset.sup'_le
    intro i _
    rw [← hrow i]
    exact row_sum_le_infNorm G i
  · apply infNorm_le_of_row_sum_le G
    · intro i
      rw [hrow i]
      exact higham11_7_envelopeCondition_row_le hn A_inv H i
    · exact higham11_7_envelopeCondition_nonneg hn A_inv H hH

/-- The direct row-sum definition specializes definitionally to Chapter 9's
global Skeel condition when `H = |A|`. -/
theorem higham11_7_envelopeCondition_absMatrix_eq_condSkeel {n : ℕ}
    (hn : 0 < n) (A A_inv : Fin n → Fin n → ℝ) :
    higham11_7_envelopeCondition hn A_inv (absMatrix n A) =
      condSkeel n hn A A_inv := by
  rfl

/-- Product-conditioning lemma behind the second line of (11.7).

For `A = B C`, write the componentwise factorization envelope as
`|B| Cenv`, where `Cenv` bounds `|C|`.  Since `B = A C⁻¹`, monotonicity of
nonnegative matrix products and infinity-norm submultiplicativity give

`‖|A⁻¹||B|Cenv‖∞ ≤ cond(A) ‖|C⁻¹|Cenv‖∞`.

The hypotheses are exact product/inverse/envelope data, not the desired norm
inequality.
-/
theorem higham11_7_product_envelopeCondition_le {n : ℕ} (hn : 0 < n)
    (A A_inv B C C_inv Cenv : Fin n → Fin n → ℝ)
    (hprod : matMul n B C = A)
    (hCright : IsRightInverse n C C_inv)
    (hCenv : ∀ i j, 0 ≤ Cenv i j) :
    higham11_7_envelopeCondition hn A_inv
        (matMul n (absMatrix n B) Cenv) ≤
      condSkeel n hn A A_inv *
        higham11_7_envelopeCondition hn C_inv Cenv := by
  have hCCinv : matMul n C C_inv = idMatrix n := by
    ext i j
    exact hCright i j
  have hB_eq : B = matMul n A C_inv := by
    calc
      B = matMul n B (idMatrix n) := (matMul_id_right n B).symm
      _ = matMul n B (matMul n C C_inv) := by rw [hCCinv]
      _ = matMul n (matMul n B C) C_inv := (matMul_assoc n B C C_inv).symm
      _ = matMul n A C_inv := by rw [hprod]
  have hBabs : ∀ i j,
      absMatrix n B i j ≤
        matMul n (absMatrix n A) (absMatrix n C_inv) i j := by
    intro i j
    rw [hB_eq]
    exact higham11_7_abs_matMul_le A C_inv i j
  let XA := absMatrix n A_inv
  let YA := absMatrix n A
  let Z := absMatrix n C_inv
  let Hsmall := matMul n (absMatrix n B) Cenv
  let Hlarge := matMul n (matMul n YA Z) Cenv
  let Tsmall := matMul n XA Hsmall
  let Tlarge := matMul n XA Hlarge
  have hXA : ∀ i j, 0 ≤ XA i j := fun _ _ => abs_nonneg _
  have hYA : ∀ i j, 0 ≤ YA i j := fun _ _ => abs_nonneg _
  have hZ : ∀ i j, 0 ≤ Z i j := fun _ _ => abs_nonneg _
  have hBnonneg : ∀ i j, 0 ≤ absMatrix n B i j := fun _ _ => abs_nonneg _
  have hYZ : ∀ i j, 0 ≤ matMul n YA Z i j :=
    higham11_7_matMul_nonneg YA Z hYA hZ
  have hHsmall : ∀ i j, 0 ≤ Hsmall i j :=
    higham11_7_matMul_nonneg (absMatrix n B) Cenv hBnonneg hCenv
  have hHlarge : ∀ i j, 0 ≤ Hlarge i j :=
    higham11_7_matMul_nonneg (matMul n YA Z) Cenv hYZ hCenv
  have hH : ∀ i j, Hsmall i j ≤ Hlarge i j := by
    exact higham11_7_matMul_mono_left_factor
      (absMatrix n B) (matMul n YA Z) Cenv (by simpa [YA, Z] using hBabs) hCenv
  have hTsmall : ∀ i j, 0 ≤ Tsmall i j :=
    higham11_7_matMul_nonneg XA Hsmall hXA hHsmall
  have hTlarge : ∀ i j, 0 ≤ Tlarge i j :=
    higham11_7_matMul_nonneg XA Hlarge hXA hHlarge
  have hT : ∀ i j, Tsmall i j ≤ Tlarge i j :=
    higham11_7_matMul_mono_right_factor XA Hsmall Hlarge hXA hH
  calc
    higham11_7_envelopeCondition hn A_inv
        (matMul n (absMatrix n B) Cenv)
        = infNorm Tsmall := by
            simpa [Tsmall, Hsmall, XA] using
              higham11_7_envelopeCondition_eq_infNorm_abs_product
                hn A_inv (matMul n (absMatrix n B) Cenv) hHsmall
    _ ≤ infNorm Tlarge :=
      higham11_7_infNorm_mono_of_nonneg Tsmall Tlarge hTsmall hTlarge hT
    _ = infNorm (matMul n (matMul n XA YA) (matMul n Z Cenv)) := by
      congr 1
      dsimp [Tlarge, Hlarge]
      rw [← matMul_assoc n XA (matMul n YA Z) Cenv,
        ← matMul_assoc n XA YA Z,
        matMul_assoc n (matMul n XA YA) Z Cenv]
    _ ≤ infNorm (matMul n XA YA) * infNorm (matMul n Z Cenv) :=
      infNorm_matMul_le hn (matMul n XA YA) (matMul n Z Cenv)
    _ = condSkeel n hn A A_inv *
        higham11_7_envelopeCondition hn C_inv Cenv := by
      dsimp [XA, YA, Z]
      rw [← higham11_7_envelopeCondition_absMatrix_eq_condSkeel hn A A_inv,
        higham11_7_envelopeCondition_eq_infNorm_abs_product hn A_inv
          (absMatrix n A) (fun _ _ => abs_nonneg _),
        higham11_7_envelopeCondition_eq_infNorm_abs_product hn C_inv Cenv hCenv]

/-- Any componentwise solve envelope `Cenv ≥ |C|` has condition at least one
when `C_inv` is a right inverse of the square matrix `C`. -/
theorem higham11_7_one_le_envelopeCondition_of_inverse {n : ℕ} (hn : 0 < n)
    (C C_inv Cenv : Fin n → Fin n → ℝ)
    (hCright : IsRightInverse n C C_inv)
    (hCenv : ∀ i j, |C i j| ≤ Cenv i j) :
    1 ≤ higham11_7_envelopeCondition hn C_inv Cenv := by
  let i0 : Fin n := ⟨0, hn⟩
  have hCleft : IsLeftInverse n C C_inv :=
    isLeftInverse_of_isRightInverse C C_inv hCright
  have hrow :
      1 ≤ ∑ j : Fin n, |C_inv i0 j| * (∑ k : Fin n, Cenv j k) := by
    calc
      1 = |∑ j : Fin n, C_inv i0 j * C j i0| := by
        rw [hCleft i0 i0]
        simp
      _ ≤ ∑ j : Fin n, |C_inv i0 j * C j i0| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin n, |C_inv i0 j| * |C j i0| := by
        apply Finset.sum_congr rfl
        intro j _
        exact abs_mul _ _
      _ ≤ ∑ j : Fin n, |C_inv i0 j| * Cenv j i0 := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hCenv j i0) (abs_nonneg _)
      _ ≤ ∑ j : Fin n, |C_inv i0 j| * (∑ k : Fin n, Cenv j k) := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact Finset.single_le_sum
          (fun k _ => (abs_nonneg (C j k)).trans (hCenv j k))
          (Finset.mem_univ i0)
  exact hrow.trans (higham11_7_envelopeCondition_row_le hn C_inv Cenv i0)

/-- The condition-number comparison printed on the second line of (11.7).
The fixed factor two is absorbed by Higham's unspecified polynomial `p(n)`.
-/
theorem higham11_7_condition_sum_le_two_mul_product {n : ℕ} (hn : 0 < n)
    (A A_inv B C C_inv Cenv : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hx : 0 < infNormVec x)
    (hprod : matMul n B C = A)
    (hCright : IsRightInverse n C C_inv)
    (hCenv : ∀ i j, |C i j| ≤ Cenv i j) :
    ch7SkeelCondAtSolutionInf n hn A A_inv x +
        higham11_7_envelopeCondition hn A_inv
          (matMul n (absMatrix n B) Cenv) ≤
      2 * condSkeel n hn A A_inv *
        higham11_7_envelopeCondition hn C_inv Cenv := by
  have hCenv_nonneg : ∀ i j, 0 ≤ Cenv i j := fun i j =>
    (abs_nonneg (C i j)).trans (hCenv i j)
  have hsolution := ch7SkeelCondAtSolutionInf_le_condSkeel n hn A A_inv x hx
  have hfactor := higham11_7_product_envelopeCondition_le hn
    A A_inv B C C_inv Cenv hprod hCright hCenv_nonneg
  have hcondC := higham11_7_one_le_envelopeCondition_of_inverse
    hn C C_inv Cenv hCright hCenv
  have hcondA : 0 ≤ condSkeel n hn A A_inv :=
    higham9_23_condSkeel_nonneg n hn A A_inv
  have hA_le_product : condSkeel n hn A A_inv ≤
      condSkeel n hn A A_inv * higham11_7_envelopeCondition hn C_inv Cenv := by
    calc
      condSkeel n hn A A_inv = condSkeel n hn A A_inv * 1 := by ring
      _ ≤ condSkeel n hn A A_inv *
          higham11_7_envelopeCondition hn C_inv Cenv :=
        mul_le_mul_of_nonneg_left hcondC hcondA
  calc
    ch7SkeelCondAtSolutionInf n hn A A_inv x +
        higham11_7_envelopeCondition hn A_inv
          (matMul n (absMatrix n B) Cenv)
        ≤ condSkeel n hn A A_inv +
          condSkeel n hn A A_inv *
            higham11_7_envelopeCondition hn C_inv Cenv :=
          add_le_add hsolution hfactor
    _ ≤ 2 * condSkeel n hn A A_inv *
        higham11_7_envelopeCondition hn C_inv Cenv := by
      nlinarith

/-- `FirstOrderLe` form of the second line of (11.7).  It consumes the first
line together with the exact product/inverse/envelope certificates above and
widens the unspecified polynomial coefficient by the fixed factor two. -/
theorem higham11_7_forwardError_firstOrder_condition_product {n : ℕ}
    (hn : 0 < n) (A A_inv B C C_inv Cenv : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) (u p_n relativeError : ℝ)
    (hu : 0 ≤ u) (hp : 0 ≤ p_n) (hx : 0 < infNormVec x)
    (hprod : matMul n B C = A)
    (hCright : IsRightInverse n C C_inv)
    (hCenv : ∀ i j, |C i j| ≤ Cenv i j)
    (hfirst : FirstOrderLe u
      (p_n * u *
        (ch7SkeelCondAtSolutionInf n hn A A_inv x +
          higham11_7_envelopeCondition hn A_inv
            (matMul n (absMatrix n B) Cenv))) relativeError) :
    FirstOrderLe u
      ((2 * p_n) * u * condSkeel n hn A A_inv *
        higham11_7_envelopeCondition hn C_inv Cenv) relativeError := by
  apply hfirst.mono_leading
  have hcond := higham11_7_condition_sum_le_two_mul_product hn
    A A_inv B C C_inv Cenv x hx hprod hCright hCenv
  have hpu : 0 ≤ p_n * u := mul_nonneg hp hu
  calc
    p_n * u *
        (ch7SkeelCondAtSolutionInf n hn A A_inv x +
          higham11_7_envelopeCondition hn A_inv
            (matMul n (absMatrix n B) Cenv))
        ≤ p_n * u *
          (2 * condSkeel n hn A A_inv *
            higham11_7_envelopeCondition hn C_inv Cenv) :=
          mul_le_mul_of_nonneg_left hcond hpu
    _ = (2 * p_n) * u * condSkeel n hn A A_inv *
        higham11_7_envelopeCondition hn C_inv Cenv := by ring

/-- Complete public endpoint for both displayed lines of equation (11.7).

This theorem first derives the source's

`p(n)u (cond(A,x) + ‖|A⁻¹|Pᵀ|L_hat||D_hat||L_hatᵀ|P‖∞) + O(u²)`

directly from the solve and factorization backward errors.  It then uses the
literal split

`A = (PᵀL_hat P) (PᵀD_hat L_hatᵀP)`

provided by `BlockLDLTSpec` to obtain the condition-product second line.  The
fixed factor two is absorbed into Higham's unspecified polynomial `p(n)`.
-/
theorem higham11_7_forwardError_firstOrder_condition_product_from_backward_errors
    {n : ℕ} (hn : 0 < n)
    (A A_inv L_hat D_hat : Fin n → Fin n → ℝ) (sigma : Fin n ≃ Fin n)
    (C_inv : Fin n → Fin n → ℝ) (x x_hat b : Fin n → ℝ)
    (DeltaSolve DeltaFactor : Fin n → Fin n → ℝ) (eta p_n u : ℝ)
    (hu : 0 ≤ u) (heta : 0 ≤ eta) (hp : 0 ≤ p_n)
    (heta_le : eta ≤ p_n * u)
    (hspec : higham11_1_BlockLDLTSpec n A L_hat D_hat sigma)
    (hCright : IsRightInverse n
      (higham11_7_permutedRightFactor sigma L_hat D_hat) C_inv)
    (hSolve : ∀ i j : Fin n, |DeltaSolve i j| ≤ eta * |A i j|)
    (hFactor : ∀ i j : Fin n, |DeltaFactor i j| ≤
      eta * higham11_7_permutedAbsLDLT sigma L_hat D_hat i j)
    (hInv : IsLeftInverse n A A_inv)
    (hAx : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hPerturbed : ∀ i : Fin n,
      ∑ j : Fin n, (A i j + (DeltaSolve i j + DeltaFactor i j)) * x_hat j = b i)
    (hsmall : eta * higham11_7_totalGlobalCondition
      hn A A_inv sigma L_hat D_hat < 1)
    (hx : 0 < infNormVec x) :
    FirstOrderLe u
      ((2 * p_n) * u * condSkeel n hn A A_inv *
        higham11_7_envelopeCondition hn C_inv
          (higham11_7_permutedRightEnvelope sigma L_hat D_hat))
      (infNormVec (fun i => x i - x_hat i) / infNormVec x) := by
  have hfirst := higham11_7_forwardError_firstOrder_from_backward_errors
    hn A A_inv sigma L_hat D_hat x x_hat b DeltaSolve DeltaFactor eta p_n u
    hu heta hp heta_le hSolve hFactor hInv hAx hPerturbed hsmall hx
  have hfactorEq :
      higham11_7_factorCondition hn A_inv sigma L_hat D_hat =
        higham11_7_envelopeCondition hn A_inv
          (matMul n
            (absMatrix n (higham11_7_permutedLeftFactor sigma L_hat))
            (higham11_7_permutedRightEnvelope sigma L_hat D_hat)) := by
    unfold higham11_7_factorCondition
    rw [higham11_7_permutedLeft_mul_rightEnvelope_eq_permutedAbsLDLT]
  rw [hfactorEq] at hfirst
  exact higham11_7_forwardError_firstOrder_condition_product
    hn A A_inv
    (higham11_7_permutedLeftFactor sigma L_hat)
    (higham11_7_permutedRightFactor sigma L_hat D_hat)
    C_inv (higham11_7_permutedRightEnvelope sigma L_hat D_hat)
    x u p_n (infNormVec (fun i => x i - x_hat i) / infNormVec x)
    hu hp hx
    (higham11_7_permutedLeft_mul_rightFactor_eq_of_BlockLDLTSpec
      A L_hat D_hat sigma hspec)
    hCright
    (higham11_7_permutedRightFactor_abs_le_envelope sigma L_hat D_hat)
    hfirst

/-! ## Uniform family form of (11.7)

The preceding `FirstOrderLe` statements retain a useful fixed-precision
algebraic decomposition, but a source `O(u^2)` assertion requires one
quadratic constant for a complete family as `u -> 0`.  The results below give
that uniform surface and, crucially, let the computed factors factor
`A + DeltaFactor` rather than requiring the first-stage backward error to
vanish.
-/

/-- Uniform denominator expansion.  The bounds `Mmax` and `Dmax` are ordinary
local boundedness certificates for the denominator and displayed condition;
the half-radius hypothesis is the explicit neighbourhood on which the
Neumann denominator is uniformly separated from zero. -/
theorem higham11_7_familyFirstOrderLe_of_denominator
    {ι : Type*} {l : Filter ι} (U : RoundoffFamily ι l)
    (p_n Mmax Dmax : ℝ) (hp : 0 ≤ p_n) (hMmax : 0 ≤ Mmax)
    (hDmax : 0 ≤ Dmax)
    (eta denCond displayCond value : ι → ℝ)
    (heta : ∀ t, 0 ≤ eta t) (hden : ∀ t, 0 ≤ denCond t)
    (hdisplay : ∀ t, 0 ≤ displayCond t)
    (heta_le : ∀ t, eta t ≤ p_n * U.unit t)
    (hhalf : ∀ t, eta t * denCond t ≤ (1 : ℝ) / 2)
    (hden_bound : ∀ t, denCond t ≤ Mmax)
    (hdisplay_bound : ∀ t, displayCond t ≤ Dmax)
    (hvalue : ∀ t, value t ≤
      eta t / (1 - eta t * denCond t) * displayCond t) :
    FamilyFirstOrderLe l U.unit
      (fun t => p_n * U.unit t * displayCond t) value := by
  let K : ℝ := 2 * p_n ^ 2 * Mmax * Dmax
  apply FamilyFirstOrderLe.of_uniform_quadratic (K := K)
  · dsimp [K]
    positivity
  · intro t
    let a : ℝ := eta t * denCond t
    let base : ℝ := (p_n * U.unit t) ^ 2 * Mmax * Dmax
    have hpu : 0 ≤ p_n * U.unit t := mul_nonneg hp (U.unit_nonneg t)
    have heta_sq : eta t ^ 2 ≤ (p_n * U.unit t) ^ 2 := by
      nlinarith [heta t, heta_le t]
    have ha_nonneg : 0 ≤ a := by
      exact mul_nonneg (heta t) (hden t)
    have hden_half : (1 : ℝ) / 2 ≤ 1 - a := by
      dsimp [a]
      linarith [hhalf t]
    have hden_pos : 0 < 1 - a := lt_of_lt_of_le (by norm_num) hden_half
    have hnum : eta t ^ 2 * denCond t * displayCond t ≤ base := by
      calc
        eta t ^ 2 * denCond t * displayCond t
            ≤ (p_n * U.unit t) ^ 2 * denCond t * displayCond t := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right heta_sq (hden t)) (hdisplay t)
        _ ≤ (p_n * U.unit t) ^ 2 * Mmax * displayCond t := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (hden_bound t) (sq_nonneg _))
                (hdisplay t)
        _ ≤ (p_n * U.unit t) ^ 2 * Mmax * Dmax := by
              exact mul_le_mul_of_nonneg_left (hdisplay_bound t)
                (mul_nonneg (sq_nonneg _) hMmax)
        _ = base := rfl
    have hbase_nonneg : 0 ≤ base := by
      dsimp [base]
      positivity
    have hbase_div : base / (1 - a) ≤ 2 * base := by
      apply (div_le_iff₀ hden_pos).2
      have hmul : 0 ≤ base * ((1 - a) - (1 : ℝ) / 2) :=
        mul_nonneg hbase_nonneg (sub_nonneg.mpr hden_half)
      nlinarith
    have hremainder :
        (eta t ^ 2 * denCond t * displayCond t) / (1 - a) ≤
          K * U.unit t ^ 2 := by
      calc
        (eta t ^ 2 * denCond t * displayCond t) / (1 - a)
            ≤ base / (1 - a) :=
              div_le_div_of_nonneg_right hnum (le_of_lt hden_pos)
        _ ≤ 2 * base := hbase_div
        _ = K * U.unit t ^ 2 := by
              dsimp [base, K]
              ring
    have hidentity :
        eta t / (1 - eta t * denCond t) * displayCond t =
          eta t * displayCond t +
            (eta t ^ 2 * denCond t * displayCond t) / (1 - a) := by
      have hne : 1 - eta t * denCond t ≠ 0 := by
        simpa [a] using ne_of_gt hden_pos
      dsimp [a]
      field_simp [hne]
      ring
    calc
      value t ≤ eta t / (1 - eta t * denCond t) * displayCond t := hvalue t
      _ = eta t * displayCond t +
          (eta t ^ 2 * denCond t * displayCond t) / (1 - a) := hidentity
      _ ≤ p_n * U.unit t * displayCond t + K * U.unit t ^ 2 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right (heta_le t) (hdisplay t)) hremainder

/-- Adding a componentwise perturbation bounded by `eta * H` changes the
Skeel row envelope by at most `eta * envelopeCondition(A_inv,H)`. -/
theorem higham11_7_condSkeel_add_perturbation_le {n : ℕ} (hn : 0 < n)
    (A A_inv Delta H : Fin n → Fin n → ℝ) (eta : ℝ)
    (heta : 0 ≤ eta) (hDelta : ∀ i j, |Delta i j| ≤ eta * H i j) :
    condSkeel n hn (fun i j => A i j + Delta i j) A_inv ≤
      condSkeel n hn A A_inv +
        eta * higham11_7_envelopeCondition hn A_inv H := by
  unfold condSkeel
  apply Finset.sup'_le
  intro i _
  have hArow :
      (∑ j : Fin n, |A_inv i j| * (∑ k : Fin n, |A j k|)) ≤
        Finset.sup' Finset.univ
          (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
          (fun r => ∑ j : Fin n, |A_inv r j| * (∑ k : Fin n, |A j k|)) :=
    Finset.le_sup'
      (fun r : Fin n =>
        ∑ j : Fin n, |A_inv r j| * (∑ k : Fin n, |A j k|))
      (Finset.mem_univ i)
  have hHrow :
      (∑ j : Fin n, |A_inv i j| * (∑ k : Fin n, H j k)) ≤
        higham11_7_envelopeCondition hn A_inv H :=
    higham11_7_envelopeCondition_row_le hn A_inv H i
  calc
    (∑ j : Fin n, |A_inv i j| *
        (∑ k : Fin n, |A j k + Delta j k|))
        ≤ ∑ j : Fin n, |A_inv i j| *
            (∑ k : Fin n, (|A j k| + eta * H j k)) := by
          apply Finset.sum_le_sum
          intro j _
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          apply Finset.sum_le_sum
          intro k _
          exact (abs_add_le _ _).trans
            (add_le_add le_rfl (hDelta j k))
    _ = (∑ j : Fin n, |A_inv i j| * (∑ k : Fin n, |A j k|)) +
          eta * (∑ j : Fin n, |A_inv i j| * (∑ k : Fin n, H j k)) := by
          simp_rw [Finset.sum_add_distrib, mul_add]
          rw [Finset.sum_add_distrib, Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          rw [← Finset.mul_sum]
          ring
    _ ≤ Finset.sup' Finset.univ
          (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
          (fun r => ∑ j : Fin n, |A_inv r j| * (∑ k : Fin n, |A j k|)) +
        eta * higham11_7_envelopeCondition hn A_inv H := by
          exact add_le_add hArow (mul_le_mul_of_nonneg_left hHrow heta)

/-- Product conditioning with a genuine first-stage backward error.  The
computed product is `A + Delta`, and the extra term is linear in that same
perturbation certificate rather than being silently set to zero. -/
theorem higham11_7_perturbed_product_envelopeCondition_le {n : ℕ}
    (hn : 0 < n)
    (A A_inv B C C_inv Cenv Delta : Fin n → Fin n → ℝ) (eta : ℝ)
    (heta : 0 ≤ eta)
    (hprod : matMul n B C = fun i j => A i j + Delta i j)
    (hCright : IsRightInverse n C C_inv)
    (hCenv_nonneg : ∀ i j, 0 ≤ Cenv i j)
    (hDelta : ∀ i j, |Delta i j| ≤
      eta * matMul n (absMatrix n B) Cenv i j) :
    higham11_7_envelopeCondition hn A_inv
        (matMul n (absMatrix n B) Cenv) ≤
      condSkeel n hn A A_inv * higham11_7_envelopeCondition hn C_inv Cenv +
        eta * higham11_7_envelopeCondition hn A_inv
          (matMul n (absMatrix n B) Cenv) *
          higham11_7_envelopeCondition hn C_inv Cenv := by
  let H := matMul n (absMatrix n B) Cenv
  let F := higham11_7_envelopeCondition hn A_inv H
  let Ccond := higham11_7_envelopeCondition hn C_inv Cenv
  have hprodBound := higham11_7_product_envelopeCondition_le hn
    (fun i j => A i j + Delta i j) A_inv B C C_inv Cenv
    hprod hCright hCenv_nonneg
  have hcondAdd := higham11_7_condSkeel_add_perturbation_le hn
    A A_inv Delta H eta heta (by simpa [H] using hDelta)
  have hCcond : 0 ≤ Ccond :=
    higham11_7_envelopeCondition_nonneg hn C_inv Cenv hCenv_nonneg
  calc
    higham11_7_envelopeCondition hn A_inv
        (matMul n (absMatrix n B) Cenv)
        ≤ condSkeel n hn (fun i j => A i j + Delta i j) A_inv * Ccond := by
          simpa [H, Ccond] using hprodBound
    _ ≤ (condSkeel n hn A A_inv + eta * F) * Ccond :=
          mul_le_mul_of_nonneg_right hcondAdd hCcond
    _ = condSkeel n hn A A_inv * Ccond + eta * F * Ccond := by ring
    _ = condSkeel n hn A A_inv *
          higham11_7_envelopeCondition hn C_inv Cenv +
        eta * higham11_7_envelopeCondition hn A_inv
          (matMul n (absMatrix n B) Cenv) *
          higham11_7_envelopeCondition hn C_inv Cenv := by
          rfl

/-- Source-facing family endpoint for both lines of (11.7).

At every precision the computed factors factor `A + DeltaFactor`.  Uniform
bounds on the displayed conditions are regularity data, not a forward-error
conclusion; they make the two hidden Landau constants independent of the
family index. -/
theorem higham11_7_forwardError_family_condition_product_from_backward_errors
    {ι : Type*} {l : Filter ι} (U : RoundoffFamily ι l)
    {n : ℕ} (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (sigma : Fin n ≃ Fin n)
    (L_hat D_hat C_inv : ι → Fin n → Fin n → ℝ)
    (x b : Fin n → ℝ) (x_hat : ι → Fin n → ℝ)
    (DeltaSolve DeltaFactor : ι → Fin n → Fin n → ℝ)
    (eta : ι → ℝ) (p_n Mmax Dmax Fmax Cmax : ℝ)
    (hp : 0 ≤ p_n) (hMmax : 0 ≤ Mmax) (hDmax : 0 ≤ Dmax)
    (hFmax : 0 ≤ Fmax) (hCmax : 0 ≤ Cmax)
    (heta : ∀ t, 0 ≤ eta t)
    (heta_le : ∀ t, eta t ≤ p_n * U.unit t)
    (hspec : ∀ t, higham11_1_BlockLDLTSpec n
      (fun i j => A i j + DeltaFactor t i j) (L_hat t) (D_hat t) sigma)
    (hCright : ∀ t, IsRightInverse n
      (higham11_7_permutedRightFactor sigma (L_hat t) (D_hat t)) (C_inv t))
    (hSolve : ∀ t i j, |DeltaSolve t i j| ≤ eta t * |A i j|)
    (hFactor : ∀ t i j, |DeltaFactor t i j| ≤
      eta t * higham11_7_permutedAbsLDLT sigma (L_hat t) (D_hat t) i j)
    (hInv : IsLeftInverse n A A_inv)
    (hAx : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hPerturbed : ∀ t i, ∑ j : Fin n,
      (A i j + (DeltaSolve t i j + DeltaFactor t i j)) * x_hat t j = b i)
    (hx : 0 < infNormVec x)
    (hhalf : ∀ t, eta t * higham11_7_totalGlobalCondition
      hn A A_inv sigma (L_hat t) (D_hat t) ≤ (1 : ℝ) / 2)
    (hMbound : ∀ t, higham11_7_totalGlobalCondition
      hn A A_inv sigma (L_hat t) (D_hat t) ≤ Mmax)
    (hDbound : ∀ t,
      ch7SkeelCondAtSolutionInf n hn A A_inv x +
        higham11_7_factorCondition hn A_inv sigma (L_hat t) (D_hat t) ≤ Dmax)
    (hFbound : ∀ t,
      higham11_7_factorCondition hn A_inv sigma (L_hat t) (D_hat t) ≤ Fmax)
    (hCbound : ∀ t, higham11_7_envelopeCondition hn (C_inv t)
      (higham11_7_permutedRightEnvelope sigma (L_hat t) (D_hat t)) ≤ Cmax) :
    FamilyFirstOrderLe l U.unit
      (fun t => (2 * p_n) * U.unit t * condSkeel n hn A A_inv *
        higham11_7_envelopeCondition hn (C_inv t)
          (higham11_7_permutedRightEnvelope sigma (L_hat t) (D_hat t)))
      (fun t => infNormVec (fun i => x i - x_hat t i) / infNormVec x) := by
  let fixed := ch7SkeelCondAtSolutionInf n hn A A_inv x
  let F : ι → ℝ := fun t =>
    higham11_7_factorCondition hn A_inv sigma (L_hat t) (D_hat t)
  let Ccond : ι → ℝ := fun t => higham11_7_envelopeCondition hn (C_inv t)
    (higham11_7_permutedRightEnvelope sigma (L_hat t) (D_hat t))
  let M : ι → ℝ := fun t =>
    higham11_7_totalGlobalCondition hn A A_inv sigma (L_hat t) (D_hat t)
  let D : ι → ℝ := fun t => fixed + F t
  let err : ι → ℝ := fun t =>
    infNormVec (fun i => x i - x_hat t i) / infNormVec x
  have hfixed : 0 ≤ fixed := by
    dsimp [fixed, ch7SkeelCondAtSolutionInf, ch7CondEFAtSolutionInf]
    exact div_nonneg
      (ch7ForwardBoundEF_nonneg n hn A_inv (fun i j => |A i j|)
        (fun _ => 0) x (fun _ _ => abs_nonneg _) (fun _ => le_rfl))
      (le_of_lt hx)
  have hF : ∀ t, 0 ≤ F t := fun t => by
    dsimp [F]
    exact higham11_7_factorCondition_nonneg hn A_inv sigma (L_hat t) (D_hat t)
  have hD : ∀ t, 0 ≤ D t := fun t => add_nonneg hfixed (hF t)
  have hM : ∀ t, 0 ≤ M t := fun t => by
    dsimp [M]
    exact higham11_7_totalGlobalCondition_nonneg
      hn A A_inv sigma (L_hat t) (D_hat t)
  have hexact : ∀ t, err t ≤ eta t / (1 - eta t * M t) * D t := by
    intro t
    have hsmall : eta t * M t < 1 := by
      simpa only [M] using
        (lt_of_le_of_lt (hhalf t) (by norm_num : (1 : ℝ) / 2 < 1))
    dsimp [err, M, D, fixed, F]
    exact higham11_7_forwardError_exact_from_backward_errors
      hn A A_inv sigma (L_hat t) (D_hat t) x (x_hat t) b
      (DeltaSolve t) (DeltaFactor t) (eta t) (heta t)
      (hSolve t) (hFactor t) hInv hAx (hPerturbed t) hsmall hx
  have hfirst : FamilyFirstOrderLe l U.unit
      (fun t => p_n * U.unit t * (fixed + F t)) err := by
    exact higham11_7_familyFirstOrderLe_of_denominator U
      p_n Mmax Dmax hp hMmax hDmax eta M D err heta hM hD heta_le
      (by simpa [M] using hhalf) (by simpa [M] using hMbound)
      (by simpa [D, fixed, F] using hDbound) hexact
  have hCnonneg : ∀ t, 0 ≤ Ccond t := fun t => by
    dsimp [Ccond]
    exact higham11_7_envelopeCondition_nonneg hn (C_inv t)
      (higham11_7_permutedRightEnvelope sigma (L_hat t) (D_hat t))
      (fun i j => Finset.sum_nonneg fun q _ =>
        mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have htransfer : FamilyLinearRemainderLe l U.unit
      (fun t => condSkeel n hn A A_inv * Ccond t) F := by
    refine ⟨fun t => p_n * Fmax * Cmax * U.unit t, ?_, ?_, ?_⟩
    · intro t
      exact mul_nonneg (mul_nonneg (mul_nonneg hp hFmax) hCmax)
        (U.unit_nonneg t)
    · intro t
      let B := higham11_7_permutedLeftFactor sigma (L_hat t)
      let C := higham11_7_permutedRightFactor sigma (L_hat t) (D_hat t)
      let Cenv := higham11_7_permutedRightEnvelope sigma (L_hat t) (D_hat t)
      have hprod : matMul n B C = fun i j => A i j + DeltaFactor t i j := by
        simpa [B, C] using
          higham11_7_permutedLeft_mul_rightFactor_eq_of_BlockLDLTSpec
            (fun i j => A i j + DeltaFactor t i j) (L_hat t) (D_hat t)
            sigma (hspec t)
      have hH : matMul n (absMatrix n B) Cenv =
          higham11_7_permutedAbsLDLT sigma (L_hat t) (D_hat t) := by
        simpa [B, Cenv] using
          higham11_7_permutedLeft_mul_rightEnvelope_eq_permutedAbsLDLT
            sigma (L_hat t) (D_hat t)
      have hpert := higham11_7_perturbed_product_envelopeCondition_le hn
        A A_inv B C (C_inv t) Cenv (DeltaFactor t) (eta t) (heta t)
        hprod (hCright t)
        (fun i j => Finset.sum_nonneg fun q _ =>
          mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (fun i j => by simpa [hH] using hFactor t i j)
      have hFC : F t * Ccond t ≤ Fmax * Cmax := by
        calc
          F t * Ccond t ≤ Fmax * Ccond t :=
            mul_le_mul_of_nonneg_right (by simpa [F] using hFbound t) (hCnonneg t)
          _ ≤ Fmax * Cmax :=
            mul_le_mul_of_nonneg_left (by simpa [Ccond] using hCbound t) hFmax
      have hetaFC : eta t * F t * Ccond t ≤
          p_n * Fmax * Cmax * U.unit t := by
        calc
          eta t * F t * Ccond t = eta t * (F t * Ccond t) := by ring
          _ ≤ (p_n * U.unit t) * (F t * Ccond t) :=
            mul_le_mul_of_nonneg_right (heta_le t)
              (mul_nonneg (hF t) (hCnonneg t))
          _ ≤ (p_n * U.unit t) * (Fmax * Cmax) :=
            mul_le_mul_of_nonneg_left hFC
              (mul_nonneg hp (U.unit_nonneg t))
          _ = p_n * Fmax * Cmax * U.unit t := by ring
      rw [hH] at hpert
      change F t ≤ condSkeel n hn A A_inv * Ccond t +
        eta t * F t * Ccond t at hpert
      exact hpert.trans (add_le_add le_rfl hetaFC)
    · simpa only [mul_assoc] using
        (Asymptotics.isBigO_refl U.unit l).const_mul_left
          (p_n * Fmax * Cmax)
  have hsecond := FamilyFirstOrderLe.coefficient_of_linear_transfer_to
    hp U.unit_nonneg hfirst htransfer
  apply hsecond.mono_leading
  intro t
  have hsolution := ch7SkeelCondAtSolutionInf_le_condSkeel
    n hn A A_inv x hx
  have hCone : 1 ≤ Ccond t := by
    dsimp [Ccond]
    exact higham11_7_one_le_envelopeCondition_of_inverse hn
      (higham11_7_permutedRightFactor sigma (L_hat t) (D_hat t)) (C_inv t)
      (higham11_7_permutedRightEnvelope sigma (L_hat t) (D_hat t))
      (hCright t)
      (higham11_7_permutedRightFactor_abs_le_envelope
        sigma (L_hat t) (D_hat t))
  have hcondA : 0 ≤ condSkeel n hn A A_inv :=
    higham9_23_condSkeel_nonneg n hn A A_inv
  have hbase : fixed + condSkeel n hn A A_inv * Ccond t ≤
      2 * condSkeel n hn A A_inv * Ccond t := by
    have hA_le : condSkeel n hn A A_inv ≤
        condSkeel n hn A A_inv * Ccond t := by
      calc
        condSkeel n hn A A_inv = condSkeel n hn A A_inv * 1 := by ring
        _ ≤ condSkeel n hn A A_inv * Ccond t :=
          mul_le_mul_of_nonneg_left hCone hcondA
    dsimp [fixed]
    linarith
  have hpu : 0 ≤ p_n * U.unit t := mul_nonneg hp (U.unit_nonneg t)
  calc
    p_n * U.unit t * (fixed + condSkeel n hn A A_inv * Ccond t)
        ≤ p_n * U.unit t *
          (2 * condSkeel n hn A A_inv * Ccond t) :=
            mul_le_mul_of_nonneg_left hbase hpu
    _ = (2 * p_n) * U.unit t * condSkeel n hn A A_inv * Ccond t := by ring

/-! ## The exact Chapter 9 equation (9.14) comparison named in §11.1.1 -/

/-- Bunch's sharp multiplier `3.07 (n-1)^0.446`, with both decimal constants
represented exactly as rationals. -/
noncomputable def higham11_1_bunchSharpGrowthMultiplier (n : ℕ) : ℝ :=
  (307 : ℝ) / 100 * Real.rpow ((n - 1 : ℕ) : ℝ) ((223 : ℝ) / 500)

/-- The right-hand side of Bunch's cited detailed analysis: the sharp Chapter
11 multiplier times Wilkinson's Chapter 9 complete-pivoting bound (9.14). -/
noncomputable def higham11_1_bunchSharpGrowthBound (n : ℕ) : ℝ :=
  higham11_1_bunchSharpGrowthMultiplier n *
    higham9_14_completePivotWilkinsonBound n

theorem higham11_1_bunchSharpGrowthMultiplier_nonneg (n : ℕ) :
    0 ≤ higham11_1_bunchSharpGrowthMultiplier n := by
  unfold higham11_1_bunchSharpGrowthMultiplier
  exact mul_nonneg (by norm_num)
    (Real.rpow_nonneg (Nat.cast_nonneg (n - 1)) _)

theorem higham11_1_bunchSharpGrowthBound_nonneg (n : ℕ) :
    0 ≤ higham11_1_bunchSharpGrowthBound n := by
  exact mul_nonneg (higham11_1_bunchSharpGrowthMultiplier_nonneg n)
    (higham9_14_completePivotWilkinsonBound_nonneg n)

/-- Definition-level bridge confirming that the Chapter 11 bound consumes the
literal Chapter 9 `(9.14)` declaration, rather than a duplicate local bound. -/
theorem higham11_1_bunchSharpGrowthBound_eq_multiplier_mul_higham9_14 (n : ℕ) :
    higham11_1_bunchSharpGrowthBound n =
      ((307 : ℝ) / 100 * Real.rpow ((n - 1 : ℕ) : ℝ) ((223 : ℝ) / 500)) *
        higham9_14_completePivotWilkinsonBound n := by
  rfl

end NumStability
