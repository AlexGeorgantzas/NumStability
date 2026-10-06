import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Rounding
import NumStability.Analysis.Summation.Signs

/-!
# Summation condition numbers and rounding-error bounds

Reusable condition-number results and floating-point summation error theorems.
Source citations record provenance, but every declaration has a semantic,
source-independent API. Generic finite-sum sign identities live in the sibling
`NumStability.Analysis.Summation.Signs` module.
-/

namespace NumStability

open scoped BigOperators

/-! ## Componentwise condition number for summation -/

/-- Componentwise relative perturbation model for the exact summation map. -/
def SummationComponentwisePerturbation {ι : Type*} (v Δ : ι → ℝ) (ε : ℝ) : Prop :=
  ∀ i, |Δ i| ≤ ε * |v i|

/-- Higham Problem 4.1's closed-form condition number for
`S(x) = sum_i x_i` under componentwise relative perturbations. -/
noncomputable def summationConditionNumber {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    ℝ :=
  (∑ i, |v i|) / |∑ i, v i|

/-- Problem 4.1 closed form, exposed as a named theorem for lookup. -/
theorem summationConditionNumber_eq {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    summationConditionNumber v = (∑ i, |v i|) / |∑ i, v i| := rfl

/-- The absolute output perturbation of exact summation is bounded by the
componentwise perturbation radius times `sum |xᵢ|`. -/
theorem summationComponentwisePerturbation_abs_error_le {ι : Type*} [Fintype ι]
    (v Δ : ι → ℝ) {ε : ℝ}
    (hΔ : SummationComponentwisePerturbation v Δ ε) :
    |(∑ i, (v i + Δ i)) - ∑ i, v i| ≤ ε * ∑ i, |v i| := by
  have hdiff :
      (∑ i, (v i + Δ i)) - ∑ i, v i = ∑ i, Δ i := by
    rw [Finset.sum_add_distrib]
    ring
  rw [hdiff]
  calc
    |∑ i, Δ i| ≤ ∑ i, |Δ i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ε * |v i| :=
      Finset.sum_le_sum (fun i _hi => hΔ i)
    _ = ε * ∑ i, |v i| := by
      rw [Finset.mul_sum]

/-- Absorb an additive residual bound into componentwise summation
coefficients.

If `computed` is within `B` of a coefficient representation
`sum_i v_i*(1+coeff_i)` and the input absolute-value sum is positive, then the
residual can be distributed across the inputs by sign-aligned coefficient
increments, giving an exact coefficient representation. -/
theorem exists_summation_coefficients_of_abs_sub_sum_coeff_le
    {ι : Type*} [Fintype ι] (v : ι → ℝ) (coeff : ι → ℝ)
    {computed B : ℝ}
    (hres : |computed - ∑ i, v i * (1 + coeff i)| ≤ B)
    (hsumAbs : 0 < ∑ i, |v i|) :
    ∃ μ : ι → ℝ,
      (∀ i,
        |μ i - coeff i| ≤ B / (∑ j, |v j|)) ∧
      computed = ∑ i, v i * (1 + μ i) := by
  let S : ℝ := ∑ i, |v i|
  let base : ℝ := ∑ i, v i * (1 + coeff i)
  let r : ℝ := computed - base
  let ν : ι → ℝ := fun i => (r / S) * summationAbsSign (v i)
  refine ⟨fun i => coeff i + ν i, ?_, ?_⟩
  · intro i
    have hSpos : 0 < S := by simpa [S] using hsumAbs
    have hr : |r| ≤ B := by
      simpa [r, base] using hres
    have hdiv : |r| / S ≤ B / S :=
      div_le_div_of_nonneg_right hr (le_of_lt hSpos)
    calc
      |coeff i + ν i - coeff i| = |ν i| := by ring_nf
      _ = |r / S| * |summationAbsSign (v i)| := by
          dsimp [ν]
          rw [abs_mul]
      _ = |r| / S := by
          rw [abs_summationAbsSign, mul_one, abs_div,
            abs_of_pos hSpos]
      _ ≤ B / S := hdiv
      _ = B / (∑ j, |v j|) := by rfl
  · have hSpos : 0 < S := by simpa [S] using hsumAbs
    have hsumν :
        (∑ i, v i * ν i) = r := by
      calc
        (∑ i, v i * ν i)
            = ∑ i, (r / S) * |v i| := by
                apply Finset.sum_congr rfl
                intro i _hi
                dsimp [ν]
                calc
                  v i * (r / S * summationAbsSign (v i))
                      = (r / S) * (summationAbsSign (v i) * v i) := by
                          ring
                  _ = (r / S) * |v i| := by
                        rw [summationAbsSign_mul_eq_abs]
        _ = (r / S) * S := by
              rw [Finset.mul_sum]
        _ = r := by
              field_simp [hSpos.ne']
    calc
      computed = base + r := by simp [r, base]
      _ = ∑ i, v i * (1 + coeff i) + ∑ i, v i * ν i := by
            rw [hsumν]
      _ = ∑ i, v i * (1 + (coeff i + ν i)) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro i _hi
            ring

/-- Distribute an additive residual across source summation coefficients.

If `|r| <= C * sum_i |v_i|`, then `r` can be written exactly as
`sum_i v_i * eta_i` with every `|eta_i| <= C`.  This is the source-coefficient
converse to the usual triangle-inequality forward bound for summation. -/
theorem exists_summation_source_coefficients_of_abs_le_mul_sum_abs
    {ι : Type*} [Fintype ι] (v : ι → ℝ) {r C : ℝ}
    (hC : 0 ≤ C) (hr : |r| ≤ C * ∑ i, |v i|) :
    ∃ η : ι → ℝ,
      (∀ i, |η i| ≤ C) ∧
      r = ∑ i, v i * η i := by
  let S : ℝ := ∑ i, |v i|
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg (fun i _hi => abs_nonneg (v i))
  rcases lt_or_eq_of_le hS_nonneg with hSpos | hSzero
  · let η : ι → ℝ := fun i => (r / S) * summationAbsSign (v i)
    refine ⟨η, ?_, ?_⟩
    · intro i
      have hdiv : |r| / S ≤ (C * S) / S :=
        div_le_div_of_nonneg_right hr (le_of_lt hSpos)
      have hcancel : (C * S) / S = C := by
        field_simp [hSpos.ne']
      calc
        |η i| = |r| / S := by
          dsimp [η]
          rw [abs_mul, abs_summationAbsSign, mul_one, abs_div,
            abs_of_pos hSpos]
        _ ≤ (C * S) / S := hdiv
        _ = C := hcancel
    · have hsumη :
          (∑ i, v i * η i) = r := by
        calc
          (∑ i, v i * η i)
              = ∑ i, (r / S) * |v i| := by
                  apply Finset.sum_congr rfl
                  intro i _hi
                  dsimp [η]
                  calc
                    v i * (r / S * summationAbsSign (v i))
                        = (r / S) * (summationAbsSign (v i) * v i) := by
                            ring
                    _ = (r / S) * |v i| := by
                          rw [summationAbsSign_mul_eq_abs]
          _ = (r / S) * S := by
                rw [Finset.mul_sum]
          _ = r := by
                field_simp [hSpos.ne']
      exact hsumη.symm
  · have habs_nonpos : |r| ≤ 0 := by
      have hsum_zero : (∑ i, |v i|) = 0 := by
        simpa [S] using hSzero.symm
      simpa [hsum_zero] using hr
    have hr0 : r = 0 := by
      exact abs_eq_zero.mp (le_antisymm habs_nonpos (abs_nonneg r))
    refine ⟨fun _ => 0, ?_, ?_⟩
    · intro _i
      simpa using hC
    · simp [hr0]

/-- Dividing the preceding perturbation inequality by the nonzero exact sum
gives the condition-number bound. -/
theorem summationComponentwisePerturbation_rel_error_le_condition {ι : Type*}
    [Fintype ι] (v Δ : ι → ℝ) {ε : ℝ}
    (hΔ : SummationComponentwisePerturbation v Δ ε)
    (hsum : (∑ i, v i) ≠ 0) :
    |(∑ i, (v i + Δ i)) - ∑ i, v i| / |∑ i, v i| ≤
      ε * summationConditionNumber v := by
  have hden : 0 < |∑ i, v i| := abs_pos.mpr hsum
  have habs := summationComponentwisePerturbation_abs_error_le v Δ hΔ
  calc
    |(∑ i, (v i + Δ i)) - ∑ i, v i| / |∑ i, v i| ≤
        (ε * ∑ i, |v i|) / |∑ i, v i| :=
      div_le_div_of_nonneg_right habs (le_of_lt hden)
    _ = ε * summationConditionNumber v := by
      rw [summationConditionNumber_eq]
      ring

/-- The closed-form condition number is sharp: the sign-aligned componentwise
perturbation attains the upper bound for every nonnegative perturbation radius. -/
theorem summationConditionNumber_attained {ι : Type*} [Fintype ι]
    (v : ι → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (_hsum : (∑ i, v i) ≠ 0) :
    ∃ Δ : ι → ℝ,
      SummationComponentwisePerturbation v Δ ε ∧
        |(∑ i, (v i + Δ i)) - ∑ i, v i| / |∑ i, v i| =
          ε * summationConditionNumber v := by
  by_cases hsum_nonneg : 0 ≤ ∑ i, v i
  · refine ⟨fun i => ε * |v i|, ?_, ?_⟩
    · intro i
      rw [abs_mul, abs_of_nonneg hε, abs_of_nonneg (abs_nonneg (v i))]
    · have hdiff :
          (∑ i, (v i + ε * |v i|)) - ∑ i, v i =
            ε * ∑ i, |v i| := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
        ring
      have hsum_abs_nonneg : 0 ≤ ε * ∑ i, |v i| :=
        mul_nonneg hε (Finset.sum_nonneg (fun i _hi => abs_nonneg (v i)))
      rw [hdiff, abs_of_nonneg hsum_abs_nonneg, summationConditionNumber_eq]
      ring
  · refine ⟨fun i => -ε * |v i|, ?_, ?_⟩
    · intro i
      rw [abs_mul, abs_neg, abs_of_nonneg hε,
        abs_of_nonneg (abs_nonneg (v i))]
    · have hdiff :
          (∑ i, (v i + -ε * |v i|)) - ∑ i, v i =
            -ε * ∑ i, |v i| := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
        ring
      have hsum_abs_nonneg : 0 ≤ ε * ∑ i, |v i| :=
        mul_nonneg hε (Finset.sum_nonneg (fun i _hi => abs_nonneg (v i)))
      rw [hdiff]
      have hneg : abs (-ε * ∑ i, |v i|) = ε * ∑ i, |v i| := by
        have hrewrite : -ε * ∑ i, |v i| = -(ε * ∑ i, |v i|) := by
          ring
        rw [hrewrite, abs_neg, abs_of_nonneg hsum_abs_nonneg]
      rw [hneg, summationConditionNumber_eq]
      ring

/-- Higham Problem 4.1: the summation condition number is always at least one
on the nonzero exact-sum domain. -/
theorem one_le_summationConditionNumber {ι : Type*} [Fintype ι] (v : ι → ℝ)
    (hsum : (∑ i, v i) ≠ 0) :
    1 ≤ summationConditionNumber v := by
  have hden_pos : 0 < |∑ i, v i| := abs_pos.mpr hsum
  have htriangle : |∑ i, v i| ≤ ∑ i, |v i| :=
    Finset.abs_sum_le_sum_abs _ _
  have hdiv := div_le_div_of_nonneg_right htriangle (le_of_lt hden_pos)
  rw [summationConditionNumber_eq]
  simpa [div_self hden_pos.ne'] using hdiv

/-- Higham Problem 4.1: one-signed data have condition number exactly one,
provided the exact sum is nonzero. -/
theorem summationConditionNumber_eq_one_of_oneSigned {ι : Type*} [Fintype ι]
    (v : ι → ℝ) (hv : OneSigned v) (hsum : (∑ i, v i) ≠ 0) :
    summationConditionNumber v = 1 := by
  have hden : |∑ i, v i| ≠ 0 := abs_ne_zero.mpr hsum
  rw [summationConditionNumber_eq, sum_abs_eq_abs_sum_of_oneSigned v hv,
    div_self hden]

/-- Higham Problem 4.1: on the nonzero exact-sum domain, the condition number
takes the value `1` exactly in the no-cancellation one-signed case. -/
theorem summationConditionNumber_eq_one_iff_oneSigned {ι : Type*} [Fintype ι]
    (v : ι → ℝ) (hsum : (∑ i, v i) ≠ 0) :
    summationConditionNumber v = 1 ↔ OneSigned v := by
  constructor
  · intro hcond
    apply (sum_abs_eq_abs_sum_iff_oneSigned v).1
    have hden : |∑ i, v i| ≠ 0 := abs_ne_zero.mpr hsum
    have hmul :
        (summationConditionNumber v) * |∑ i, v i| =
          1 * |∑ i, v i| := by
      rw [hcond]
    rw [summationConditionNumber_eq] at hmul
    simpa [div_mul_cancel₀ _ hden] using hmul
  · intro hv
    exact summationConditionNumber_eq_one_of_oneSigned v hv hsum

/-- Product of the suffix of local summation factors that affects term `i`.

For left-to-right summation with local factors `1 + delta j`, the term inserted
at step `i` is multiplied by every factor from step `i` through the final step. -/
noncomputable def sumSuffixErrorProduct : (n : ℕ) → (Fin n → ℝ) → Fin n → ℝ
  | 0, _ => fun i => i.elim0
  | n + 1, delta =>
      Fin.lastCases (1 + delta (Fin.last n))
        (fun i => sumSuffixErrorProduct n (fun j => delta j.castSucc) i *
          (1 + delta (Fin.last n)))

/-- The recursive suffix-factor definition is the source-style product over
all local factors from index `i` through the final accumulation step. -/
theorem sumSuffixErrorProduct_eq_prod_if (n : ℕ) (delta : Fin n → ℝ)
    (i : Fin n) :
    sumSuffixErrorProduct n delta i =
      ∏ j : Fin n, if i.val ≤ j.val then 1 + delta j else 1 := by
  induction n with
  | zero =>
      exact i.elim0
  | succ n ih =>
      refine Fin.lastCases ?_ ?_ i
      · rw [Fin.prod_univ_castSucc]
        simp [sumSuffixErrorProduct]
        have hprefix :
            (∏ x : Fin n, if n ≤ x.val then 1 + delta x.castSucc else 1) = 1 := by
          apply Finset.prod_eq_one
          intro j _hj
          simp [Nat.not_le.mpr j.isLt]
        calc
          1 + delta (Fin.last n) =
              1 * (1 + delta (Fin.last n)) := by ring
          _ =
              (∏ x : Fin n, if n ≤ x.val then 1 + delta x.castSucc else 1) *
                (1 + delta (Fin.last n)) :=
              congrArg (fun a => a * (1 + delta (Fin.last n))) hprefix.symm
      · intro i
        rw [Fin.prod_univ_castSucc]
        simp [sumSuffixErrorProduct, ih]

/-- A suffix product of local summation factors is itself a `1 + θ`
factor, with the `gamma` index equal to the number of factors in that suffix.

This is the variable-budget form needed for Higham Problem 4.3: the first
two terms pass through all remaining additions, while a term inserted later
passes through only the suffix of additions after its insertion. -/
lemma sumSuffixErrorProduct_exists_theta_le_gamma (fp : FPModel) (n : ℕ)
    (delta : Fin n → ℝ) (hdelta : ∀ i, |delta i| ≤ fp.u)
    (i : Fin n) (hvalid : gammaValid fp (n - i.val)) :
    ∃ θ : ℝ, |θ| ≤ gamma fp (n - i.val) ∧
      sumSuffixErrorProduct n delta i = 1 + θ := by
  induction n with
  | zero =>
      exact i.elim0
  | succ n ih =>
      refine Fin.lastCases
        (motive := fun i : Fin (n + 1) =>
          gammaValid fp (n + 1 - i.val) →
            ∃ θ : ℝ, |θ| ≤ gamma fp (n + 1 - i.val) ∧
              sumSuffixErrorProduct (n + 1) delta i = 1 + θ)
        ?_ ?_ i hvalid
      · intro hvalidLast
        refine ⟨delta (Fin.last n), ?_, ?_⟩
        · have hpos : 0 < n + 1 - (Fin.last n).val := by simp
          exact le_trans (hdelta (Fin.last n)) (u_le_gamma fp hpos hvalidLast)
        · simp [sumSuffixErrorProduct]
      · intro j hvalidJ
        have hvalidJ' : gammaValid fp (n + 1 - j.val) := by
          simpa using hvalidJ
        have hvalid_old : gammaValid fp (n - j.val) :=
          gammaValid_mono fp (by
            have hj := j.isLt
            omega) hvalidJ'
        obtain ⟨θold, hθold, hprod_old⟩ :=
          ih (fun k : Fin n => delta k.castSucc) (fun k => hdelta k.castSucc) j
            hvalid_old
        have hvalid1 : gammaValid fp 1 :=
          gammaValid_mono fp (by
            have hj := j.isLt
            omega) hvalidJ'
        have hdelta1 : |delta (Fin.last n)| ≤ gamma fp 1 :=
          le_trans (hdelta (Fin.last n)) (u_le_gamma fp one_pos hvalid1)
        have hvalid_comb : gammaValid fp ((n - j.val) + 1) := by
          have hrem : (n - j.val) + 1 = n + 1 - j.val := by
            have hj := j.isLt
            omega
          simpa [hrem] using hvalidJ'
        obtain ⟨θ, hθ, hprod⟩ :=
          gamma_mul fp (n - j.val) 1 θold (delta (Fin.last n))
            hθold hdelta1 hvalid_comb
        refine ⟨θ, ?_, ?_⟩
        · have hrem : (n - j.val) + 1 = n + 1 - j.val := by
            have hj := j.isLt
            omega
          simpa [hrem] using hθ
        · rw [show sumSuffixErrorProduct (n + 1) delta j.castSucc =
              sumSuffixErrorProduct n (fun k : Fin n => delta k.castSucc) j *
                (1 + delta (Fin.last n)) by
                simp [sumSuffixErrorProduct]]
          rw [hprod_old]
          exact hprod

/-- Exact algebraic expansion of a left-to-right rounded-addition fold with
specified local relative-error factors.

This is the factor-level summation identity underlying Higham Chapter 3,
equations (3.1)--(3.2): the initial accumulator carries every local factor,
and each inserted term carries the suffix of factors from its insertion step. -/
theorem foldl_add_mul_one_add_suffix_expansion (n : ℕ)
    (v : Fin n → ℝ) (s : ℝ) (delta : Fin n → ℝ) :
    Fin.foldl n (fun acc i => (acc + v i) * (1 + delta i)) s =
      s * (∏ i : Fin n, (1 + delta i)) +
        ∑ i : Fin n, v i * sumSuffixErrorProduct n delta i := by
  induction n with
  | zero =>
      simp [sumSuffixErrorProduct]
  | succ n ih =>
      rw [Fin.foldl_succ_last, ih]
      rw [Fin.prod_univ_castSucc, Fin.sum_univ_castSucc]
      simp [sumSuffixErrorProduct]
      rw [add_mul, add_mul]
      rw [Finset.sum_mul]
      ring_nf

/-- Floating-point summation with an initial accumulator, expanded with the
actual local addition factors rather than compressed `gamma` witnesses.

This is the FP-facing factor expansion needed for Chapter 3 equations
(3.1)--(3.2) and the sharper small-`nu` dot-product route: each local `fl_add`
contributes one factor `1 + delta i`, and each inserted term carries the suffix
of factors from its insertion step. -/
lemma fl_sum_error_init_suffix_expansion (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (s : ℝ) :
    ∃ delta : Fin n → ℝ,
      (∀ i, |delta i| ≤ fp.u) ∧
      Fin.foldl n (fun acc i => fp.fl_add acc (v i)) s =
        s * (∏ i : Fin n, (1 + delta i)) +
          ∑ i : Fin n, v i * sumSuffixErrorProduct n delta i := by
  induction n generalizing s with
  | zero =>
      exact ⟨fun i => i.elim0, fun i => i.elim0, by simp [sumSuffixErrorProduct]⟩
  | succ n ih =>
      obtain ⟨delta', hdelta', hfold'⟩ :=
        ih (fun i => v i.castSucc) s
      obtain ⟨deltaLast, hdeltaLast, hflLast⟩ :=
        fp.model_add
          (Fin.foldl n (fun acc i => fp.fl_add acc (v i.castSucc)) s)
          (v (Fin.last n))
      refine ⟨Fin.lastCases deltaLast delta', ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ ?_ i
        · simp only [Fin.lastCases_last]
          exact hdeltaLast
        · intro j
          simp only [Fin.lastCases_castSucc]
          exact hdelta' j
      · rw [Fin.foldl_succ_last, hflLast, hfold']
        rw [Fin.prod_univ_castSucc, Fin.sum_univ_castSucc]
        simp [sumSuffixErrorProduct]
        rw [add_mul, add_mul]
        rw [Finset.sum_mul]
        ring_nf

/-- **Summation rounding error lemma** (Higham §3.1).

    For a sequence of values v : Fin n → ℝ, sequential floating-point
    summation (left-to-right, starting from 0) produces a result equal to
    a perturbation of the exact sum:

      fl_sum fp n v = ∑ i, v i * (1 + θ i)

    where each |θ i| ≤ gamma fp n.

    Intuition: the term v 0 passes through all n additions and accumulates
    up to n rounding errors; term v i passes through (n - i) additions.
    The worst case over all terms is γ(n), giving a uniform bound.

    Precondition: gammaValid fp n ensures the denominator of γ is positive.

    Proof sketch: induction on n, peeling the last addition via
    `Fin.foldl_succ_last`.  For each prior term, one new rounding error δ
    combines with the IH witness θ' i via `gamma_mul`: the new error
    θ' i + δ + θ' i · δ satisfies |·| ≤ γ(n+1).  The new term v(last n)
    picks up only δ, which is bounded by u ≤ γ(1) ≤ γ(n+1). -/

lemma fl_sum_error (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hn : gammaValid fp n) :
    ∃ θ : Fin n → ℝ,
      (∀ i, |θ i| ≤ gamma fp n) ∧
      Fin.foldl n (fun acc i => fp.fl_add acc (v i)) 0 =
        ∑ i : Fin n, v i * (1 + θ i) := by
  induction n with
  | zero =>
    exact ⟨fun i => i.elim0, fun i => i.elim0, by simp⟩
  | succ n ih =>
    have hn_pred : gammaValid fp n := gammaValid_mono fp (Nat.le_succ n) hn
    have h1valid : gammaValid fp 1 := gammaValid_mono fp (by omega) hn
    -- Apply IH to v ∘ Fin.castSucc
    obtain ⟨θ', hθ', hfold_n⟩ := ih (fun i => v i.castSucc) hn_pred
    -- Peel the last addition off the fold
    have hfold_last : Fin.foldl (n + 1) (fun acc i => fp.fl_add acc (v i)) 0 =
        fp.fl_add (Fin.foldl n (fun acc i => fp.fl_add acc (v i.castSucc)) 0) (v (Fin.last n)) :=
      Fin.foldl_succ_last _ _
    -- Extract the rounding error δ for the last fl_add
    obtain ⟨δ, hδ, hfl⟩ := fp.model_add
        (Fin.foldl n (fun acc i => fp.fl_add acc (v i.castSucc)) 0) (v (Fin.last n))
    -- Rewrite the fold to its expanded form
    rw [hfold_last, hfl, hfold_n]
    -- Construct θ : Fin (n+1) → ℝ
    refine ⟨Fin.lastCases δ (fun i => θ' i + δ + θ' i * δ), ?_, ?_⟩
    · -- Bound: ∀ i, |θ i| ≤ γ(n+1)
      intro i
      refine Fin.lastCases ?_ ?_ i
      · -- i = Fin.last n: |δ| ≤ u ≤ γ(1) ≤ γ(n+1)
        simp only [Fin.lastCases_last]
        have h1n : gamma fp 1 ≤ gamma fp (n + 1) := gamma_mono fp (by omega) hn
        linarith [u_le_gamma fp one_pos h1valid]
      · -- i = j.castSucc: |θ' j + δ + θ' j * δ| ≤ γ(n+1)
        intro j
        simp only [Fin.lastCases_castSucc]
        have hδ_1 : |δ| ≤ gamma fp 1 :=
          le_trans hδ (u_le_gamma fp one_pos h1valid)
        obtain ⟨θ_j, hθ_j, heq⟩ := gamma_mul fp n 1 (θ' j) δ (hθ' j) hδ_1 hn
        have hval : θ_j = θ' j + δ + θ' j * δ := by
          have hring : (1 + θ' j) * (1 + δ) = 1 + (θ' j + δ + θ' j * δ) := by ring
          linarith [hring, heq]
        rw [← hval]; exact hθ_j
    · -- Sum equality: (∑ θ'·terms + last) * (1+δ) = ∑(n+1) θ·terms
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
      rw [add_mul, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- **Summation rounding error with initial accumulator** (Higham §3.1 generalized).

    For a sequence v : Fin n → ℝ and an initial value s ∈ ℝ, sequential
    floating-point summation starting from s satisfies:

      foldl n (fl_add · (v ·)) s = s * (1 + Θ) + ∑ i, v i * (1 + θ i)

    where |Θ| ≤ γ(n) and each |θ i| ≤ γ(n).

    This generalizes `fl_sum_error` (which has s = 0) and is the key ingredient
    for the tight Higham dot-product bound, where the initial accumulator is
    fl_mul (x 0) (y 0) rather than 0.

    Proof sketch: induction on n, peeling the last addition via
    `Fin.foldl_succ_last`.  The new error δ combines with Θ' (and each θ' i)
    via `gamma_mul` to stay within γ(n+1). -/
lemma fl_sum_error_init (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) (s : ℝ)
    (hn : gammaValid fp n) :
    ∃ (Θ : ℝ) (θ : Fin n → ℝ),
      |Θ| ≤ gamma fp n ∧ (∀ i, |θ i| ≤ gamma fp n) ∧
      Fin.foldl n (fun acc i => fp.fl_add acc (v i)) s =
        s * (1 + Θ) + ∑ i : Fin n, v i * (1 + θ i) := by
  induction n with
  | zero =>
    exact ⟨0, fun i => i.elim0, by simp [gamma], fun i => i.elim0, by simp⟩
  | succ n ih =>
    have hn_pred : gammaValid fp n := gammaValid_mono fp (Nat.le_succ n) hn
    have h1valid : gammaValid fp 1 := gammaValid_mono fp (by omega) hn
    -- Apply IH to v ∘ Fin.castSucc with the same initial accumulator s
    obtain ⟨Θ', θ', hΘ', hθ', hfold_n⟩ := ih (fun i => v i.castSucc) hn_pred
    -- Peel the last addition off the fold
    have hfold_last : Fin.foldl (n + 1) (fun acc i => fp.fl_add acc (v i)) s =
        fp.fl_add (Fin.foldl n (fun acc i => fp.fl_add acc (v i.castSucc)) s)
          (v (Fin.last n)) :=
      Fin.foldl_succ_last _ _
    -- Extract the rounding error δ for the last fl_add
    obtain ⟨δ, hδ, hfl⟩ := fp.model_add
        (Fin.foldl n (fun acc i => fp.fl_add acc (v i.castSucc)) s) (v (Fin.last n))
    -- Rewrite the fold to its expanded form
    rw [hfold_last, hfl, hfold_n]
    -- Construct witnesses: Θ = Θ' + δ + Θ'·δ,  θ = lastCases δ (θ' j + δ + θ' j·δ)
    refine ⟨Θ' + δ + Θ' * δ, Fin.lastCases δ (fun i => θ' i + δ + θ' i * δ), ?_, ?_, ?_⟩
    · -- |Θ' + δ + Θ' * δ| ≤ γ(n+1)
      have hδ_1 : |δ| ≤ gamma fp 1 := le_trans hδ (u_le_gamma fp one_pos h1valid)
      obtain ⟨η, hη, heq⟩ := gamma_mul fp n 1 Θ' δ hΘ' hδ_1 hn
      have hval : η = Θ' + δ + Θ' * δ := by
        have hring : (1 + Θ') * (1 + δ) = 1 + (Θ' + δ + Θ' * δ) := by ring
        linarith [hring, heq]
      rw [← hval]; exact hη
    · -- ∀ i, |θ i| ≤ γ(n+1)
      intro i
      refine Fin.lastCases ?_ ?_ i
      · -- i = Fin.last n: |δ| ≤ u ≤ γ(1) ≤ γ(n+1)
        simp only [Fin.lastCases_last]
        have h1n : gamma fp 1 ≤ gamma fp (n + 1) := gamma_mono fp (by omega) hn
        linarith [u_le_gamma fp one_pos h1valid]
      · -- i = j.castSucc: |θ' j + δ + θ' j * δ| ≤ γ(n+1)
        intro j
        simp only [Fin.lastCases_castSucc]
        have hδ_1 : |δ| ≤ gamma fp 1 := le_trans hδ (u_le_gamma fp one_pos h1valid)
        obtain ⟨θ_j, hθ_j, heq⟩ := gamma_mul fp n 1 (θ' j) δ (hθ' j) hδ_1 hn
        have hval : θ_j = θ' j + δ + θ' j * δ := by
          have hring : (1 + θ' j) * (1 + δ) = 1 + (θ' j + δ + θ' j * δ) := by ring
          linarith [hring, heq]
        rw [← hval]; exact hθ_j
    · -- Sum equality: s*(1+Θ')*(1+δ) + (∑ terms)*(1+δ) + last*(1+δ) = s*(1+Θ) + ∑(n+1) terms
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
      have hsum_rw : ∑ i : Fin n, v i.castSucc * (1 + (θ' i + δ + θ' i * δ)) =
                     (∑ i : Fin n, v i.castSucc * (1 + θ' i)) * (1 + δ) := by
        rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring
      rw [hsum_rw]
      ring

/-- **Tight summation error** (Higham §4.2, eq. 4.4 exact constant).

    For n ≥ 1 values, recursive summation starting from 0 satisfies:
      `fl_sum fp n v = ∑ i, v i * (1 + θ i)`
    where each `|θ i| ≤ γ(n - 1)`.

    This matches Higham's backward error bound γ(n-1), tighter than the
    γ(n) from `fl_sum_error`.  The improvement comes from `fl_add_zero`:
    the first step `fl_add 0 (v 0) = v 0` is exact, reducing the effective
    number of rounding steps from n to n - 1.

    Proof: peel the first step via `Fin.foldl_succ`; apply `fl_add_zero`
    to show it is exact; then apply `fl_sum_error_init` for the remaining
    `n - 1` additions. -/
lemma fl_sum_error_tight (fp : FPModel) (n : ℕ) (hn : 0 < n) (v : Fin n → ℝ)
    (hval : gammaValid fp (n - 1)) :
    ∃ θ : Fin n → ℝ,
      (∀ i, |θ i| ≤ gamma fp (n - 1)) ∧
      Fin.foldl n (fun acc i => fp.fl_add acc (v i)) 0 =
        ∑ i : Fin n, v i * (1 + θ i) := by
  -- Write n = m + 1
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
  simp only [Nat.succ_sub_one] at hval
  -- Peel the first addition: foldl (m+1) f 0 = foldl m f' (f 0 0)
  have hpeel : Fin.foldl (m + 1) (fun acc i => fp.fl_add acc (v i)) 0 =
      Fin.foldl m (fun acc i => fp.fl_add acc (v i.succ)) (fp.fl_add 0 (v 0)) :=
    Fin.foldl_succ _ _
  -- The first step is exact by fl_add_zero
  rw [hpeel, fp.fl_add_zero]
  -- Apply fl_sum_error_init for the remaining m steps
  obtain ⟨Θ, θ, hΘ, hθ, hfold⟩ :=
    fl_sum_error_init fp m (fun i => v i.succ) (v 0) hval
  rw [hfold]
  -- Build η : Fin (m+1) → ℝ via Fin.cons: η 0 = Θ, η i.succ = θ i
  refine ⟨Fin.cons Θ θ, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ ?_ i
    · simp only [Fin.cons_zero]; exact hΘ
    · intro j; simp only [Fin.cons_succ]; exact hθ j
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]

end NumStability
