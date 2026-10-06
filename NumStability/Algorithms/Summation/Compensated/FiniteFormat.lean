import NumStability.Analysis.FloatingPointArithmetic
import NumStability.Algorithms.Summation.Compensated.CorrectionFormula
import NumStability.Algorithms.Summation.Compensated.FastTwoSum

open Classical

namespace NumStability

/-!
# Finite-format support for compensated summation

Reusable safe-completion semantics for finite binary round-to-even arithmetic,
operation bridges, and the local correction-formula exactness certificate.
Numbered Higham equation closures live under
`NumStability.Source.Higham.Chapter04`.
-/

/-- The *safe completion* of a finite binary format to an `FPModel`.

`fl_add`/`fl_sub` use `finiteRoundToEvenOp` in the finite normal range (where the
standard relative-error model holds); the `a = 0` guard on addition makes
`fl(0 + x) = x` hold definitionally, as `FPModel` requires; outside the normal
range the operation falls back to the exact real result, which keeps the model
axioms unconditional without affecting any computation that stays in range.
`fl_mul`/`fl_div`/`fl_sqrt` are exact (unused by compensated summation). -/
noncomputable def kahanFF_model (fmt : FloatingPointFormat) : FPModel where
  u := fmt.unitRoundoff
  u_nonneg := fmt.unitRoundoff_nonneg
  fl_add := fun a b =>
    if a = 0 then b
    else if fmt.finiteNormalRange (a + b) then
      fmt.finiteRoundToEvenOp BasicOp.add a b
    else a + b
  fl_sub := fun a b =>
    if fmt.finiteNormalRange (a - b) then
      fmt.finiteRoundToEvenOp BasicOp.sub a b
    else a - b
  fl_mul := fun a b => a * b
  fl_div := fun a b => a / b
  fl_sqrt := fun a => Real.sqrt a
  fl_add_zero := by
    intro x
    simp
  model_add := by
    intro x y
    by_cases hx : x = 0
    · exact ⟨0, by simpa using fmt.unitRoundoff_nonneg, by subst hx; simp⟩
    · by_cases hr : fmt.finiteNormalRange (x + y)
      · obtain ⟨δ, hδ, hval⟩ :=
          fmt.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
            (op := BasicOp.add) (x := x) (y := y)
            (by simpa [BasicOp.exact] using hr)
        refine ⟨δ, le_of_lt hδ, ?_⟩
        simp only [if_neg hx, if_pos hr]
        rw [hval]; simp [BasicOp.exact]
      · exact ⟨0, by simpa using fmt.unitRoundoff_nonneg, by
          simp only [if_neg hx, if_neg hr]; ring⟩
  model_sub := by
    intro x y
    by_cases hr : fmt.finiteNormalRange (x - y)
    · obtain ⟨δ, hδ, hval⟩ :=
        fmt.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
          (op := BasicOp.sub) (x := x) (y := y)
          (by simpa [BasicOp.exact] using hr)
      refine ⟨δ, le_of_lt hδ, ?_⟩
      simp only [if_pos hr]
      rw [hval]; simp [BasicOp.exact]
    · exact ⟨0, by simpa using fmt.unitRoundoff_nonneg, by
        simp only [if_neg hr]; ring⟩
  model_mul := by
    intro x y
    exact ⟨0, by simpa using fmt.unitRoundoff_nonneg, by simp⟩
  model_div := by
    intro x y _hy
    exact ⟨0, by simpa using fmt.unitRoundoff_nonneg, by simp⟩
  model_sqrt := by
    intro x _hx
    exact ⟨0, by simpa using fmt.unitRoundoff_nonneg, by simp⟩

/-- The safe-completion model's unit roundoff is the format's unit roundoff. -/
theorem kahanFF_model_u (fmt : FloatingPointFormat) :
    (kahanFF_model fmt).u = fmt.unitRoundoff := rfl

/-- Definitional unfolding of the safe-completion addition. -/
theorem kahanFF_model_fl_add (fmt : FloatingPointFormat) (a b : ℝ) :
    (kahanFF_model fmt).fl_add a b =
      (if a = 0 then b
      else if fmt.finiteNormalRange (a + b) then
        fmt.finiteRoundToEvenOp BasicOp.add a b
      else a + b) := rfl

/-- Definitional unfolding of the safe-completion subtraction. -/
theorem kahanFF_model_fl_sub (fmt : FloatingPointFormat) (a b : ℝ) :
    (kahanFF_model fmt).fl_sub a b =
      (if fmt.finiteNormalRange (a - b) then
        fmt.finiteRoundToEvenOp BasicOp.sub a b
      else a - b) := rfl

/-! ### Bridge lemmas: the completion agrees with genuine finite round-to-even -/

/-- When the current term `b` is representable and the running add is either in
finite normal range or already exact, the safe-completion addition coincides
with genuine finite round-to-even addition. -/
theorem kahanFF_fl_add_eq_finiteRoundToEvenOp
    (fmt : FloatingPointFormat) {a b : ℝ}
    (hb : fmt.finiteSystem b)
    (hdisj :
      fmt.finiteNormalRange (a + b) ∨
        fmt.finiteRoundToEvenOp BasicOp.add a b = a + b) :
    (kahanFF_model fmt).fl_add a b =
      fmt.finiteRoundToEvenOp BasicOp.add a b := by
  rw [kahanFF_model_fl_add]
  split_ifs with ha0 hr
  · subst ha0
    have hbb : fmt.finiteSystem (BasicOp.exact BasicOp.add 0 b) := by
      simpa [BasicOp.exact] using hb
    rw [fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem hbb]
    simp [BasicOp.exact]
  · rfl
  · rcases hdisj with h | h
    · exact absurd h hr
    · exact h.symm

/-- When the exact real sum `a + b` is representable, the safe-completion
addition returns it exactly. -/
theorem kahanFF_fl_add_eq_of_finiteSystem
    (fmt : FloatingPointFormat) {a b : ℝ}
    (hab : fmt.finiteSystem (a + b)) :
    (kahanFF_model fmt).fl_add a b = a + b := by
  rw [kahanFF_model_fl_add]
  split_ifs with ha0 hr
  · subst ha0; simp
  · have hab' : fmt.finiteSystem (BasicOp.exact BasicOp.add a b) := by
      simpa [BasicOp.exact] using hab
    rw [fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem hab']
    simp [BasicOp.exact]
  · rfl

/-- When the exact real difference `a - b` is representable, the safe-completion
subtraction returns it exactly. -/
theorem kahanFF_fl_sub_eq_of_finiteSystem
    (fmt : FloatingPointFormat) {a b : ℝ}
    (hab : fmt.finiteSystem (a - b)) :
    (kahanFF_model fmt).fl_sub a b = a - b := by
  rw [kahanFF_model_fl_sub]
  split_ifs with hr
  · have hab' : fmt.finiteSystem (BasicOp.exact BasicOp.sub a b) := by
      simpa [BasicOp.exact] using hab
    rw [fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem hab']
    simp [BasicOp.exact]
  · rfl

/-! ### Per-step equation-(4.7) exactness in the finite format -/

/-- The applicability of Higham's correction formula (4.7) at one step of a
recursive sum with running value `a` and current term `b`: `b` is representable,
and either the Dekker magnitude order `|b| < |a|` holds with `a + b` in finite
normal range (the abstract (4.7) hypothesis), or the running add is already
exact (which covers, in particular, the first add from `a = 0`). -/
def kahanFF_stepCondition (fmt : FloatingPointFormat) (a b : ℝ) : Prop :=
  fmt.finiteSystem b ∧
    ((fmt.finiteSystem a ∧ |b| ≤ |a| ∧ fmt.finiteNormalRange (a + b)) ∨
      fmt.finiteRoundToEvenOp BasicOp.add a b = a + b)

/-- Equation (4.7) for the safe-completion model at one step.

Under `kahanFF_stepCondition`, the Kahan correction trace `(s, e)` computed by
the safe-completion model on `(a, b)` recovers the running sum exactly:
`a + b = s + e`.  The proof obtains the finite `FastTwoSumFiniteCertificate`
(the engine behind `finiteCorrectionFormulaTrace_exact_of_base2_abs_gt`), uses
its representability fields to show the completion coincides with genuine finite
round-to-even on the whole trace, and concludes by the certificate's exact
intermediate arithmetic. -/
theorem kahanFF_step_exact
    (fmt : FloatingPointFormat) (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    (a b : ℝ) (hstep : kahanFF_stepCondition fmt a b) :
    CorrectionFormulaTrace.exact a b
      ({ s := (kahanFF_model fmt).fl_add a b,
         e := (kahanFF_model fmt).fl_add
                ((kahanFF_model fmt).fl_sub a
                  ((kahanFF_model fmt).fl_add a b)) b }
        : CorrectionFormulaTrace) := by
  obtain ⟨hb, hmain⟩ := hstep
  -- Finite FastTwoSum certificate for `(a, b)`.
  have hcert : FastTwoSumFiniteCertificate fmt a b := by
    rcases hmain with ⟨ha, hab, hrange⟩ | hexadd
    · exact FastTwoSumFiniteCertificate.of_base2_abs_le fmt hbeta ht ha hb hab hrange
    · exact FastTwoSumFiniteCertificate.of_exact_add fmt a b hb hexadd
  -- The running add is in normal range or exact (feeds the main-add bridge).
  have hdisj :
      fmt.finiteNormalRange (a + b) ∨
        fmt.finiteRoundToEvenOp BasicOp.add a b = a + b := by
    rcases hmain with ⟨_, _, hrange⟩ | hexadd
    · exact Or.inl hrange
    · exact Or.inr hexadd
  have hs : (kahanFF_model fmt).fl_add a b =
      fmt.finiteRoundToEvenOp BasicOp.add a b :=
    kahanFF_fl_add_eq_finiteRoundToEvenOp fmt hb hdisj
  have hsub_fin :
      fmt.finiteSystem (a - fmt.finiteRoundToEvenOp BasicOp.add a b) :=
    hcert.finite_a_sub_s
  have herr_fin :
      fmt.finiteSystem ((a + b) - fmt.finiteRoundToEvenOp BasicOp.add a b) :=
    hcert.finite_error
  have hsub_br :
      (kahanFF_model fmt).fl_sub a (fmt.finiteRoundToEvenOp BasicOp.add a b) =
        a - fmt.finiteRoundToEvenOp BasicOp.add a b :=
    kahanFF_fl_sub_eq_of_finiteSystem fmt hsub_fin
  have hadd_br :
      (kahanFF_model fmt).fl_add
          (a - fmt.finiteRoundToEvenOp BasicOp.add a b) b =
        (a - fmt.finiteRoundToEvenOp BasicOp.add a b) + b := by
    apply kahanFF_fl_add_eq_of_finiteSystem
    have hrw :
        (a - fmt.finiteRoundToEvenOp BasicOp.add a b) + b =
          (a + b) - fmt.finiteRoundToEvenOp BasicOp.add a b := by ring
    rw [hrw]; exact herr_fin
  show a + b =
    (kahanFF_model fmt).fl_add a b +
      (kahanFF_model fmt).fl_add
        ((kahanFF_model fmt).fl_sub a
          ((kahanFF_model fmt).fl_add a b)) b
  rw [hs, hsub_br, hadd_br]
  ring

end NumStability
