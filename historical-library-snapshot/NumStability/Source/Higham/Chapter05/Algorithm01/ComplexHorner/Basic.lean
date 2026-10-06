import Mathlib.Tactic
import NumStability.Analysis.ComplexArithmetic

/-!
# Chapter05 Algorithm01 ComplexHorner Basic

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapter5ComplexAlgorithm51` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

/-- One exact complex Horner update. -/
def complexHornerStep (x y a : ℂ) : ℂ := x * y + a

/-- One actual rounded complex Horner update: first the Chapter 3 rounded
complex multiplication, then the Chapter 3 rounded complex addition. -/
noncomputable def fl_complexHornerStep
    (fp : FPModel) (x y a : ℂ) : ℂ :=
  fl_complexAdd fp (fl_complexMul fp x y) a

/-- Exact complex Horner evaluation for descending coefficients. -/
def complexHornerDesc (x : ℂ) : List ℂ → ℂ
  | [] => 0
  | a :: rest => rest.foldl (complexHornerStep x) a

/-- The complex polynomial in descending coefficient order. -/
def complexPolyDesc (x : ℂ) : List ℂ → ℂ
  | [] => 0
  | a :: rest => a * x ^ rest.length + complexPolyDesc x rest

lemma complexHornerFold_eq_acc_mul_pow_add_polyDesc (x : ℂ) :
    ∀ (rest : List ℂ) (y : ℂ),
      rest.foldl (complexHornerStep x) y =
        y * x ^ rest.length + complexPolyDesc x rest := by
  intro rest
  induction rest with
  | nil =>
      intro y
      simp [complexPolyDesc]
  | cons a rest ih =>
      intro y
      simp [List.foldl, complexHornerStep, complexPolyDesc, ih, pow_succ]
      ring

/-- Exact complex Horner evaluation agrees with the displayed polynomial. -/
theorem complexHornerDesc_eq_complexPolyDesc
    (x : ℂ) (coeffsDesc : List ℂ) :
    complexHornerDesc x coeffsDesc = complexPolyDesc x coeffsDesc := by
  cases coeffsDesc with
  | nil => rfl
  | cons a rest =>
      simpa [complexHornerDesc, complexPolyDesc]
        using complexHornerFold_eq_acc_mul_pow_add_polyDesc x rest a

/-- Actual rounded complex Horner evaluation for descending coefficients. -/
noncomputable def fl_complexHornerDesc
    (fp : FPModel) (x : ℂ) : List ℂ → ℂ
  | [] => 0
  | a :: rest => rest.foldl (fl_complexHornerStep fp x) a

/-- The source coefficient `sqrt(2) * gamma_2` for the complex extension of
Algorithm 5.1. -/
noncomputable def complexHornerRunningRadius (fp : FPModel) : ℝ :=
  Real.sqrt 2 * gamma fp 2

/-- One complex Algorithm 5.1 state update. The first component is the actual
rounded Horner value; the second is the exact real running accumulator. -/
noncomputable def fl_complexHornerRunningStep
    (fp : FPModel) (x : ℂ) (state : ℂ × ℝ) (a : ℂ) : ℂ × ℝ :=
  let y := fl_complexHornerStep fp x state.1 a
  (y, ‖x‖ * state.2 + ‖y‖)

/-- Complex Algorithm 5.1 running state, before its final scale. -/
noncomputable def fl_complexHornerRunningState
    (fp : FPModel) (x : ℂ) : List ℂ → ℂ × ℝ
  | [] => (0, 0)
  | a :: rest =>
      rest.foldl (fl_complexHornerRunningStep fp x) (a, ‖a‖ / 2)

/-- Complex Algorithm 5.1's final source bound
`sqrt(2) * gamma_2 * (2*mu - |y|)`. -/
noncomputable def fl_complexHornerRunningBound
    (fp : FPModel) (x : ℂ) (coeffsDesc : List ℂ) : ℝ :=
  let state := fl_complexHornerRunningState fp x coeffsDesc
  complexHornerRunningRadius fp * (2 * state.2 - ‖state.1‖)

lemma fl_complexHornerRunningFold_fst_eq (fp : FPModel) (x : ℂ) :
    ∀ (rest : List ℂ) (y : ℂ) (mu : ℝ),
      (rest.foldl (fl_complexHornerRunningStep fp x) (y, mu)).1 =
        rest.foldl (fl_complexHornerStep fp x) y := by
  intro rest
  induction rest with
  | nil => intro y mu; rfl
  | cons a rest ih =>
      intro y mu
      simp [List.foldl, fl_complexHornerRunningStep, ih]

/-- The first component of the running state is the actual rounded complex
Horner execution. -/
theorem fl_complexHornerRunningState_fst_eq_fl_complexHornerDesc
    (fp : FPModel) (x : ℂ) (coeffsDesc : List ℂ) :
    (fl_complexHornerRunningState fp x coeffsDesc).1 =
      fl_complexHornerDesc fp x coeffsDesc := by
  cases coeffsDesc with
  | nil => rfl
  | cons a rest =>
      simpa [fl_complexHornerRunningState, fl_complexHornerDesc]
        using fl_complexHornerRunningFold_fst_eq fp x rest a (‖a‖ / 2)

lemma fl_complexHornerRunningStep_snd_nonneg
    (fp : FPModel) (x a : ℂ) {state : ℂ × ℝ} (hmu : 0 ≤ state.2) :
    0 ≤ (fl_complexHornerRunningStep fp x state a).2 := by
  simp [fl_complexHornerRunningStep]
  exact add_nonneg (mul_nonneg (norm_nonneg x) hmu) (norm_nonneg _)

lemma fl_complexHornerRunningStep_norm_fst_le_two_snd
    (fp : FPModel) (x a : ℂ) {state : ℂ × ℝ} (hmu : 0 ≤ state.2) :
    ‖(fl_complexHornerRunningStep fp x state a).1‖ ≤
      2 * (fl_complexHornerRunningStep fp x state a).2 := by
  simp [fl_complexHornerRunningStep]
  have hterm : 0 ≤ ‖x‖ * state.2 :=
    mul_nonneg (norm_nonneg x) hmu
  have hy : 0 ≤ ‖fl_complexHornerStep fp x state.1 a‖ := norm_nonneg _
  nlinarith

lemma fl_complexHornerRunningFold_snd_nonneg (fp : FPModel) (x : ℂ) :
    ∀ (rest : List ℂ) (state : ℂ × ℝ),
      0 ≤ state.2 →
      0 ≤ (rest.foldl (fl_complexHornerRunningStep fp x) state).2 := by
  intro rest
  induction rest with
  | nil => intro state hmu; simpa using hmu
  | cons a rest ih =>
      intro state hmu
      exact ih (fl_complexHornerRunningStep fp x state a)
        (fl_complexHornerRunningStep_snd_nonneg fp x a hmu)

lemma fl_complexHornerRunningFold_norm_fst_le_two_snd
    (fp : FPModel) (x : ℂ) :
    ∀ (rest : List ℂ) (state : ℂ × ℝ),
      0 ≤ state.2 →
      ‖state.1‖ ≤ 2 * state.2 →
      ‖(rest.foldl (fl_complexHornerRunningStep fp x) state).1‖ ≤
        2 * (rest.foldl (fl_complexHornerRunningStep fp x) state).2 := by
  intro rest
  induction rest with
  | nil => intro state _ hstate; simpa using hstate
  | cons a rest ih =>
      intro state hmu _hstate
      exact ih (fl_complexHornerRunningStep fp x state a)
        (fl_complexHornerRunningStep_snd_nonneg fp x a hmu)
        (fl_complexHornerRunningStep_norm_fst_le_two_snd fp x a hmu)

/-- The final state satisfies the source invariant `|y| <= 2*mu`. -/
theorem fl_complexHornerRunningState_norm_fst_le_two_mu
    (fp : FPModel) (x : ℂ) (coeffsDesc : List ℂ) :
    ‖(fl_complexHornerRunningState fp x coeffsDesc).1‖ ≤
      2 * (fl_complexHornerRunningState fp x coeffsDesc).2 := by
  cases coeffsDesc with
  | nil => simp [fl_complexHornerRunningState]
  | cons a rest =>
      have hinit_mu : 0 ≤ ‖a‖ / 2 := by positivity
      have hinit_norm : ‖a‖ ≤ 2 * (‖a‖ / 2) := by
        have h : (2 : ℝ) * (‖a‖ / 2) = ‖a‖ := by ring
        rw [h]
      simpa [fl_complexHornerRunningState]
        using fl_complexHornerRunningFold_norm_fst_le_two_snd fp x rest
          (a, ‖a‖ / 2) hinit_mu hinit_norm

end NumStability
