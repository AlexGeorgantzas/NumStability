import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Analysis.FloatingPointArithmetic.IeeeSpecialValueOperations.Results
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter05.Section01.Horner.Basic

/-!
# Chapter05 Section02 DerivativeEvaluation SyntheticDivision

Canonical destination for material split out of
`NumStability.Algorithms.Horner` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- Coefficients of the synthetic-division quotient generated while Horner's
method evaluates the current accumulator `y` against the remaining descending
coefficient list. -/
def hornerSyntheticQuotientFold (alpha y : ℝ) : List ℝ → List ℝ
  | [] => []
  | [ _a0 ] => [y]
  | a :: b :: rest =>
      y :: hornerSyntheticQuotientFold alpha (hornerStep alpha y a)
        (b :: rest)

/-- Synthetic-division quotient coefficients for `coeffsDesc`, in descending
order.  If `coeffsDesc` represents `p`, the result represents the quotient
`q` in `p(x) = (x - alpha) q(x) + p(alpha)`. -/
def hornerSyntheticQuotientDesc (alpha : ℝ) : List ℝ → List ℝ
  | [] => []
  | [_a] => []
  | a :: b :: rest => hornerSyntheticQuotientFold alpha a (b :: rest)

lemma hornerSyntheticQuotientFold_length (alpha : ℝ) :
    ∀ (rest : List ℝ) (y : ℝ),
      (hornerSyntheticQuotientFold alpha y rest).length = rest.length := by
  intro rest
  induction rest with
  | nil =>
      intro y
      simp [hornerSyntheticQuotientFold]
  | cons a rest ih =>
      intro y
      cases rest with
      | nil =>
          simp [hornerSyntheticQuotientFold]
      | cons b tail =>
          simpa [hornerSyntheticQuotientFold] using
            ih (hornerStep alpha y a)

lemma hornerSyntheticQuotientFold_spec (alpha x : ℝ) :
    ∀ (rest : List ℝ) (y : ℝ),
      y * x ^ rest.length + polyDesc x rest =
        (x - alpha) *
            polyDesc x (hornerSyntheticQuotientFold alpha y rest) +
          rest.foldl (hornerStep alpha) y := by
  intro rest
  induction rest with
  | nil =>
      intro y
      simp [hornerSyntheticQuotientFold, polyDesc]
  | cons a rest ih =>
      intro y
      cases rest with
      | nil =>
          simp [hornerSyntheticQuotientFold, polyDesc, hornerStep]
          ring
      | cons b tail =>
          have hih := ih (hornerStep alpha y a)
          have hlen :
              (hornerSyntheticQuotientFold alpha (hornerStep alpha y a)
                  (b :: tail)).length = (b :: tail).length :=
            hornerSyntheticQuotientFold_length alpha (b :: tail)
              (hornerStep alpha y a)
          have hlen' :
              (hornerSyntheticQuotientFold alpha (alpha * y + a)
                  (b :: tail)).length = (b :: tail).length := by
            simpa [hornerStep] using hlen
          simp [hornerSyntheticQuotientFold, polyDesc, hornerStep,
            pow_succ] at hih ⊢
          calc
            y * (x ^ tail.length * x * x) +
                (a * (x ^ tail.length * x) +
                  (b * x ^ tail.length + polyDesc x tail)) =
              (x - alpha) * (y * (x ^ tail.length * x)) +
                ((alpha * y + a) * (x ^ tail.length * x) +
                  (b * x ^ tail.length + polyDesc x tail)) := by
                ring
            _ =
              (x - alpha) * (y * (x ^ tail.length * x)) +
                ((x - alpha) *
                    polyDesc x
                      (hornerSyntheticQuotientFold alpha
                        (alpha * y + a) (b :: tail)) +
                  List.foldl (hornerStep alpha)
                    (alpha * (alpha * y + a) + b) tail) := by
                rw [hih]
            _ =
              (x - alpha) *
                  (y * (x ^ tail.length * x) +
                    polyDesc x
                      (hornerSyntheticQuotientFold alpha
                        (alpha * y + a) (b :: tail))) +
                List.foldl (hornerStep alpha)
                  (alpha * (alpha * y + a) + b) tail := by
                ring
            _ =
              (x - alpha) *
                  (y * x ^
                      (hornerSyntheticQuotientFold alpha
                        (alpha * y + a) (b :: tail)).length +
                    polyDesc x
                      (hornerSyntheticQuotientFold alpha
                        (alpha * y + a) (b :: tail))) +
                List.foldl (hornerStep alpha)
                  (alpha * (alpha * y + a) + b) tail := by
                rw [hlen']
                simp [pow_succ]

/-- Horner's method implements synthetic division:
`p(x) = (x - alpha) q(x) + p(alpha)`. -/
theorem hornerSyntheticDivisionDesc_spec
    (alpha x : ℝ) (coeffsDesc : List ℝ) :
    polyDesc x coeffsDesc =
      (x - alpha) * polyDesc x
          (hornerSyntheticQuotientDesc alpha coeffsDesc) +
        hornerDesc alpha coeffsDesc := by
  cases coeffsDesc with
  | nil =>
      simp [polyDesc, hornerSyntheticQuotientDesc, hornerDesc]
  | cons a rest =>
      cases rest with
      | nil =>
          simp [polyDesc, hornerSyntheticQuotientDesc, hornerDesc]
      | cons b tail =>
          simpa [polyDesc, hornerSyntheticQuotientDesc, hornerDesc]
            using hornerSyntheticQuotientFold_spec alpha x (b :: tail) a

/-- Rounded synthetic-division quotient coefficients generated by the value
component of Algorithm 5.2 while it walks over the remaining descending
coefficients. -/
noncomputable def fl_hornerSyntheticQuotientFold
    (fp : FPModel) (x y : ℝ) : List ℝ → List ℝ
  | [] => []
  | [_a0] => [y]
  | a :: b :: rest =>
      y :: fl_hornerSyntheticQuotientFold fp x
        (fl_hornerStep fp x y a) (b :: rest)

/-- Rounded synthetic-division quotient coefficients for `coeffsDesc`, in
descending order.  These are the computed analogues of
`hornerSyntheticQuotientDesc`. -/
noncomputable def fl_hornerSyntheticQuotientDesc
    (fp : FPModel) (x : ℝ) : List ℝ → List ℝ
  | [] => []
  | [_a] => []
  | a :: b :: rest => fl_hornerSyntheticQuotientFold fp x a (b :: rest)

lemma fl_hornerSyntheticQuotientFold_length
    (fp : FPModel) (x : ℝ) :
    ∀ (rest : List ℝ) (y : ℝ),
      (fl_hornerSyntheticQuotientFold fp x y rest).length =
        rest.length := by
  intro rest
  induction rest with
  | nil =>
      intro y
      simp [fl_hornerSyntheticQuotientFold]
  | cons a rest ih =>
      intro y
      cases rest with
      | nil =>
          simp [fl_hornerSyntheticQuotientFold]
      | cons b tail =>
          simpa [fl_hornerSyntheticQuotientFold] using
            ih (fl_hornerStep fp x y a)

/-- The computed synthetic-division quotient has one fewer coefficient than
the original polynomial coefficient list. -/
theorem fl_hornerSyntheticQuotientDesc_length
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ) :
    (fl_hornerSyntheticQuotientDesc fp x coeffsDesc).length =
      coeffsDesc.length - 1 := by
  cases coeffsDesc with
  | nil =>
      simp [fl_hornerSyntheticQuotientDesc]
  | cons a rest =>
      cases rest with
      | nil =>
          simp [fl_hornerSyntheticQuotientDesc]
      | cons b tail =>
          simpa [fl_hornerSyntheticQuotientDesc] using
            fl_hornerSyntheticQuotientFold_length fp x (b :: tail) a

/-- Source-shaped version of the computed-quotient evaluation majorant.  It
replaces rounded accumulators by exact accumulators plus an explicit propagated
error bound, which is the next bridge toward the first-order (5.7) display. -/
noncomputable def fl_hornerSyntheticQuotientEvalForwardSourceMajorant
    (fp : FPModel) (x : ℝ) : List ℝ → ℝ → ℝ → ℝ
  | [], _y, _eps => 0
  | [_a0], _y, eps => eps
  | a :: b :: rest, y, eps =>
      eps * |x| ^ (b :: rest).length +
        fl_hornerSyntheticQuotientEvalForwardSourceMajorant fp x (b :: rest)
          (hornerStep x y a)
          (fp.u * ((2 + fp.u) * (|x| * (|y| + eps)) + |a|) +
            |x| * eps)

/-- Whole-polynomial specialization of the source-shaped computed-quotient
majorant, starting from the shared leading coefficient and zero accumulated
error. -/
noncomputable def fl_hornerSyntheticQuotientDescEvalForwardSourceMajorant
    (fp : FPModel) (x : ℝ) : List ℝ → ℝ
  | [] => 0
  | [_a] => 0
  | a :: b :: rest =>
      fl_hornerSyntheticQuotientEvalForwardSourceMajorant fp x
        (b :: rest) a 0

lemma fl_hornerSyntheticQuotientEvalForwardSourceMajorant_nonneg
    (fp : FPModel) (x : ℝ) :
    ∀ (rest : List ℝ) (y eps : ℝ),
      0 ≤ eps →
      0 ≤ fl_hornerSyntheticQuotientEvalForwardSourceMajorant fp x rest
        y eps := by
  intro rest
  induction rest with
  | nil =>
      intro y eps _heps
      simp [fl_hornerSyntheticQuotientEvalForwardSourceMajorant]
  | cons a rest ih =>
      intro y eps heps
      cases rest with
      | nil =>
          simpa [fl_hornerSyntheticQuotientEvalForwardSourceMajorant] using
            heps
      | cons b tail =>
          have hcoef : 0 ≤ 2 + fp.u := by nlinarith [fp.u_nonneg]
          have hy_eps : 0 ≤ |y| + eps :=
            add_nonneg (abs_nonneg y) heps
          have hinside :
              0 ≤ (2 + fp.u) * (|x| * (|y| + eps)) + |a| := by
            exact add_nonneg
              (mul_nonneg hcoef
                (mul_nonneg (abs_nonneg x) hy_eps))
              (abs_nonneg a)
          have hepsNext :
              0 ≤ fp.u *
                    ((2 + fp.u) * (|x| * (|y| + eps)) + |a|) +
                  |x| * eps := by
            exact add_nonneg
              (mul_nonneg fp.u_nonneg hinside)
              (mul_nonneg (abs_nonneg x) heps)
          have hhead :
              0 ≤ eps * |x| ^ (b :: tail).length :=
            mul_nonneg heps (pow_nonneg (abs_nonneg x) _)
          have htail :=
            ih (hornerStep x y a)
              (fp.u * ((2 + fp.u) * (|x| * (|y| + eps)) + |a|) +
                |x| * eps)
              hepsNext
          simpa [fl_hornerSyntheticQuotientEvalForwardSourceMajorant]
            using add_nonneg hhead htail

theorem fl_hornerSyntheticQuotientDescEvalForwardSourceMajorant_nonneg
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ) :
    0 ≤ fl_hornerSyntheticQuotientDescEvalForwardSourceMajorant fp x
      coeffsDesc := by
  cases coeffsDesc with
  | nil =>
      simp [fl_hornerSyntheticQuotientDescEvalForwardSourceMajorant]
  | cons a rest =>
      cases rest with
      | nil =>
          simp [fl_hornerSyntheticQuotientDescEvalForwardSourceMajorant]
      | cons b tail =>
          simpa [fl_hornerSyntheticQuotientDescEvalForwardSourceMajorant]
            using
              fl_hornerSyntheticQuotientEvalForwardSourceMajorant_nonneg
                fp x (b :: tail) a 0 (by norm_num)

lemma fl_hornerSyntheticQuotientEvalForwardSourceMajorant_eq_zero_of_u_eq_zero_of_eps_eq_zero
    (fp : FPModel) (x : ℝ) :
    ∀ (rest : List ℝ) (y eps : ℝ),
      fp.u = 0 →
      eps = 0 →
      fl_hornerSyntheticQuotientEvalForwardSourceMajorant fp x rest
        y eps = 0 := by
  intro rest
  induction rest with
  | nil =>
      intro y eps _hu _heps
      simp [fl_hornerSyntheticQuotientEvalForwardSourceMajorant]
  | cons a rest ih =>
      intro y eps hu heps
      cases rest with
      | nil =>
          simp [fl_hornerSyntheticQuotientEvalForwardSourceMajorant, heps]
      | cons b tail =>
          simpa [fl_hornerSyntheticQuotientEvalForwardSourceMajorant,
            hu, heps] using
            ih (hornerStep x y a) 0 hu rfl

theorem fl_hornerSyntheticQuotientDescEvalForwardSourceMajorant_eq_zero_of_u_eq_zero
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ) (hu : fp.u = 0) :
    fl_hornerSyntheticQuotientDescEvalForwardSourceMajorant fp x coeffsDesc =
      0 := by
  cases coeffsDesc with
  | nil =>
      simp [fl_hornerSyntheticQuotientDescEvalForwardSourceMajorant]
  | cons a rest =>
      cases rest with
      | nil =>
          simp [fl_hornerSyntheticQuotientDescEvalForwardSourceMajorant]
      | cons b tail =>
          simpa [fl_hornerSyntheticQuotientDescEvalForwardSourceMajorant]
            using
              fl_hornerSyntheticQuotientEvalForwardSourceMajorant_eq_zero_of_u_eq_zero_of_eps_eq_zero
                fp x (b :: tail) a 0 hu rfl

/-- A finite, list-level forward majorant for the error in evaluating the
computed synthetic-division quotient against the exact one.  The argument
`eps` is a bound for the current value-accumulator error. -/
noncomputable def fl_hornerSyntheticQuotientEvalForwardMajorant
    (fp : FPModel) (x : ℝ) : List ℝ → ℝ → ℝ → ℝ → ℝ
  | [], _yhat, _y, _eps => 0
  | [_a0], _yhat, _y, eps => eps
  | a :: b :: rest, yhat, y, eps =>
      eps * |x| ^ (b :: rest).length +
        fl_hornerSyntheticQuotientEvalForwardMajorant fp x (b :: rest)
          (fl_hornerStep fp x yhat a)
          (hornerStep x y a)
          (fl_hornerStepForwardErrorBudget fp x yhat a + |x| * eps)

/-- The whole-polynomial specialization of
`fl_hornerSyntheticQuotientEvalForwardMajorant`, starting from equal exact and
rounded leading accumulators. -/
noncomputable def fl_hornerSyntheticQuotientDescEvalForwardMajorant
    (fp : FPModel) (x : ℝ) : List ℝ → ℝ
  | [] => 0
  | [_a] => 0
  | a :: b :: rest =>
      fl_hornerSyntheticQuotientEvalForwardMajorant fp x (b :: rest) a a 0

/-- The rounded-data quotient-evaluation budget is dominated by the
source-shaped budget using the exact accumulator and an explicit error bound. -/
theorem fl_hornerSyntheticQuotientEvalForwardMajorant_le_source_majorant
    (fp : FPModel) (x : ℝ) :
    ∀ (rest : List ℝ) (yhat y eps epsBound : ℝ),
      0 ≤ eps →
      |yhat - y| ≤ eps →
      eps ≤ epsBound →
      fl_hornerSyntheticQuotientEvalForwardMajorant fp x rest
        yhat y eps ≤
        fl_hornerSyntheticQuotientEvalForwardSourceMajorant fp x rest
          y epsBound := by
  intro rest
  induction rest with
  | nil =>
      intro yhat y eps epsBound _heps _herr _heps_le
      simp [fl_hornerSyntheticQuotientEvalForwardMajorant,
        fl_hornerSyntheticQuotientEvalForwardSourceMajorant]
  | cons a rest ih =>
      intro yhat y eps epsBound heps herr heps_le
      cases rest with
      | nil =>
          simpa [fl_hornerSyntheticQuotientEvalForwardMajorant,
            fl_hornerSyntheticQuotientEvalForwardSourceMajorant]
            using heps_le
      | cons b tail =>
          let epsNext :=
            fl_hornerStepForwardErrorBudget fp x yhat a + |x| * eps
          let epsBoundNext :=
            fp.u * ((2 + fp.u) * (|x| * (|y| + epsBound)) + |a|) +
              |x| * epsBound
          have hepsBound_nonneg : 0 ≤ epsBound :=
            le_trans heps heps_le
          have hepsNext_nonneg : 0 ≤ epsNext := by
            exact add_nonneg
              (fl_hornerStepForwardErrorBudget_nonneg fp x yhat a)
              (mul_nonneg (abs_nonneg x) heps)
          have herrNext :
              |fl_hornerStep fp x yhat a - hornerStep x y a| ≤
                epsNext := by
            have hlocal :
                |fl_hornerStep fp x yhat a - hornerStep x yhat a| ≤
                  fl_hornerStepForwardErrorBudget fp x yhat a := by
              simpa [fl_hornerStepForwardErrorBudget]
                using fl_hornerStep_forward_local_error_bound fp x yhat a
            have hexact :
                |hornerStep x yhat a - hornerStep x y a| ≤
                  |x| * eps := by
              have hdiff :
                  hornerStep x yhat a - hornerStep x y a =
                    x * (yhat - y) := by
                unfold hornerStep
                ring
              rw [hdiff, abs_mul]
              exact mul_le_mul_of_nonneg_left herr (abs_nonneg x)
            have htri :
                |fl_hornerStep fp x yhat a - hornerStep x y a| ≤
                  |fl_hornerStep fp x yhat a - hornerStep x yhat a| +
                    |hornerStep x yhat a - hornerStep x y a| := by
              have hsplit :
                  fl_hornerStep fp x yhat a - hornerStep x y a =
                    (fl_hornerStep fp x yhat a -
                      hornerStep x yhat a) +
                    (hornerStep x yhat a - hornerStep x y a) := by
                ring
              rw [hsplit]
              exact abs_add_le _ _
            exact le_trans htri (by
              dsimp [epsNext]
              exact add_le_add hlocal hexact)
          have hlocalBound :
              fl_hornerStepForwardErrorBudget fp x yhat a ≤
                fp.u *
                  ((2 + fp.u) * (|x| * (|y| + epsBound)) + |a|) := by
            exact
              fl_hornerStepForwardErrorBudget_le_exact_abs_plus_error
                fp x yhat y a epsBound hepsBound_nonneg
                (le_trans herr heps_le)
          have heps_x_le :
              |x| * eps ≤ |x| * epsBound :=
            mul_le_mul_of_nonneg_left heps_le (abs_nonneg x)
          have hepsNext_le : epsNext ≤ epsBoundNext := by
            dsimp [epsNext, epsBoundNext]
            exact add_le_add hlocalBound heps_x_le
          have htail :=
            ih (fl_hornerStep fp x yhat a) (hornerStep x y a)
              epsNext epsBoundNext hepsNext_nonneg herrNext hepsNext_le
          have hpow_nonneg :
              0 ≤ |x| ^ (b :: tail).length :=
            pow_nonneg (abs_nonneg x) _
          have hhead :
              eps * |x| ^ (b :: tail).length ≤
                epsBound * |x| ^ (b :: tail).length :=
            mul_le_mul_of_nonneg_right heps_le hpow_nonneg
          have hcombine :=
            add_le_add hhead htail
          simpa [fl_hornerSyntheticQuotientEvalForwardMajorant,
            fl_hornerSyntheticQuotientEvalForwardSourceMajorant,
            epsNext, epsBoundNext] using hcombine

theorem fl_hornerSyntheticQuotientDescEvalForwardMajorant_le_source_majorant
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ) :
    fl_hornerSyntheticQuotientDescEvalForwardMajorant fp x coeffsDesc ≤
      fl_hornerSyntheticQuotientDescEvalForwardSourceMajorant fp x
        coeffsDesc := by
  cases coeffsDesc with
  | nil =>
      simp [fl_hornerSyntheticQuotientDescEvalForwardMajorant,
        fl_hornerSyntheticQuotientDescEvalForwardSourceMajorant]
  | cons a rest =>
      cases rest with
      | nil =>
          simp [fl_hornerSyntheticQuotientDescEvalForwardMajorant,
            fl_hornerSyntheticQuotientDescEvalForwardSourceMajorant]
      | cons b tail =>
          simpa [fl_hornerSyntheticQuotientDescEvalForwardMajorant,
            fl_hornerSyntheticQuotientDescEvalForwardSourceMajorant]
            using
              fl_hornerSyntheticQuotientEvalForwardMajorant_le_source_majorant
                fp x (b :: tail) a a 0 0 (by norm_num) (by simp)
                (by norm_num)

lemma fl_hornerSyntheticQuotientEvalForwardMajorant_nonneg
    (fp : FPModel) (x : ℝ) :
    ∀ (rest : List ℝ) (yhat y eps : ℝ),
      0 ≤ eps →
      0 ≤ fl_hornerSyntheticQuotientEvalForwardMajorant fp x rest
        yhat y eps := by
  intro rest
  induction rest with
  | nil =>
      intro yhat y eps _heps
      simp [fl_hornerSyntheticQuotientEvalForwardMajorant]
  | cons a rest ih =>
      intro yhat y eps heps
      cases rest with
      | nil =>
          simpa [fl_hornerSyntheticQuotientEvalForwardMajorant] using heps
      | cons b tail =>
          have hnext :
              0 ≤ fl_hornerStepForwardErrorBudget fp x yhat a +
                  |x| * eps := by
            exact add_nonneg
              (fl_hornerStepForwardErrorBudget_nonneg fp x yhat a)
              (mul_nonneg (abs_nonneg x) heps)
          have hhead :
              0 ≤ eps * |x| ^ (b :: tail).length :=
            mul_nonneg heps (pow_nonneg (abs_nonneg x) _)
          have htail :=
            ih (fl_hornerStep fp x yhat a) (hornerStep x y a)
              (fl_hornerStepForwardErrorBudget fp x yhat a + |x| * eps)
              hnext
          simpa [fl_hornerSyntheticQuotientEvalForwardMajorant]
            using add_nonneg hhead htail

theorem fl_hornerSyntheticQuotientDescEvalForwardMajorant_nonneg
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ) :
    0 ≤ fl_hornerSyntheticQuotientDescEvalForwardMajorant fp x
      coeffsDesc := by
  cases coeffsDesc with
  | nil =>
      simp [fl_hornerSyntheticQuotientDescEvalForwardMajorant]
  | cons a rest =>
      cases rest with
      | nil =>
          simp [fl_hornerSyntheticQuotientDescEvalForwardMajorant]
      | cons b tail =>
          simpa [fl_hornerSyntheticQuotientDescEvalForwardMajorant] using
            fl_hornerSyntheticQuotientEvalForwardMajorant_nonneg fp x
              (b :: tail) a a 0 (by norm_num)

lemma fl_hornerSyntheticQuotientFold_abs_le_exact_abs_plus_eval_majorant
    (fp : FPModel) (x : ℝ) :
    ∀ (rest : List ℝ) (yhat y eps : ℝ),
      0 ≤ eps →
      |yhat - y| ≤ eps →
      polyDescAbs x (fl_hornerSyntheticQuotientFold fp x yhat rest) ≤
        polyDescAbs x (hornerSyntheticQuotientFold x y rest) +
          fl_hornerSyntheticQuotientEvalForwardMajorant fp x rest
            yhat y eps := by
  intro rest
  induction rest with
  | nil =>
      intro yhat y eps _heps _herr
      simp [fl_hornerSyntheticQuotientFold,
        hornerSyntheticQuotientFold,
        fl_hornerSyntheticQuotientEvalForwardMajorant, polyDescAbs]
  | cons a rest ih =>
      intro yhat y eps heps herr
      cases rest with
      | nil =>
          have hyabs : |yhat| ≤ |y| + eps := by
            have htri : |yhat| ≤ |y| + |yhat - y| := by
              calc
                |yhat| = |y + (yhat - y)| := by
                  congr 1
                  ring
                _ ≤ |y| + |yhat - y| := abs_add_le _ _
            linarith
          simpa [fl_hornerSyntheticQuotientFold,
            hornerSyntheticQuotientFold,
            fl_hornerSyntheticQuotientEvalForwardMajorant, polyDescAbs]
            using hyabs
      | cons b tail =>
          let epsNext :=
            fl_hornerStepForwardErrorBudget fp x yhat a + |x| * eps
          have hepsNext : 0 ≤ epsNext := by
            exact add_nonneg
              (fl_hornerStepForwardErrorBudget_nonneg fp x yhat a)
              (mul_nonneg (abs_nonneg x) heps)
          have herrNext :
              |fl_hornerStep fp x yhat a - hornerStep x y a| ≤
                epsNext := by
            have hlocal :
                |fl_hornerStep fp x yhat a - hornerStep x yhat a| ≤
                  fl_hornerStepForwardErrorBudget fp x yhat a := by
              simpa [fl_hornerStepForwardErrorBudget]
                using fl_hornerStep_forward_local_error_bound fp x yhat a
            have hexact :
                |hornerStep x yhat a - hornerStep x y a| ≤
                  |x| * eps := by
              have hdiff :
                  hornerStep x yhat a - hornerStep x y a =
                    x * (yhat - y) := by
                unfold hornerStep
                ring
              rw [hdiff, abs_mul]
              exact mul_le_mul_of_nonneg_left herr (abs_nonneg x)
            have htri :
                |fl_hornerStep fp x yhat a - hornerStep x y a| ≤
                  |fl_hornerStep fp x yhat a - hornerStep x yhat a| +
                    |hornerStep x yhat a - hornerStep x y a| := by
              have hsplit :
                  fl_hornerStep fp x yhat a - hornerStep x y a =
                    (fl_hornerStep fp x yhat a - hornerStep x yhat a) +
                      (hornerStep x yhat a - hornerStep x y a) := by
                ring
              rw [hsplit]
              exact abs_add_le _ _
            simpa [epsNext] using
              le_trans htri (add_le_add hlocal hexact)
          have htail :=
            ih (fl_hornerStep fp x yhat a) (hornerStep x y a)
              epsNext hepsNext herrNext
          have hlenFl :
              (fl_hornerSyntheticQuotientFold fp x
                  (fl_hornerStep fp x yhat a) (b :: tail)).length =
                (b :: tail).length :=
            fl_hornerSyntheticQuotientFold_length fp x (b :: tail)
              (fl_hornerStep fp x yhat a)
          have hlenExact :
              (hornerSyntheticQuotientFold x (hornerStep x y a)
                  (b :: tail)).length = (b :: tail).length :=
            hornerSyntheticQuotientFold_length x (b :: tail)
              (hornerStep x y a)
          have hpow_nonneg :
              0 ≤ |x| ^ (b :: tail).length :=
            pow_nonneg (abs_nonneg x) _
          have hyabs : |yhat| ≤ |y| + eps := by
            have htri : |yhat| ≤ |y| + |yhat - y| := by
              calc
                |yhat| = |y + (yhat - y)| := by
                  congr 1
                  ring
                _ ≤ |y| + |yhat - y| := abs_add_le _ _
            linarith
          have hhead :
              |yhat| * |x| ^ (b :: tail).length ≤
                |y| * |x| ^ (b :: tail).length +
                  eps * |x| ^ (b :: tail).length := by
            calc
              |yhat| * |x| ^ (b :: tail).length ≤
                  (|y| + eps) * |x| ^ (b :: tail).length :=
                mul_le_mul_of_nonneg_right hyabs hpow_nonneg
              _ = |y| * |x| ^ (b :: tail).length +
                  eps * |x| ^ (b :: tail).length := by ring
          have hcombine :
              |yhat| * |x| ^ (b :: tail).length +
                  polyDescAbs x
                    (fl_hornerSyntheticQuotientFold fp x
                      (fl_hornerStep fp x yhat a) (b :: tail)) ≤
                |y| * |x| ^ (b :: tail).length +
                  polyDescAbs x
                    (hornerSyntheticQuotientFold x
                      (hornerStep x y a) (b :: tail)) +
                  (eps * |x| ^ (b :: tail).length +
                    fl_hornerSyntheticQuotientEvalForwardMajorant fp x
                      (b :: tail) (fl_hornerStep fp x yhat a)
                      (hornerStep x y a) epsNext) := by
            nlinarith [hhead, htail]
          simpa [fl_hornerSyntheticQuotientFold,
            hornerSyntheticQuotientFold, polyDescAbs, hlenFl, hlenExact,
            fl_hornerSyntheticQuotientEvalForwardMajorant, epsNext]
            using hcombine

theorem fl_hornerSyntheticQuotientDesc_abs_le_exact_abs_plus_eval_majorant
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ) :
    polyDescAbs x (fl_hornerSyntheticQuotientDesc fp x coeffsDesc) ≤
      polyDescAbs x (hornerSyntheticQuotientDesc x coeffsDesc) +
        fl_hornerSyntheticQuotientDescEvalForwardMajorant fp x coeffsDesc := by
  cases coeffsDesc with
  | nil =>
      simp [fl_hornerSyntheticQuotientDesc,
        hornerSyntheticQuotientDesc, polyDescAbs,
        fl_hornerSyntheticQuotientDescEvalForwardMajorant]
  | cons a rest =>
      cases rest with
      | nil =>
          simp [fl_hornerSyntheticQuotientDesc,
            hornerSyntheticQuotientDesc, polyDescAbs,
            fl_hornerSyntheticQuotientDescEvalForwardMajorant]
      | cons b tail =>
          have h :=
            fl_hornerSyntheticQuotientFold_abs_le_exact_abs_plus_eval_majorant
              fp x (b :: tail) a a 0 (by norm_num) (by simp)
          simpa [fl_hornerSyntheticQuotientDesc,
            hornerSyntheticQuotientDesc,
            fl_hornerSyntheticQuotientDescEvalForwardMajorant] using h

/-- List-level forward bound for the computed synthetic-division quotient.

This is the scalar/evaluation form of the remaining (5.5) quotient
perturbation: it bounds the difference between evaluating the rounded quotient
stream and evaluating the exact synthetic-division quotient stream. -/
theorem fl_hornerSyntheticQuotientFold_eval_forward_error_bound
    (fp : FPModel) (x : ℝ) :
    ∀ (rest : List ℝ) (yhat y eps : ℝ),
      0 ≤ eps →
      |yhat - y| ≤ eps →
      |polyDesc x (fl_hornerSyntheticQuotientFold fp x yhat rest) -
          polyDesc x (hornerSyntheticQuotientFold x y rest)| ≤
        fl_hornerSyntheticQuotientEvalForwardMajorant fp x rest
          yhat y eps := by
  intro rest
  induction rest with
  | nil =>
      intro yhat y eps _heps _herr
      simp [fl_hornerSyntheticQuotientFold,
        hornerSyntheticQuotientFold,
        fl_hornerSyntheticQuotientEvalForwardMajorant, polyDesc]
  | cons a rest ih =>
      intro yhat y eps heps herr
      cases rest with
      | nil =>
          simpa [fl_hornerSyntheticQuotientFold,
            hornerSyntheticQuotientFold,
            fl_hornerSyntheticQuotientEvalForwardMajorant, polyDesc]
            using herr
      | cons b tail =>
          let epsNext :=
            fl_hornerStepForwardErrorBudget fp x yhat a + |x| * eps
          have hepsNext : 0 ≤ epsNext := by
            exact add_nonneg
              (fl_hornerStepForwardErrorBudget_nonneg fp x yhat a)
              (mul_nonneg (abs_nonneg x) heps)
          have herrNext :
              |fl_hornerStep fp x yhat a - hornerStep x y a| ≤
                epsNext := by
            simpa [epsNext] using
              fl_hornerStep_error_bound_of_accumulator_error
                fp x yhat y a eps herr
          have htail :=
            ih (fl_hornerStep fp x yhat a) (hornerStep x y a)
              epsNext hepsNext herrNext
          have hlenFl :
              (fl_hornerSyntheticQuotientFold fp x
                  (fl_hornerStep fp x yhat a) (b :: tail)).length =
                (b :: tail).length :=
            fl_hornerSyntheticQuotientFold_length fp x (b :: tail)
              (fl_hornerStep fp x yhat a)
          have hlenExact :
              (hornerSyntheticQuotientFold x (hornerStep x y a)
                  (b :: tail)).length = (b :: tail).length :=
            hornerSyntheticQuotientFold_length x (b :: tail)
              (hornerStep x y a)
          have hsplit :
              polyDesc x
                  (fl_hornerSyntheticQuotientFold fp x yhat
                    (a :: b :: tail)) -
                polyDesc x
                  (hornerSyntheticQuotientFold x y
                    (a :: b :: tail)) =
              (yhat - y) * x ^ (b :: tail).length +
                (polyDesc x
                    (fl_hornerSyntheticQuotientFold fp x
                      (fl_hornerStep fp x yhat a) (b :: tail)) -
                  polyDesc x
                    (hornerSyntheticQuotientFold x
                      (hornerStep x y a) (b :: tail))) := by
            simp [fl_hornerSyntheticQuotientFold,
              hornerSyntheticQuotientFold, polyDesc, hlenFl, hlenExact]
            ring
          have hhead :
              |(yhat - y) * x ^ (b :: tail).length| ≤
                eps * |x| ^ (b :: tail).length := by
            rw [abs_mul, abs_pow]
            exact mul_le_mul_of_nonneg_right herr
              (pow_nonneg (abs_nonneg x) _)
          have htri :
              |(yhat - y) * x ^ (b :: tail).length +
                  (polyDesc x
                    (fl_hornerSyntheticQuotientFold fp x
                      (fl_hornerStep fp x yhat a) (b :: tail)) -
                  polyDesc x
                    (hornerSyntheticQuotientFold x
                      (hornerStep x y a) (b :: tail)))| ≤
                |(yhat - y) * x ^ (b :: tail).length| +
                  |polyDesc x
                    (fl_hornerSyntheticQuotientFold fp x
                      (fl_hornerStep fp x yhat a) (b :: tail)) -
                  polyDesc x
                    (hornerSyntheticQuotientFold x
                      (hornerStep x y a) (b :: tail))| :=
            abs_add_le _ _
          rw [hsplit]
          exact le_trans htri
            (by
              simpa [fl_hornerSyntheticQuotientEvalForwardMajorant,
                epsNext] using add_le_add hhead htail)

/-- Forward bound for the computed synthetic-division quotient attached to a
whole coefficient list. -/
theorem fl_hornerSyntheticQuotientDesc_eval_forward_error_bound
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ) :
    |polyDesc x (fl_hornerSyntheticQuotientDesc fp x coeffsDesc) -
        polyDesc x (hornerSyntheticQuotientDesc x coeffsDesc)| ≤
      fl_hornerSyntheticQuotientDescEvalForwardMajorant fp x coeffsDesc := by
  cases coeffsDesc with
  | nil =>
      simp [fl_hornerSyntheticQuotientDesc,
        hornerSyntheticQuotientDesc, polyDesc,
        fl_hornerSyntheticQuotientDescEvalForwardMajorant]
  | cons a rest =>
      cases rest with
      | nil =>
          simp [fl_hornerSyntheticQuotientDesc,
            hornerSyntheticQuotientDesc, polyDesc,
            fl_hornerSyntheticQuotientDescEvalForwardMajorant]
      | cons b tail =>
          have h :=
            fl_hornerSyntheticQuotientFold_eval_forward_error_bound
              fp x (b :: tail) a a 0 (by norm_num) (by simp)
          simpa [fl_hornerSyntheticQuotientDesc,
            hornerSyntheticQuotientDesc,
            fl_hornerSyntheticQuotientDescEvalForwardMajorant] using h

lemma fl_hornerSyntheticQuotientFold_exactWithUnitRoundoff
    (u0 : ℝ) (hu0 : 0 ≤ u0) (x : ℝ) :
    ∀ (rest : List ℝ) (y : ℝ),
      fl_hornerSyntheticQuotientFold
          (FPModel.exactWithUnitRoundoff u0 hu0) x y rest =
        hornerSyntheticQuotientFold x y rest := by
  intro rest
  induction rest with
  | nil =>
      intro y
      rfl
  | cons a rest ih =>
      intro y
      cases rest with
      | nil =>
          rfl
      | cons b tail =>
          simpa [fl_hornerSyntheticQuotientFold,
            hornerSyntheticQuotientFold, fl_hornerStep, hornerStep,
            FPModel.exactWithUnitRoundoff] using ih (x * y + a)

/-- Exact arithmetic, packaged as an `FPModel`, produces the exact
synthetic-division quotient stream. -/
theorem fl_hornerSyntheticQuotientDesc_exactWithUnitRoundoff
    (u0 : ℝ) (hu0 : 0 ≤ u0) (x : ℝ) (coeffsDesc : List ℝ) :
    fl_hornerSyntheticQuotientDesc
        (FPModel.exactWithUnitRoundoff u0 hu0) x coeffsDesc =
      hornerSyntheticQuotientDesc x coeffsDesc := by
  cases coeffsDesc with
  | nil =>
      rfl
  | cons a rest =>
      cases rest with
      | nil =>
          rfl
      | cons b tail =>
          simpa [fl_hornerSyntheticQuotientDesc,
            hornerSyntheticQuotientDesc] using
            fl_hornerSyntheticQuotientFold_exactWithUnitRoundoff
              u0 hu0 x (b :: tail) a

end NumStability
