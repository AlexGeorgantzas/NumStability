-- Stability.lean

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Error

namespace NumStability

/-!
# Stability and Condition Number

Following Higham, "Accuracy and Stability of Numerical Algorithms", §1.5–§1.6.

We formalise the key concepts that classify how well an algorithm handles
the unavoidable rounding errors introduced by finite precision arithmetic:
backward error, forward error, mixed stability, numerical stability, and the
condition number of a problem.
-/

-- ============================================================
-- §1.5  Backward and forward error predicates
-- ============================================================

/-- Backward error bound for a computed result `xhat` for scalar problem `f` at input `a`.

    Asserts that there exists a perturbation Δa with |Δa| ≤ ε such that `xhat` is
    the *exact* solution to the perturbed problem `f(a + Δa)`:
      ∃ Δa, |Δa| ≤ ε ∧ f(a + Δa) = xhat

    The vector analog is `backwardErrorBoundedVec`. -/
def backwardErrorBounded (f : ℝ → ℝ) (a xhat ε : ℝ) : Prop :=
  ∃ Δa : ℝ, |Δa| ≤ ε ∧ f (a + Δa) = xhat

/-- Backward error bound for a computed vector result `xhat` for problem
    `f : (Fin n → ℝ) → (Fin m → ℝ)` at input `a`.

    Asserts that there exists a componentwise perturbation Δa with |Δa i| ≤ ε for all i,
    such that `xhat` is the *exact* solution to the perturbed problem `f(a + Δa)`:
      ∃ Δa, (∀ i, |Δa i| ≤ ε) ∧ f(fun i => a i + Δa i) = xhat

    The scalar analog is `backwardErrorBounded`. -/
def backwardErrorBoundedVec (n m : ℕ) (f : (Fin n → ℝ) → (Fin m → ℝ))
    (a : Fin n → ℝ) (xhat : Fin m → ℝ) (ε : ℝ) : Prop :=
  ∃ Δa : Fin n → ℝ, (∀ i, |Δa i| ≤ ε) ∧ f (fun i => a i + Δa i) = xhat

/-- Forward error bound for a scalar computed result `xhat`.

    This names Higham's forward-error viewpoint: the computed answer is close
    to the exact answer `f a` for the original data.  The bound is relative,
    using `relError`; callers should separately enforce `f a ≠ 0` when they
    need the mathematical nonzero-domain convention. -/
noncomputable def forwardErrorBounded (f : ℝ → ℝ) (a xhat ε : ℝ) : Prop :=
  relError xhat (f a) ≤ ε

/-- Normwise forward error bound for vector problems, parameterized by the
chosen norm. -/
noncomputable def forwardErrorBoundedVec (n m : ℕ)
    (norm : (Fin m → ℝ) → ℝ)
    (f : (Fin n → ℝ) → (Fin m → ℝ))
    (a : Fin n → ℝ) (xhat : Fin m → ℝ) (ε : ℝ) : Prop :=
  normwiseRelError m norm xhat (f a) ≤ ε

/-- Normwise backward error for vector problems, parameterized by the chosen
input norm.  This is the normed analogue of `backwardErrorBoundedVec`: the
computed result is exact for `a + Δa`, with `||Δa|| <= ε`. -/
def normwiseBackwardErrorBoundedVec (n m : ℕ)
    (normIn : (Fin n → ℝ) → ℝ)
    (f : (Fin n → ℝ) → (Fin m → ℝ))
    (a : Fin n → ℝ) (xhat : Fin m → ℝ) (ε : ℝ) : Prop :=
  ∃ Δa : Fin n → ℝ, normIn Δa ≤ ε ∧ f (fun i => a i + Δa i) = xhat

/-- Higham §1.5 mixed forward-backward error for scalar problems:
the computed result plus a small output perturbation is the exact result for a
smallly perturbed input. -/
def mixedForwardBackwardErrorBounded (f : ℝ → ℝ) (a xhat εBack εForw : ℝ) :
    Prop :=
  ∃ Δa Δy : ℝ,
    |Δa| ≤ εBack ∧ |Δy| ≤ εForw ∧ xhat + Δy = f (a + Δa)

/-- Vector-valued mixed forward-backward error: the input perturbation is
componentwise bounded and the output perturbation is componentwise bounded. -/
def mixedForwardBackwardErrorBoundedVec (n m : ℕ)
    (f : (Fin n → ℝ) → (Fin m → ℝ))
    (a : Fin n → ℝ) (xhat : Fin m → ℝ) (εBack εForw : ℝ) : Prop :=
  ∃ Δa : Fin n → ℝ, ∃ Δy : Fin m → ℝ,
    (∀ i, |Δa i| ≤ εBack) ∧
    (∀ j, |Δy j| ≤ εForw) ∧
    (fun j => xhat j + Δy j) = f (fun i => a i + Δa i)

/-- A backward-error certificate is a mixed forward-backward certificate with
zero forward perturbation. -/
theorem mixedForwardBackward_of_backward (f : ℝ → ℝ) (a xhat εBack εForw : ℝ)
    (hback : backwardErrorBounded f a xhat εBack) (hforw : 0 ≤ εForw) :
    mixedForwardBackwardErrorBounded f a xhat εBack εForw := by
  obtain ⟨Δa, hΔa, hEq⟩ := hback
  refine ⟨Δa, 0, hΔa, ?_, ?_⟩
  · simpa using hforw
  · simp [hEq]

-- ============================================================
-- §1.5  Backward stability (scalar problems)
-- ============================================================

/-- An algorithm computing `f : ℝ → ℝ` at input `a` is **backward stable**
    if the computed result `xhat` is the exact answer for a slightly perturbed
    input.  The perturbation is required to be no larger than `c * u`:
      ∃ Δa, |Δa| ≤ c * u ∧ f(a + Δa) = xhat

    Typically the constant c depends on the algorithm; u is the unit roundoff. -/
def isBackwardStable (fp : FPModel) (f : ℝ → ℝ) (alg : ℝ → ℝ)
    (c : ℝ) : Prop :=
  ∀ a : ℝ, backwardErrorBounded f a (alg a) (c * fp.u)

-- ============================================================
-- §1.5  Backward stability (vector problems)
-- ============================================================

/-- Backward stability for a vector-to-vector problem `f : (Fin n → ℝ) → (Fin m → ℝ)`.

    The computed output `alg a` is the exact answer for a componentwise-perturbed
    input, with each component perturbed by at most `c * u`. -/
def isVectorBackwardStable (fp : FPModel) (n m : ℕ)
    (f : (Fin n → ℝ) → (Fin m → ℝ))
    (alg : (Fin n → ℝ) → (Fin m → ℝ))
    (c : ℝ) : Prop :=
  ∀ a : Fin n → ℝ, backwardErrorBoundedVec n m f a (alg a) (c * fp.u)

-- ============================================================
-- §1.5  Numerical and forward stability
-- ============================================================

/-- Higham §1.5 numerical stability in mixed forward-backward form.  The
constants multiply the model unit roundoff and are supplied by the concrete
algorithm analysis. -/
def isNumericallyStable (fp : FPModel) (f : ℝ → ℝ) (alg : ℝ → ℝ)
    (cBack cForw : ℝ) : Prop :=
  ∀ a : ℝ,
    mixedForwardBackwardErrorBounded f a (alg a) (cBack * fp.u) (cForw * fp.u)

/-- Vector-valued numerical stability in mixed forward-backward form. -/
def isVectorNumericallyStable (fp : FPModel) (n m : ℕ)
    (f : (Fin n → ℝ) → (Fin m → ℝ))
    (alg : (Fin n → ℝ) → (Fin m → ℝ))
    (cBack cForw : ℝ) : Prop :=
  ∀ a : Fin n → ℝ,
    mixedForwardBackwardErrorBoundedVec n m f a (alg a)
      (cBack * fp.u) (cForw * fp.u)

/-- Higham's forward-stability comparison: `alg` has forward errors bounded by
a constant multiple of a reference algorithm's forward errors.  In Chapter 1
the reference class is a backward-stable method for the same problem. -/
noncomputable def isForwardStableRelativeTo (f : ℝ → ℝ) (alg referenceAlg : ℝ → ℝ)
    (c : ℝ) : Prop :=
  ∀ a : ℝ, relError (alg a) (f a) ≤ c * relError (referenceAlg a) (f a)

/-- Vector version of `isForwardStableRelativeTo`, parameterized by the chosen
output norm. -/
noncomputable def isVectorForwardStableRelativeTo (n m : ℕ)
    (norm : (Fin m → ℝ) → ℝ)
    (f : (Fin n → ℝ) → (Fin m → ℝ))
    (alg referenceAlg : (Fin n → ℝ) → (Fin m → ℝ))
    (c : ℝ) : Prop :=
  ∀ a : Fin n → ℝ,
    normwiseRelError m norm (alg a) (f a) ≤
      c * normwiseRelError m norm (referenceAlg a) (f a)

-- ============================================================
-- §1.5  Relative componentwise backward stability (two-input scalar problems)
-- ============================================================

/-- Relative componentwise backward error bound for a two-input scalar problem
    `f : (Fin n → ℝ) → (Fin n → ℝ) → ℝ`.

    Asserts that there exists a componentwise perturbation Δx with
    |Δx i| ≤ ε * |x i| for all i, such that `xhat` is the *exact* result
    of the unperturbed `f` at the perturbed first input:
      ∃ Δx, (∀ i, |Δx i| ≤ ε * |x i|) ∧ f(fun i => x i + Δx i, y) = xhat

    This is the relative componentwise form of the backward error:
    each component of x is perturbed by at most a ε-fraction of its magnitude,
    matching Higham's condition (3.4) for the inner product. -/
def relBackwardErrorBounded2 (n : ℕ) (f : (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (x y : Fin n → ℝ) (xhat : ℝ) (ε : ℝ) : Prop :=
  ∃ Δx : Fin n → ℝ, (∀ i, |Δx i| ≤ ε * |x i|) ∧ f (fun i => x i + Δx i) y = xhat

/-- An algorithm `alg` computing a two-input scalar problem `f` is
    **relatively componentwise backward stable** with bound ε if, for every
    pair of inputs `(x, y)`, the computed result is the exact answer for a
    first-input perturbation with relative componentwise bound ε:
      ∀ x y, ∃ Δx, (∀ i, |Δx i| ≤ ε * |x i|) ∧ f(x + Δx, y) = alg(x, y)

    Setting ε = γ(n) and `f = inner product` recovers Higham §3.1 (3.4). -/
def isRelComponentwiseBackwardStable (n : ℕ)
    (f : (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (alg : (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (ε : ℝ) : Prop :=
  ∀ x y : Fin n → ℝ, relBackwardErrorBounded2 n f x y (alg x y) ε

-- ============================================================
-- §1.6  Condition number of a scalar problem
-- ============================================================

/-- The condition number of a differentiable scalar problem `f` at input `a`.

    Defined as the relative change in output per unit relative change in input:
      κ(f, a) = |a * f'(a) / f(a)|

    A large condition number means the problem is ill-conditioned: small relative
    changes in input cause large relative changes in output, independently of
    the algorithm used.

    The derivative `f'` must be supplied by the caller (as a function `df`).
    Meaningful only when `f(a) ≠ 0`; the caller must enforce this. -/
noncomputable def condNumber (f df : ℝ → ℝ) (a : ℝ) : ℝ :=
  |a * df a / f a|

/-- A problem `f` is **well-conditioned** at `a` if its condition number is
    at most `κ_max`.  The threshold `κ_max` is problem- and context-dependent;
    typical values are O(1) to O(1/u) where u is the unit roundoff. -/
def isWellConditioned (f df : ℝ → ℝ) (a κ_max : ℝ) : Prop :=
  condNumber f df a ≤ κ_max

/-- Normwise local condition-number bound for a finite-dimensional vector
problem.  The predicate says that every perturbation `Δa` of size at most `ρ`
has relative output change bounded by
`κ * (||Δa||_in / ||a||_in)`.

This is the finite-vector surface for Higham §1.6's statement that, when vector
data or vector outputs are involved, condition numbers are defined with norms
and measure the maximum relative change. -/
noncomputable def normwiseConditionNumberBoundedVec (n m : ℕ)
    (normIn : (Fin n → ℝ) → ℝ) (normOut : (Fin m → ℝ) → ℝ)
    (f : (Fin n → ℝ) → (Fin m → ℝ))
    (a : Fin n → ℝ) (κ ρ : ℝ) : Prop :=
  ∀ Δa : Fin n → ℝ, normIn Δa ≤ ρ →
    normwiseRelError m normOut (f (fun i => a i + Δa i)) (f a) ≤
      κ * (normIn Δa / normIn a)

/-- Source-facing supremum form of the normwise condition number.

The number `κ` is the least upper bound, in the inequality form used by
Higham's local condition-number estimate, for all perturbations with
`||Δa||_in <= ρ`.  This avoids baking in a specific topology or compactness
theorem for arbitrary user-supplied norms; concrete norm/continuity choices can
later prove this predicate by an attainment theorem. -/
noncomputable def normwiseConditionNumberSupremumVec (n m : ℕ)
    (normIn : (Fin n → ℝ) → ℝ) (normOut : (Fin m → ℝ) → ℝ)
    (f : (Fin n → ℝ) → (Fin m → ℝ))
    (a : Fin n → ℝ) (κ ρ : ℝ) : Prop :=
  normwiseConditionNumberBoundedVec n m normIn normOut f a κ ρ ∧
    ∀ κ' : ℝ,
      normwiseConditionNumberBoundedVec n m normIn normOut f a κ' ρ →
        κ ≤ κ'

/-- Attained maximum form of the normwise condition number.  The positive
relative perturbation condition excludes the zero-denominator perturbation when
turning an attained upper bound into a least upper bound. -/
noncomputable def normwiseConditionNumberAttainedVec (n m : ℕ)
    (normIn : (Fin n → ℝ) → ℝ) (normOut : (Fin m → ℝ) → ℝ)
    (f : (Fin n → ℝ) → (Fin m → ℝ))
    (a : Fin n → ℝ) (κ ρ : ℝ) : Prop :=
  ∃ Δa : Fin n → ℝ,
    normIn Δa ≤ ρ ∧
      0 < normIn Δa / normIn a ∧
        normwiseRelError m normOut (f (fun i => a i + Δa i)) (f a) =
          κ * (normIn Δa / normIn a)

theorem normwiseConditionNumberSupremumVec.bounded (n m : ℕ)
    (normIn : (Fin n → ℝ) → ℝ) (normOut : (Fin m → ℝ) → ℝ)
    (f : (Fin n → ℝ) → (Fin m → ℝ))
    (a : Fin n → ℝ) (κ ρ : ℝ)
    (hκ : normwiseConditionNumberSupremumVec n m normIn normOut f a κ ρ) :
    normwiseConditionNumberBoundedVec n m normIn normOut f a κ ρ :=
  hκ.1

theorem normwiseConditionNumberSupremumVec.le_of_bound (n m : ℕ)
    (normIn : (Fin n → ℝ) → ℝ) (normOut : (Fin m → ℝ) → ℝ)
    (f : (Fin n → ℝ) → (Fin m → ℝ))
    (a : Fin n → ℝ) (κ κ' ρ : ℝ)
    (hκ : normwiseConditionNumberSupremumVec n m normIn normOut f a κ ρ)
    (hbound :
      normwiseConditionNumberBoundedVec n m normIn normOut f a κ' ρ) :
    κ ≤ κ' :=
  hκ.2 κ' hbound

/-- If an upper bound is attained at a perturbation with positive relative
size, then it is the source-facing supremum condition number. -/
theorem normwiseConditionNumberSupremumVec_of_attained_bound (n m : ℕ)
    (normIn : (Fin n → ℝ) → ℝ) (normOut : (Fin m → ℝ) → ℝ)
    (f : (Fin n → ℝ) → (Fin m → ℝ))
    (a : Fin n → ℝ) (κ ρ : ℝ)
    (hbound :
      normwiseConditionNumberBoundedVec n m normIn normOut f a κ ρ)
    (hattain :
      normwiseConditionNumberAttainedVec n m normIn normOut f a κ ρ) :
    normwiseConditionNumberSupremumVec n m normIn normOut f a κ ρ := by
  refine ⟨hbound, ?_⟩
  intro κ' hbound'
  rcases hattain with ⟨Δa, hΔa, hrelpos, hattain_eq⟩
  have hκ' := hbound' Δa hΔa
  rw [hattain_eq] at hκ'
  have hdiv :
      κ * (normIn Δa / normIn a) / (normIn Δa / normIn a) ≤
        κ' * (normIn Δa / normIn a) / (normIn Δa / normIn a) :=
    div_le_div_of_nonneg_right hκ' (le_of_lt hrelpos)
  simpa [hrelpos.ne'] using hdiv

-- ============================================================
-- §1.6  Forward error from backward error + condition number
-- ============================================================

/-- **Fundamental theorem of backward error analysis** (Higham §1.6).

    If the computed result `xhat` has absolute backward error at most ε, i.e.,
      ∃ Δa, |Δa| ≤ ε ∧ f(a + Δa) = xhat,
    and `f` satisfies the linearisation bound
      ∀ Δa, |Δa| ≤ ε → |f(a + Δa) - f(a)| ≤ |df(a)| · |Δa|,
    then the relative forward error satisfies:
      relError xhat (f a) ≤ condNumber f df a · (ε / |a|).

    The linearisation hypothesis `hlin` encodes the first-order sensitivity of
    `f`: it holds exactly when `f` is linear, and (to first order in ε) for any
    smooth `f` via Taylor's theorem.

    Proof: let Δa witness the backward error.  Then
      |f(a+Δa) - f(a)| ≤ |df(a)| · |Δa| ≤ |df(a)| · ε.
    Dividing by |f(a)| and noting condNumber f df a · (ε/|a|) = |df(a)|·ε/|f(a)|
    (since condNumber = |a·df(a)/f(a)|) gives the result. -/
lemma forward_from_backward (f df : ℝ → ℝ) (a ε xhat : ℝ)
    (ha  : a ≠ 0)
    (hf  : f a ≠ 0)
    (hback : backwardErrorBounded f a xhat ε)
    (hlin  : ∀ Δa : ℝ, |Δa| ≤ ε → |f (a + Δa) - f a| ≤ |df a| * |Δa|) :
    relError xhat (f a) ≤ condNumber f df a * (ε / |a|) := by
  unfold relError condNumber
  obtain ⟨Δa, hΔa, hfΔa⟩ := hback
  rw [← hfΔa]
  have hfa_pos : 0 < |f a| := abs_pos.mpr hf
  have ha_pos  : 0 < |a|   := abs_pos.mpr ha
  -- |f(a+Δa) - f a| ≤ |df a| * ε
  have h1 : |f (a + Δa) - f a| ≤ |df a| * ε :=
    le_trans (hlin Δa hΔa) (mul_le_mul_of_nonneg_left hΔa (abs_nonneg _))
  -- condNumber simplifies: |a * df a / f a| * (ε / |a|) = |df a| * ε / |f a|
  have hrhs : |a * df a / f a| * (ε / |a|) = |df a| * ε / |f a| := by
    rw [abs_div, abs_mul]
    field_simp [ha_pos.ne', hfa_pos.ne']
  rw [hrhs]
  -- Reduce to h1 by contradiction: assume strict inequality, multiply by |f a|
  by_contra h
  push_neg at h
  have hmul := mul_lt_mul_of_pos_right h hfa_pos
  have hc1 : |f (a + Δa) - f a| / |f a| * |f a| = |f (a + Δa) - f a| := by
    field_simp [hfa_pos.ne']
  have hc2 : |df a| * ε / |f a| * |f a| = |df a| * ε := by
    field_simp [hfa_pos.ne']
  rw [hc1, hc2] at hmul
  linarith

/-- Normwise vector form of the Chapter 1 rule of thumb:

`forward error <= condition number * backward error`.

If `xhat` is exact for a normwise input perturbation `Δa` with
`||Δa||_in <= ε`, and the problem has local normwise condition-number bound
`κ` on the same perturbation radius, then the normwise forward error is bounded
by `κ * (ε / ||a||_in)`. -/
theorem normwise_forward_from_backward_vec (n m : ℕ)
    (normIn : (Fin n → ℝ) → ℝ) (normOut : (Fin m → ℝ) → ℝ)
    (f : (Fin n → ℝ) → (Fin m → ℝ))
    (a : Fin n → ℝ) (xhat : Fin m → ℝ) (ε κ : ℝ)
    (ha : 0 < normIn a)
    (hκ : 0 ≤ κ)
    (hback : normwiseBackwardErrorBoundedVec n m normIn f a xhat ε)
    (hcond : normwiseConditionNumberBoundedVec n m normIn normOut f a κ ε) :
    forwardErrorBoundedVec n m normOut f a xhat (κ * (ε / normIn a)) := by
  unfold forwardErrorBoundedVec
  obtain ⟨Δa, hΔa, hxhat⟩ := hback
  rw [← hxhat]
  have hlocal := hcond Δa hΔa
  calc
    normwiseRelError m normOut (f (fun i => a i + Δa i)) (f a)
        ≤ κ * (normIn Δa / normIn a) := hlocal
    _ ≤ κ * (ε / normIn a) := by
        exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hΔa (le_of_lt ha)) hκ

/-- Supremum-valued version of the normwise Chapter 1 rule of thumb.  It uses
the source-facing least-upper-bound condition number directly, then delegates to
the existing local bound theorem. -/
theorem normwise_forward_from_backward_vec_of_condition_supremum (n m : ℕ)
    (normIn : (Fin n → ℝ) → ℝ) (normOut : (Fin m → ℝ) → ℝ)
    (f : (Fin n → ℝ) → (Fin m → ℝ))
    (a : Fin n → ℝ) (xhat : Fin m → ℝ) (ε κ : ℝ)
    (ha : 0 < normIn a)
    (hκ_nonneg : 0 ≤ κ)
    (hback : normwiseBackwardErrorBoundedVec n m normIn f a xhat ε)
    (hκ :
      normwiseConditionNumberSupremumVec n m normIn normOut f a κ ε) :
    forwardErrorBoundedVec n m normOut f a xhat (κ * (ε / normIn a)) := by
  exact
    normwise_forward_from_backward_vec n m normIn normOut f a xhat ε κ ha
      hκ_nonneg hback hκ.bounded

end NumStability
