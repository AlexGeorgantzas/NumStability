-- Rounding.lean

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import NumStability.FloatingPoint.Model

namespace NumStability

/-!
# Accumulated Rounding Error Bound (γ)

Following Higham, "Accuracy and Stability of Numerical Algorithms", §3.1.
The central source statements are Lemma 3.1 for products of local rounding
factors and Lemma 3.3 in §3.4 for algebraic rules on `θ_k`/`γ_k` terms.

For a sequence of n elementary floating-point operations each introducing
a relative error at most u (the unit roundoff), the worst-case accumulated
relative error is bounded by γ(n), defined below.

The definition is valid only under the side condition `n * u < 1`,
which ensures the denominator is positive and the bound is finite.
This condition is always satisfied in practice for reasonable n,
since u is of order 2⁻⁵³ for IEEE double precision.
-/

-- ============================================================
-- §3.1  The γ function
-- ============================================================

/-- `gamma fp n` is Higham's γₙ = (n * u) / (1 - n * u).

    It bounds the relative error accumulated after n rounding operations,
    each satisfying the standard model fl(x op y) = (x op y)(1 + δ), |δ| ≤ u.

    Precondition for meaningful use: `n * fp.u < 1`.
    See `gammaValid` for the explicit guard and `prod_error_bound` for the
    central lemma that justifies this bound. -/
noncomputable def gamma (fp : FPModel) (n : ℕ) : ℝ :=
  (n * fp.u) / (1 - n * fp.u)

/-- Well-definedness guard for `gamma`.
    The denominator `1 - n * u` is positive iff `n * u < 1`.
    All lemmas that use `gamma` in a meaningful bound require this hypothesis.
    In practice this holds for any realistic algorithm depth, since
    u ≈ 2⁻⁵³ in double precision. -/
def gammaValid (fp : FPModel) (n : ℕ) : Prop :=
  (n : ℝ) * fp.u < 1

-- ============================================================
-- §3.1  Basic properties of gamma and gammaValid
-- ============================================================

/-- `gammaValid` is monotone: if n operations are valid, so are k ≤ n. -/
lemma gammaValid_mono (fp : FPModel) {k n : ℕ} (h : k ≤ n) (hn : gammaValid fp n) :
    gammaValid fp k := by
  unfold gammaValid at hn ⊢
  have hkn : (k : ℝ) ≤ n := by exact_mod_cast h
  linarith [mul_le_mul_of_nonneg_right hkn fp.u_nonneg]

/-- A displayed unit-roundoff cap implies the corresponding `gammaValid` guard.

This is useful for public theorem surfaces stated with an explicit cap `Ucap`:
if `fp.u ≤ Ucap` and the displayed cap satisfies `(n : ℝ) * Ucap < 1`, then
the usual validity condition `(n : ℝ) * fp.u < 1` is not an additional
hypothesis. -/
lemma gammaValid_of_u_le_cap (fp : FPModel) (n : ℕ) (Ucap : ℝ)
    (hu : fp.u ≤ Ucap) (hcap : (n : ℝ) * Ucap < 1) :
    gammaValid fp n := by
  unfold gammaValid
  have hn_nonneg : (0 : ℝ) ≤ n := by exact_mod_cast n.zero_le
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hu hn_nonneg) hcap

/-- `gamma` is nonneg whenever `gammaValid` holds. -/
lemma gamma_nonneg (fp : FPModel) {n : ℕ} (hn : gammaValid fp n) : 0 ≤ gamma fp n :=
  div_nonneg (mul_nonneg (by exact_mod_cast n.zero_le) fp.u_nonneg)
             (by unfold gammaValid at hn; linarith)

/-- Exact split of `γ_n` into its first-order unit-roundoff term plus the
quadratic-and-higher rational remainder. -/
lemma gamma_eq_linear_plus_quadratic_remainder (fp : FPModel) (n : ℕ)
    (hn : gammaValid fp n) :
    gamma fp n =
      (n : ℝ) * fp.u + (((n : ℝ) * fp.u) ^ 2) /
        (1 - (n : ℝ) * fp.u) := by
  have hden : 1 - (n : ℝ) * fp.u ≠ 0 := by
    unfold gammaValid at hn
    linarith
  unfold gamma
  field_simp [hden]
  ring

/-- If the accumulated first-order term is at most one half, then `γ_n` is at
most twice the first-order term.  This is the standard way to turn a proved
`gamma` bound into a readable linear-in-`nu` surface under an explicit smallness
regime. -/
lemma gamma_le_two_mul_n_u_of_nu_le_half (fp : FPModel) (n : ℕ)
    (hhalf : (n : ℝ) * fp.u ≤ 1 / 2) :
    gamma fp n ≤ 2 * ((n : ℝ) * fp.u) := by
  set a : ℝ := (n : ℝ) * fp.u
  have ha_nonneg : 0 ≤ a := by
    exact mul_nonneg (by exact_mod_cast n.zero_le) fp.u_nonneg
  have hden_pos : 0 < 1 - a := by
    linarith
  unfold gamma
  change a / (1 - a) ≤ 2 * a
  rw [div_le_iff₀ hden_pos]
  nlinarith

/-- Source-shaped `nu` simplification for the `γ_{n-1}` radius.

For a nonempty `n`-term sum, the exact `gamma (n - 1)` radius is at most
`n * u` whenever the displayed smallness side condition
`n * (n - 1) * u ≤ 1` holds. -/
lemma gamma_pred_le_n_mul_u_of_n_mul_pred_u_le_one (fp : FPModel) {n : ℕ}
    (hn : 0 < n) (hvalid : gammaValid fp (n - 1))
    (hsmall : (n : ℝ) * (((n - 1 : ℕ) : ℝ) * fp.u) ≤ 1) :
    gamma fp (n - 1) ≤ (n : ℝ) * fp.u := by
  set k : ℕ := n - 1
  set a : ℝ := (k : ℝ) * fp.u
  have hden_pos : 0 < 1 - a := by
    unfold gammaValid at hvalid
    dsimp [k, a] at hvalid
    linarith
  have hsmall_u : ((n : ℝ) * a) * fp.u ≤ fp.u := by
    have h := mul_le_mul_of_nonneg_right hsmall fp.u_nonneg
    simpa [a, k, mul_assoc] using h
  have hdiff : (n : ℝ) * fp.u - a = fp.u := by
    have hk : (k : ℝ) + 1 = (n : ℝ) := by
      exact_mod_cast (Nat.sub_add_cancel hn)
    rw [← hk]
    dsimp [a]
    ring
  unfold gamma
  change a / (1 - a) ≤ (n : ℝ) * fp.u
  rw [div_le_iff₀ hden_pos]
  nlinarith

/-- `gamma` is monotone in n.

    Proof: write n = k + m, then γ(k) ≤ γ(k) + γ(m) + γ(k)·γ(m) ≤ γ(k+m) = γ(n). -/
lemma gamma_mono (fp : FPModel) {k n : ℕ} (h : k ≤ n) (hn : gammaValid fp n) :
    gamma fp k ≤ gamma fp n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  have hval' : (↑k + ↑m) * fp.u < 1 := by
    have h := hn; unfold gammaValid at h; push_cast at h; exact h
  have hku  : (↑k : ℝ) * fp.u < 1 :=
    by linarith [mul_nonneg (by exact_mod_cast m.zero_le : (0:ℝ) ≤ ↑m) fp.u_nonneg]
  have hmu  : (↑m : ℝ) * fp.u < 1 :=
    by linarith [mul_nonneg (by exact_mod_cast k.zero_le : (0:ℝ) ≤ ↑k) fp.u_nonneg]
  have hdk  : (0 : ℝ) < 1 - ↑k * fp.u        := by linarith
  have hdm  : (0 : ℝ) < 1 - ↑m * fp.u        := by linarith
  have hdkm : (0 : ℝ) < 1 - (↑k + ↑m) * fp.u := by linarith
  have hγk  : 0 ≤ gamma fp k :=
    div_nonneg (mul_nonneg (by exact_mod_cast k.zero_le) fp.u_nonneg) (by linarith)
  have hγm  : 0 ≤ gamma fp m :=
    div_nonneg (mul_nonneg (by exact_mod_cast m.zero_le) fp.u_nonneg) (by linarith)
  -- γ(k) + γ(m) + γ(k)·γ(m) ≤ γ(k+m)  (same identity as in gamma_mul)
  have h_ineq : gamma fp k + gamma fp m + gamma fp k * gamma fp m ≤ gamma fp (k + m) := by
    unfold gamma; push_cast; rw [← sub_nonneg]
    have key : (↑k + ↑m) * fp.u / (1 - (↑k + ↑m) * fp.u) -
               (↑k * fp.u / (1 - ↑k * fp.u) + ↑m * fp.u / (1 - ↑m * fp.u) +
                ↑k * fp.u / (1 - ↑k * fp.u) * (↑m * fp.u / (1 - ↑m * fp.u))) =
               ↑k * ↑m * fp.u ^ 2 /
               ((1 - ↑k * fp.u) * (1 - ↑m * fp.u) * (1 - (↑k + ↑m) * fp.u)) := by
      field_simp [hdk.ne', hdm.ne', hdkm.ne']; ring
    rw [key]
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by exact_mod_cast k.zero_le) (by exact_mod_cast m.zero_le))
                  (sq_nonneg fp.u))
      (le_of_lt (mul_pos (mul_pos hdk hdm) hdkm))
  linarith [mul_nonneg hγk hγm]

/-- The unit roundoff is bounded by γ(k) for any k ≥ 1.

    Proof: u ≤ k·u ≤ k·u/(1−k·u) = γ(k),
    since k ≥ 1 gives u ≤ k·u, and 1−k·u ≤ 1 gives k·u ≤ k·u/(1−k·u). -/
lemma u_le_gamma (fp : FPModel) {k : ℕ} (hk : 0 < k) (hval : gammaValid fp k) :
    fp.u ≤ gamma fp k := by
  unfold gamma
  have hku  : (↑k : ℝ) * fp.u < 1 := hval
  have hdk  : (0 : ℝ) < 1 - ↑k * fp.u := by linarith
  have hk1  : (1 : ℝ) ≤ ↑k := by exact_mod_cast hk
  -- fp.u ≤ k * fp.u  (since k ≥ 1)
  have h1 : fp.u ≤ ↑k * fp.u := le_mul_of_one_le_left fp.u_nonneg hk1
  -- k * fp.u ≤ k * fp.u / (1 - k * fp.u)  (since 1 - k * fp.u ≤ 1)
  have h2 : ↑k * fp.u ≤ ↑k * fp.u / (1 - ↑k * fp.u) := by
    by_contra hc
    push_neg at hc
    have hmul := mul_lt_mul_of_pos_right hc hdk
    have hcancel : ↑k * fp.u / (1 - ↑k * fp.u) * (1 - ↑k * fp.u) = ↑k * fp.u := by
      field_simp [hdk.ne']
    rw [hcancel] at hmul
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ ↑k) fp.u_nonneg) fp.u_nonneg]
  linarith

/-- The raw first-order quantity `n*u` is bounded by `gamma n`.

    This is the same denominator-shrinking fact as `u_le_gamma`, but without
    first dividing out the operation count. -/
lemma n_mul_u_le_gamma (fp : FPModel) (n : ℕ) (hval : gammaValid fp n) :
    (n : ℝ) * fp.u ≤ gamma fp n := by
  unfold gamma
  have hnu : (n : ℝ) * fp.u < 1 := hval
  have hden : 0 < 1 - (n : ℝ) * fp.u := by linarith
  have ha : 0 ≤ (n : ℝ) * fp.u :=
    mul_nonneg (by exact_mod_cast n.zero_le) fp.u_nonneg
  rw [le_div_iff₀ hden]
  nlinarith [sq_nonneg ((n : ℝ) * fp.u)]

/-- Multiplicative-index upper comparison for accumulated `gamma` terms.

If the larger index `i*k` is in the standard half-radius regime, then
`gamma (i*k)` is at most `2*i*gamma k`.  This is the converse-style estimate
used when a conservative operation-count radius has already been absorbed into
one large `gamma`, but a source-facing statement wants the smaller base radius
`gamma k` with an explicit dimension-only multiplier. -/
lemma gamma_mul_index_le_two_mul_nat_mul_gamma (fp : FPModel)
    (i k : ℕ)
    (hhalf : ((i * k : ℕ) : ℝ) * fp.u ≤ 1 / 2)
    (hkvalid : gammaValid fp k) :
    gamma fp (i * k) ≤ (2 : ℝ) * (i : ℝ) * gamma fp k := by
  have hlinear :
      ((i * k : ℕ) : ℝ) * fp.u ≤ (i : ℝ) * gamma fp k := by
    calc
      ((i * k : ℕ) : ℝ) * fp.u
          = (i : ℝ) * ((k : ℝ) * fp.u) := by
              norm_num [Nat.cast_mul]
              ring
      _ ≤ (i : ℝ) * gamma fp k :=
          mul_le_mul_of_nonneg_left
            (n_mul_u_le_gamma fp k hkvalid)
            (by exact_mod_cast Nat.zero_le i)
  calc
    gamma fp (i * k)
        ≤ 2 * (((i * k : ℕ) : ℝ) * fp.u) :=
            gamma_le_two_mul_n_u_of_nu_le_half fp (i * k) hhalf
    _ ≤ 2 * ((i : ℝ) * gamma fp k) :=
        mul_le_mul_of_nonneg_left hlinear (by norm_num)
    _ = (2 : ℝ) * (i : ℝ) * gamma fp k := by ring

/-- Cap `gamma fp n` by replacing the unit roundoff with a displayed upper cap.

This is the monotonicity of `x ↦ n*x/(1-n*x)` on the validity interval,
packaged in the form needed by downstream explicit floating-point budgets. -/
lemma gamma_le_of_u_le_cap (fp : FPModel) (n : ℕ) (Ucap : ℝ)
    (hu : fp.u ≤ Ucap) (hcap : (n : ℝ) * Ucap < 1) :
    gamma fp n ≤ ((n : ℝ) * Ucap) / (1 - (n : ℝ) * Ucap) := by
  unfold gamma
  have hn_nonneg : (0 : ℝ) ≤ n := by exact_mod_cast n.zero_le
  have hnu : (n : ℝ) * fp.u < 1 := by
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hu hn_nonneg) hcap
  have hdenu : 0 < 1 - (n : ℝ) * fp.u := by linarith
  have hdenU : 0 < 1 - (n : ℝ) * Ucap := by linarith
  rw [← sub_nonneg]
  have key :
      (n : ℝ) * Ucap / (1 - (n : ℝ) * Ucap) -
          (n : ℝ) * fp.u / (1 - (n : ℝ) * fp.u) =
        (n : ℝ) * (Ucap - fp.u) /
          ((1 - (n : ℝ) * Ucap) * (1 - (n : ℝ) * fp.u)) := by
    field_simp [hdenU.ne', hdenu.ne']
    ring
  rw [key]
  exact div_nonneg
    (mul_nonneg hn_nonneg (sub_nonneg.mpr hu))
    (le_of_lt (mul_pos hdenU hdenu))

/-- Displayed-cap version of `gamma_le_of_u_le_cap`.

If `Gcap` dominates the rational expression obtained by replacing `u` with
`Ucap`, then `Gcap` is a valid upper bound for `gamma fp n`. -/
lemma gamma_le_Gcap_of_u_le_cap (fp : FPModel) (n : ℕ) (Ucap Gcap : ℝ)
    (hu : fp.u ≤ Ucap) (hcap : (n : ℝ) * Ucap < 1)
    (hGcap : ((n : ℝ) * Ucap) / (1 - (n : ℝ) * Ucap) ≤ Gcap) :
    gamma fp n ≤ Gcap :=
  le_trans (gamma_le_of_u_le_cap fp n Ucap hu hcap) hGcap

-- ============================================================
-- §3.1  Product lemma
-- ============================================================

open scoped BigOperators

/-- Product over an appended finite tuple splits into the product of its pieces. -/
lemma fin_prod_append {α : Type*} [CommMonoid α] (j k : ℕ)
    (a : Fin j → α) (b : Fin k → α) :
    (∏ i : Fin (j + k), Fin.append a b i) =
      (∏ i : Fin j, a i) * (∏ i : Fin k, b i) := by
  rw [← Fin.prod_ofFn (Fin.append a b), List.ofFn_fin_append,
    List.prod_append, Fin.prod_ofFn a, Fin.prod_ofFn b]

/-- **Product rounding error lemma** (Higham §3.1, Lemma 3.1).

    Given n rounding errors δ_i with |δ_i| ≤ u, their product satisfies
      ∏ᵢ (1 + δᵢ) = 1 + θ
    for some θ with |θ| ≤ γ(n).

    This is the foundational lemma for all forward error analysis:
    any composition of n rounded operations accumulates a relative
    error bounded by γ(n), regardless of the signs of the individual δᵢ.-/

lemma prod_error_bound (fp : FPModel) (n : ℕ) (δ : Fin n → ℝ)
    (hδ : ∀ i, |δ i| ≤ fp.u)
    (hn : gammaValid fp n) :
    ∃ θ : ℝ, |θ| ≤ gamma fp n ∧
      ∏ i : Fin n, (1 + δ i) = 1 + θ := by
  induction n with
  | zero => exact ⟨0, by simp [gamma], by simp⟩
  | succ n ih =>
    -- Predecessor validity: n*u < (n+1)*u < 1
    have hnu : (n : ℝ) * fp.u < 1 := by
      have h := hn; unfold gammaValid at h; push_cast at h
      have : (↑n + 1) * fp.u = ↑n * fp.u + fp.u := by ring
      linarith [fp.u_nonneg]
    have hn_pred : gammaValid fp n := hnu
    -- Apply IH to the first n components
    obtain ⟨θ', hθ', hprod⟩ :=
      ih (fun i => δ i.castSucc) (fun i => hδ i.castSucc) hn_pred
    -- The new error: θ' from prefix + δₙ from last op + cross term
    refine ⟨θ' + δ (Fin.last n) + θ' * δ (Fin.last n), ?_, ?_⟩
    · have hδn   : |δ (Fin.last n)| ≤ fp.u := hδ (Fin.last n)
      have hγn   : 0 ≤ gamma fp n :=
        div_nonneg (mul_nonneg (by exact_mod_cast n.zero_le) fp.u_nonneg) (by linarith)
      have hn1u  : ((n : ℝ) + 1) * fp.u < 1 := by
        have h := hn; unfold gammaValid at h; push_cast at h; exact h
      have hd_pos  : (0 : ℝ) < 1 - ↑n * fp.u       := by linarith
      have hd1_pos : (0 : ℝ) < 1 - (↑n + 1) * fp.u := by linarith
      -- Product bound: |θ' * δₙ| ≤ γ(n) * u
      have hmul : |θ'| * |δ (Fin.last n)| ≤ gamma fp n * fp.u :=
        mul_le_mul hθ' hδn (abs_nonneg _) hγn
      have hcmul : |θ' * δ (Fin.last n)| ≤ gamma fp n * fp.u := abs_mul θ' _ ▸ hmul
      -- Triangle inequality via abs_le (avoids case split on sign)
      have h_tri : |θ' + δ (Fin.last n) + θ' * δ (Fin.last n)|
          ≤ gamma fp n + fp.u + gamma fp n * fp.u := by
        rw [abs_le]
        constructor
        · linarith [neg_abs_le θ', neg_abs_le (δ (Fin.last n)),
                    neg_abs_le (θ' * δ (Fin.last n))]
        · linarith [le_abs_self θ', le_abs_self (δ (Fin.last n)),
                    le_abs_self (θ' * δ (Fin.last n))]
      -- Algebraic identity: γ(n) + u + γ(n)·u = (n+1)·u / (1 - n·u)
      have h_id : gamma fp n + fp.u + gamma fp n * fp.u =
          (↑n + 1) * fp.u / (1 - ↑n * fp.u) := by
        unfold gamma; field_simp [hd_pos.ne']; ring
      -- Monotonicity: (n+1)·u / (1 - n·u) ≤ γ(n+1) since denominator shrinks
      -- Proof: show γ(n+1) - (n+1)u/(1-nu) = (n+1)u² / ((1-nu)(1-(n+1)u)) ≥ 0
      have h_le : (↑n + 1) * fp.u / (1 - ↑n * fp.u) ≤ gamma fp (n + 1) := by
        unfold gamma; push_cast
        have h0n : (0 : ℝ) ≤ ↑n := by exact_mod_cast n.zero_le
        have ha : (0 : ℝ) ≤ (↑n + 1) * fp.u := by
          have : (↑n + 1) * fp.u = ↑n * fp.u + fp.u := by ring
          linarith [mul_nonneg h0n fp.u_nonneg, fp.u_nonneg]
        rw [← sub_nonneg]
        have key : (↑n + 1) * fp.u / (1 - (↑n + 1) * fp.u) -
                   (↑n + 1) * fp.u / (1 - ↑n * fp.u) =
                   (↑n + 1) * fp.u * fp.u /
                   ((1 - ↑n * fp.u) * (1 - (↑n + 1) * fp.u)) := by
          field_simp [hd_pos.ne', hd1_pos.ne']; ring
        rw [key]
        exact div_nonneg (mul_nonneg ha fp.u_nonneg) (le_of_lt (mul_pos hd_pos hd1_pos))
      linarith
    · -- ∏ᵢ<n+1 (1+δᵢ) = (∏ᵢ<n (1+δᵢ.castSucc)) * (1+δₙ) = (1+θ') * (1+δₙ)
      rw [Fin.prod_univ_castSucc, hprod]; ring

/-- Linearized nonnegative geometric product bound.

If `c >= 0` and the accumulated product radius satisfies `n*c <= 1/2`, then
`(1+c)^n - 1 <= 2*n*c`.  This is a convenient way to reuse Higham's product
lemma for second-order factors such as `c = O(u^2)`. -/
lemma one_add_pow_sub_one_le_two_mul_nat_mul_of_nat_mul_le_half
    (n : ℕ) {c : ℝ} (hc0 : 0 ≤ c)
    (hsmall : (n : ℝ) * c ≤ 1 / 2) :
    (1 + c) ^ n - 1 ≤ 2 * ((n : ℝ) * c) := by
  let fp := FPModel.exactWithUnitRoundoff c hc0
  have hvalid : gammaValid fp n := by
    unfold gammaValid
    dsimp [fp, FPModel.exactWithUnitRoundoff]
    linarith
  have hδ : ∀ _i : Fin n, |c| ≤ fp.u := by
    intro _i
    dsimp [fp, FPModel.exactWithUnitRoundoff]
    simp [abs_of_nonneg hc0]
  obtain ⟨θ, hθ, hprod⟩ :=
    prod_error_bound fp n (fun _i => c) hδ hvalid
  have hprod' : (1 + c) ^ n = 1 + θ := by
    simpa using hprod
  have hθ_eq : (1 + c) ^ n - 1 = θ := by
    linarith
  have hγ :
      gamma fp n ≤ 2 * ((n : ℝ) * c) := by
    simpa [fp, FPModel.exactWithUnitRoundoff] using
      gamma_le_two_mul_n_u_of_nu_le_half fp n hsmall
  calc
    (1 + c) ^ n - 1 = θ := hθ_eq
    _ ≤ |θ| := le_abs_self θ
    _ ≤ gamma fp n := hθ
    _ ≤ 2 * ((n : ℝ) * c) := hγ

-- ============================================================
-- §3.4  Lemma 3.3 — γ arithmetic rules
-- ============================================================

/- **γ multiplication rule** (Higham §3.4, Lemma 3.3 part 1).

    If |θⱼ| ≤ γ(j) and |θₖ| ≤ γ(k), then (1+θⱼ)(1+θₖ) = 1+θ
    for some θ with |θ| ≤ γ(j+k).

    Proof sketch: expand (1+θⱼ)(1+θₖ) = 1 + (θⱼ + θₖ + θⱼθₖ) and bound
      |θⱼ + θₖ + θⱼθₖ| ≤ γ(j) + γ(k) + γ(j)·γ(k) = γ(j+k)
    using the inequality γ(j) + γ(k) + γ(j)·γ(k) ≤ γ(j+k), proved via
    γ(j+k) − (γ(j)+γ(k)+γ(j)γ(k)) = j·k·u² / ((1−j·u)(1−k·u)(1−(j+k)·u)) ≥ 0. -/
lemma gamma_mul (fp : FPModel) (j k : ℕ) (θj θk : ℝ)
    (hj  : |θj| ≤ gamma fp j)
    (hk  : |θk| ≤ gamma fp k)
    (hval : gammaValid fp (j + k)) :
    ∃ θ : ℝ, |θ| ≤ gamma fp (j + k) ∧ (1 + θj) * (1 + θk) = 1 + θ := by
  refine ⟨θj + θk + θj * θk, ?_, by ring⟩
  -- Sub-step 1: positivity facts
  have hval' : (↑j + ↑k) * fp.u < 1 := by
    have h := hval; unfold gammaValid at h; push_cast at h; exact h
  have hju : (↑j : ℝ) * fp.u < 1 := by
    linarith [mul_nonneg (by exact_mod_cast k.zero_le : (0:ℝ) ≤ ↑k) fp.u_nonneg]
  have hku : (↑k : ℝ) * fp.u < 1 := by
    linarith [mul_nonneg (by exact_mod_cast j.zero_le : (0:ℝ) ≤ ↑j) fp.u_nonneg]
  have hdj  : (0 : ℝ) < 1 - ↑j * fp.u       := by linarith
  have hdk  : (0 : ℝ) < 1 - ↑k * fp.u       := by linarith
  have hdjk : (0 : ℝ) < 1 - (↑j + ↑k) * fp.u := by linarith
  have hγj : 0 ≤ gamma fp j :=
    div_nonneg (mul_nonneg (by exact_mod_cast j.zero_le) fp.u_nonneg) (by linarith)
  have hγk : 0 ≤ gamma fp k :=
    div_nonneg (mul_nonneg (by exact_mod_cast k.zero_le) fp.u_nonneg) (by linarith)
  -- Sub-step 2: cross term bound
  have hmul : |θj * θk| ≤ gamma fp j * gamma fp k :=
    abs_mul θj θk ▸ mul_le_mul hj hk (abs_nonneg _) hγj
  -- Sub-step 3: triangle inequality
  have h_tri : |θj + θk + θj * θk| ≤ gamma fp j + gamma fp k + gamma fp j * gamma fp k := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le θj, neg_abs_le θk, neg_abs_le (θj * θk)]
    · linarith [le_abs_self θj, le_abs_self θk, le_abs_self (θj * θk)]
  -- Sub-step 4: γ(j) + γ(k) + γ(j)·γ(k) ≤ γ(j+k)
  have h_gamma_ineq : gamma fp j + gamma fp k + gamma fp j * gamma fp k ≤ gamma fp (j + k) := by
    unfold gamma; push_cast
    rw [← sub_nonneg]
    have key : (↑j + ↑k) * fp.u / (1 - (↑j + ↑k) * fp.u) -
               (↑j * fp.u / (1 - ↑j * fp.u) + ↑k * fp.u / (1 - ↑k * fp.u) +
                ↑j * fp.u / (1 - ↑j * fp.u) * (↑k * fp.u / (1 - ↑k * fp.u))) =
               ↑j * ↑k * fp.u ^ 2 /
               ((1 - ↑j * fp.u) * (1 - ↑k * fp.u) * (1 - (↑j + ↑k) * fp.u)) := by
      field_simp [hdj.ne', hdk.ne', hdjk.ne']; ring
    rw [key]
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg (by exact_mod_cast j.zero_le) (by exact_mod_cast k.zero_le))
                       (sq_nonneg fp.u)
    · exact le_of_lt (mul_pos (mul_pos hdj hdk) hdjk)
  linarith

/-- **Signed product rounding error lemma** (Higham §3.1, Lemma 3.1).

    Given `n` rounding errors with `|δᵢ| ≤ u`, a product containing each
    factor either as `(1 + δᵢ)` or as its reciprocal has the form `1 + θ`
    with `|θ| ≤ γ(n)`.

    The Boolean selector `neg i` represents Higham's exponent `pᵢ = -1`
    when true and `pᵢ = +1` when false.  This avoids committing downstream
    users to a particular integer-power encoding while proving the signed
    content of Lemma 3.1. -/
lemma prod_signed_error_bound (fp : FPModel) (n : ℕ) (δ : Fin n → ℝ)
    (neg : Fin n → Bool)
    (hδ : ∀ i, |δ i| ≤ fp.u)
    (hn : gammaValid fp n) :
    ∃ θ : ℝ, |θ| ≤ gamma fp n ∧
      ∏ i : Fin n, (if neg i then 1 / (1 + δ i) else 1 + δ i) = 1 + θ := by
  induction n with
  | zero =>
      exact ⟨0, by simp [gamma], by simp⟩
  | succ n ih =>
      have hn_pred : gammaValid fp n := gammaValid_mono fp (Nat.le_succ n) hn
      have h1valid : gammaValid fp 1 := gammaValid_mono fp (by omega) hn
      have hu : fp.u < 1 := by
        unfold gammaValid at h1valid
        simpa using h1valid
      obtain ⟨θ', hθ', hprod⟩ :=
        ih (fun i => δ i.castSucc) (fun i => neg i.castSucc)
          (fun i => hδ i.castSucc) hn_pred
      let δ_last : ℝ := δ (Fin.last n)
      let α : ℝ := if neg (Fin.last n) then -δ_last / (1 + δ_last) else δ_last
      have hδ_last : |δ_last| ≤ fp.u := hδ (Fin.last n)
      have hpos : (0 : ℝ) < 1 + δ_last := by
        linarith [neg_abs_le δ_last]
      have hfactor :
          (if neg (Fin.last n) then 1 / (1 + δ_last) else 1 + δ_last) = 1 + α := by
        cases hneg : neg (Fin.last n)
        · simp [α, hneg]
        · simp [α, hneg]
          field_simp [hpos.ne']
          ring
      have hα_bound : |α| ≤ gamma fp 1 := by
        cases hneg : neg (Fin.last n)
        · simp [α, hneg]
          exact le_trans hδ_last (u_le_gamma fp one_pos h1valid)
        · simp [α, hneg, abs_div, abs_neg, abs_of_pos hpos]
          have h1u : (0 : ℝ) < 1 - fp.u := by linarith
          have hγ1 : gamma fp 1 = fp.u / (1 - fp.u) := by
            unfold gamma
            simp
          rw [hγ1, ← sub_nonneg]
          have key : fp.u / (1 - fp.u) - |δ_last| / (1 + δ_last) =
                 (fp.u * (1 + δ_last) - |δ_last| * (1 - fp.u)) /
                 ((1 - fp.u) * (1 + δ_last)) := by
            field_simp [h1u.ne', hpos.ne']
          rw [key]
          apply div_nonneg
          · nlinarith [neg_abs_le δ_last, fp.u_nonneg]
          · exact le_of_lt (mul_pos h1u hpos)
      obtain ⟨η, hη, heq⟩ := gamma_mul fp n 1 θ' α hθ' hα_bound hn
      refine ⟨η, hη, ?_⟩
      rw [Fin.prod_univ_castSucc, hprod]
      show (1 + θ') *
          (if neg (Fin.last n) then 1 / (1 + δ (Fin.last n)) else 1 + δ (Fin.last n)) =
        1 + η
      rw [show δ (Fin.last n) = δ_last from rfl, hfactor]
      exact heq

/-- **Stewart relative-error counter** `<k>` (Higham §3.4, eq. (3.10)).

The counter denotes a product of `k` local factors, each either `(1 + δᵢ)` or
its reciprocal, with `|δᵢ| <= u`.  A true Boolean selector means that the
corresponding source exponent is `-1`; false means `+1`. -/
noncomputable def relErrorCounter (fp : FPModel) (k : ℕ) (c : ℝ) : Prop :=
  ∃ (δ : Fin k → ℝ) (neg : Fin k → Bool),
    (∀ i, |δ i| ≤ fp.u) ∧
      c = ∏ i : Fin k, (if neg i then 1 / (1 + δ i) else 1 + δ i)

/-- A Stewart counter is bounded by the matching `γ` term. -/
lemma relErrorCounter_abs_sub_one_le_gamma (fp : FPModel) (k : ℕ) (c : ℝ)
    (hc : relErrorCounter fp k c) (hk : gammaValid fp k) :
    |c - 1| ≤ gamma fp k := by
  rcases hc with ⟨δ, neg, hδ, hc_eq⟩
  obtain ⟨θ, hθ, hprod⟩ := prod_signed_error_bound fp k δ neg hδ hk
  have hcθ : c = 1 + θ := by
    rw [hc_eq, hprod]
  rw [hcθ]
  simpa using hθ

/-- Stewart counter multiplication rule: `<j><k> = <j+k>`. -/
lemma relErrorCounter_mul (fp : FPModel) (j k : ℕ) (cj ck : ℝ)
    (hcj : relErrorCounter fp j cj) (hck : relErrorCounter fp k ck) :
    relErrorCounter fp (j + k) (cj * ck) := by
  rcases hcj with ⟨δj, negj, hδj, hcj_eq⟩
  rcases hck with ⟨δk, negk, hδk, hck_eq⟩
  refine ⟨Fin.append δj δk, Fin.append negj negk, ?_, ?_⟩
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro i
      simpa only [Fin.append_left] using hδj i
    · intro i
      simpa only [Fin.append_right] using hδk i
  · rw [hcj_eq, hck_eq]
    rw [← fin_prod_append j k
      (fun i : Fin j => if negj i then 1 / (1 + δj i) else 1 + δj i)
      (fun i : Fin k => if negk i then 1 / (1 + δk i) else 1 + δk i)]
    apply Finset.prod_congr rfl
    intro i _
    refine Fin.addCases ?_ ?_ i
    · intro i
      simp only [Fin.append_left]
    · intro i
      simp only [Fin.append_right]

/-- Positivity of a local signed factor when the unit roundoff is below one. -/
lemma relErrorCounter_factor_pos (fp : FPModel) {δ : ℝ} {neg : Bool}
    (hδ : |δ| ≤ fp.u) (hu : fp.u < 1) :
    0 < if neg then 1 / (1 + δ) else 1 + δ := by
  have hpos : (0 : ℝ) < 1 + δ := by
    linarith [neg_abs_le δ, hδ, hu]
  split
  · exact div_pos zero_lt_one hpos
  · exact hpos

/-- Stewart counter reciprocal rule: if `c = <k>` and `u < 1`, then `1/c = <k>`. -/
lemma relErrorCounter_inv (fp : FPModel) (k : ℕ) (c : ℝ)
    (hc : relErrorCounter fp k c) (hu : fp.u < 1) :
    relErrorCounter fp k (1 / c) := by
  rcases hc with ⟨δ, neg, hδ, hc_eq⟩
  refine ⟨δ, fun i => !neg i, hδ, ?_⟩
  let f : Fin k → ℝ := fun i => if neg i then 1 / (1 + δ i) else 1 + δ i
  let g : Fin k → ℝ := fun i => if !neg i then 1 / (1 + δ i) else 1 + δ i
  have hf_pos : ∀ i, 0 < f i := by
    intro i
    exact relErrorCounter_factor_pos fp (hδ i) hu
  have hf_ne : (∏ i : Fin k, f i) ≠ 0 :=
    (Finset.prod_pos (fun i _ => hf_pos i)).ne'
  have hgf : (∏ i : Fin k, g i) * (∏ i : Fin k, f i) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro i _
    have hpos : (0 : ℝ) < 1 + δ i := by
      linarith [neg_abs_le (δ i), hδ i, hu]
    cases hneg : neg i <;> simp [f, g, hneg]
    · field_simp [hpos.ne']
    · field_simp [hpos.ne']
  have hg_eq : (∏ i : Fin k, g i) = 1 / (∏ i : Fin k, f i) := by
    field_simp [hf_ne]
    simpa [mul_comm] using hgf
  rw [hc_eq]
  exact hg_eq.symm

/-- Stewart counter division rule: `<j>/<k> = <j+k>`, with `u < 1` for
nonzero reciprocal factors. -/
lemma relErrorCounter_div (fp : FPModel) (j k : ℕ) (cj ck : ℝ)
    (hcj : relErrorCounter fp j cj) (hck : relErrorCounter fp k ck)
    (hu : fp.u < 1) :
    relErrorCounter fp (j + k) (cj / ck) := by
  have hck_inv : relErrorCounter fp k (1 / ck) :=
    relErrorCounter_inv fp k ck hck hu
  simpa [div_eq_mul_inv] using relErrorCounter_mul fp j k cj (1 / ck) hcj hck_inv

/-- **γ reciprocal rule** (Higham §3.4, Lemma 3.3 part 2).

    If |θₖ| ≤ γ(k) and 1 + θₖ > 0, then 1/(1+θₖ) = 1+θ
    for some θ with |θ| ≤ γ(2k).

    Proof sketch: witness θ = −θₖ/(1+θₖ). Bound via
      |θ| = |θₖ|/(1+θₖ) ≤ γ(k)/(1+θₖ) ≤ γ(2k),
    using the identity γ(2k)·(1−γ(k)) = 2·γ(k) and 1−γ(k) ≤ 1+θₖ. -/
lemma gamma_inv (fp : FPModel) (k : ℕ) (θk : ℝ)
    (hk   : |θk| ≤ gamma fp k)
    (hpos : (0 : ℝ) < 1 + θk)
    (hval : gammaValid fp (2 * k)) :
    ∃ θ : ℝ, |θ| ≤ gamma fp (2 * k) ∧ 1 / (1 + θk) = 1 + θ := by
  refine ⟨-θk / (1 + θk), ?_, by field_simp [hpos.ne']; ring⟩
  -- Setup facts from hval
  have h2ku : 2 * (↑k : ℝ) * fp.u < 1 := by
    have h := hval; unfold gammaValid at h; push_cast at h; linarith
  have hku  : (↑k : ℝ) * fp.u < 1 := by linarith
  have hdk  : (0 : ℝ) < 1 - ↑k * fp.u     := by linarith
  have hd2k : (0 : ℝ) < 1 - 2 * ↑k * fp.u := by linarith
  have hγk  : 0 ≤ gamma fp k :=
    div_nonneg (mul_nonneg (by exact_mod_cast k.zero_le) fp.u_nonneg) (by linarith)
  have hγk_lt1 : gamma fp k < 1 := by
    unfold gamma; rw [div_lt_one hdk]; linarith
  have hγ2k : 0 ≤ gamma fp (2 * k) := by
    unfold gamma
    apply div_nonneg
    · exact mul_nonneg (by exact_mod_cast (2 * k).zero_le) fp.u_nonneg
    · have h := hval; unfold gammaValid at h; linarith
  have htk_lb : -gamma fp k ≤ θk := by linarith [neg_abs_le θk]
  -- Rewrite to multiplicative form
  have h_abs : |-θk / (1 + θk)| = |θk| / (1 + θk) := by
    rw [abs_div, abs_neg, abs_of_pos hpos]
  rw [h_abs]
  -- Key algebraic identity: γ(2k) · (1 − γ(k)) = 2 · γ(k)
  have h_id : gamma fp (2 * k) * (1 - gamma fp k) = 2 * gamma fp k := by
    unfold gamma; push_cast
    field_simp [hdk.ne', hd2k.ne']; ring
  have h_bound : |θk| ≤ gamma fp (2 * k) * (1 + θk) := by
    calc |θk|
        ≤ gamma fp k                           := hk
      _ ≤ 2 * gamma fp k                      := by linarith
      _ = gamma fp (2 * k) * (1 - gamma fp k) := h_id.symm
      _ ≤ gamma fp (2 * k) * (1 + θk)        :=
            mul_le_mul_of_nonneg_left (by linarith) hγ2k
  -- |θk| / (1 + θk) ≤ γ(2k): by contradiction, multiplying out
  have hcancel : |θk| / (1 + θk) * (1 + θk) = |θk| := by field_simp [hpos.ne']
  by_contra h
  push_neg at h
  have hmul := mul_lt_mul_of_pos_right h hpos
  rw [hcancel] at hmul
  linarith

/-- If a denominator has a `γ(k)` relative perturbation and the final division
    contributes one primitive rounding error, then the combined factor is still
    bounded by `γ(2k)` for `k ≥ 1`:

    `(1/(1+θ_k)) * (1+δ) = 1+θ`, with `|θ| ≤ γ(2k)`.

    This is the form needed by Higham Lemma 18.1 for the beta computation:
    the reciprocal and the final rounded division are counted together. -/
lemma gamma_inv_mul_roundoff (fp : FPModel) (k : ℕ) (θk δ : ℝ)
    (hkpos : 0 < k)
    (hk   : |θk| ≤ gamma fp k)
    (hδ   : |δ| ≤ fp.u)
    (hpos : (0 : ℝ) < 1 + θk)
    (hval : gammaValid fp (2 * k)) :
    ∃ θ : ℝ,
      |θ| ≤ gamma fp (2 * k) ∧
      (1 / (1 + θk)) * (1 + δ) = 1 + θ := by
  refine ⟨(δ - θk) / (1 + θk), ?_, ?_⟩
  · have h_abs_num : |δ - θk| ≤ fp.u + gamma fp k := by
      have hδ_lower : -fp.u ≤ δ := by linarith [neg_abs_le δ, hδ]
      have hδ_upper : δ ≤ fp.u := by linarith [le_abs_self δ, hδ]
      have hθ_lower : -gamma fp k ≤ θk := by linarith [neg_abs_le θk, hk]
      have hθ_upper : θk ≤ gamma fp k := by linarith [le_abs_self θk, hk]
      rw [abs_le]
      constructor
      · linarith
      · linarith
    have hval_k : gammaValid fp k := gammaValid_mono fp (by omega) hval
    have hγ2_nonneg : 0 ≤ gamma fp (2 * k) := gamma_nonneg fp hval
    have hθ_lower : -gamma fp k ≤ θk := by
      linarith [neg_abs_le θk, hk]
    have h2ku : 2 * (↑k : ℝ) * fp.u < 1 := by
      have h := hval
      unfold gammaValid at h
      push_cast at h
      linarith
    have hku : (↑k : ℝ) * fp.u < 1 := by linarith
    have hdk : (0 : ℝ) < 1 - ↑k * fp.u := by linarith
    have hd2k : (0 : ℝ) < 1 - 2 * ↑k * fp.u := by linarith
    have h_id : gamma fp (2 * k) * (1 - gamma fp k) =
        2 * gamma fp k := by
      unfold gamma
      push_cast
      field_simp [hdk.ne', hd2k.ne']
      ring
    have hright : fp.u + gamma fp k ≤ gamma fp (2 * k) * (1 + θk) := by
      calc
        fp.u + gamma fp k ≤ 2 * gamma fp k := by
          linarith [u_le_gamma fp hkpos hval_k]
        _ = gamma fp (2 * k) * (1 - gamma fp k) := h_id.symm
        _ ≤ gamma fp (2 * k) * (1 + θk) :=
          mul_le_mul_of_nonneg_left (by linarith) hγ2_nonneg
    rw [abs_div, abs_of_pos hpos]
    rw [div_le_iff₀ hpos]
    exact le_trans h_abs_num hright
  · field_simp [hpos.ne']
    ring

/-- **γ division rule** (Higham §3.4, Lemma 3.3 part 3).

    If |θⱼ| ≤ γ(j) and |θₖ| ≤ γ(k) and 1+θₖ > 0, then (1+θⱼ)/(1+θₖ) = 1+θ
    for some θ with |θ| ≤ γ(j + 2k).

    Proof sketch: apply `gamma_inv` to denominator (cost: 2k), then
      `gamma_mul` with the numerator (cost: j), total j+2k. -/
lemma gamma_div (fp : FPModel) (j k : ℕ) (θj θk : ℝ)
    (hj   : |θj| ≤ gamma fp j)
    (hk   : |θk| ≤ gamma fp k)
    (hpos : (0 : ℝ) < 1 + θk)
    (hval : gammaValid fp (j + 2 * k)) :
    ∃ θ : ℝ, |θ| ≤ gamma fp (j + 2 * k) ∧ (1 + θj) / (1 + θk) = 1 + θ := by
  -- Step 1: extract gammaValid fp (2 * k) from hval
  have hval2k : gammaValid fp (2 * k) := by
    unfold gammaValid at hval ⊢; push_cast at hval ⊢
    linarith [mul_nonneg (by exact_mod_cast j.zero_le : (0:ℝ) ≤ ↑j) fp.u_nonneg]
  -- Step 2: apply gamma_inv — cost 2k on denominator
  obtain ⟨θ', hθ', hinv⟩ := gamma_inv fp k θk hk hpos hval2k
  -- Step 3: apply gamma_mul — cost j + 2k on numerator × inv
  obtain ⟨θ'', hθ'', hmul⟩ := gamma_mul fp j (2 * k) θj θ' hj hθ' hval
  refine ⟨θ'', hθ'', ?_⟩
  have : (1 + θj) / (1 + θk) = (1 + θj) * (1 / (1 + θk)) := by ring
  rw [this, hinv, hmul]

/-- Scalar inequality for the sharp denominator branch in Higham Lemma 3.3.

If the denominator index `j` is no larger than the numerator index `k`, then
the worst quotient error radius `(γ_k + γ_j)/(1 - γ_j)` is bounded by
`γ_{k+j}`. -/
lemma gamma_add_div_one_sub_gamma_le_of_le (fp : FPModel) (k j : ℕ)
    (hjk : j ≤ k) (hval : gammaValid fp (k + j)) :
    (gamma fp k + gamma fp j) / (1 - gamma fp j) ≤ gamma fp (k + j) := by
  have hvalk : gammaValid fp k := gammaValid_mono fp (by omega) hval
  have hvalj : gammaValid fp j := gammaValid_mono fp (by omega) hval
  have h2j_le : 2 * j ≤ k + j := by omega
  have hval2j : gammaValid fp (2 * j) := gammaValid_mono fp h2j_le hval
  have hku : (k : ℝ) * fp.u < 1 := by
    simpa [gammaValid] using hvalk
  have hju : (j : ℝ) * fp.u < 1 := by
    simpa [gammaValid] using hvalj
  have h2ju : 2 * (j : ℝ) * fp.u < 1 := by
    have h := hval2j
    unfold gammaValid at h
    push_cast at h
    linarith
  have hkj : ((k : ℝ) + (j : ℝ)) * fp.u < 1 := by
    have h := hval
    unfold gammaValid at h
    push_cast at h
    exact h
  have hdk : (0 : ℝ) < 1 - (k : ℝ) * fp.u := by linarith
  have hdj : (0 : ℝ) < 1 - (j : ℝ) * fp.u := by linarith
  have hd2j : (0 : ℝ) < 1 - 2 * (j : ℝ) * fp.u := by linarith
  have hdkj : (0 : ℝ) < 1 - ((k : ℝ) + (j : ℝ)) * fp.u := by linarith
  have hγj_lt : gamma fp j < 1 := by
    unfold gamma
    rw [div_lt_one hdj]
    linarith
  have hdenγj : (0 : ℝ) < 1 - gamma fp j := by linarith
  rw [← sub_nonneg]
  unfold gamma
  push_cast
  set A : ℝ := (k : ℝ) * fp.u
  set B : ℝ := (j : ℝ) * fp.u
  have hABsum : ((k : ℝ) + (j : ℝ)) * fp.u = A + B := by
    simp [A, B]
    ring
  rw [hABsum]
  change 0 ≤
    (A + B) / (1 - (A + B)) -
      (A / (1 - A) + B / (1 - B)) /
        (1 - B / (1 - B))
  have hdA : 1 - A ≠ 0 := by simpa [A] using hdk.ne'
  have hdB : 1 - B ≠ 0 := by simpa [B] using hdj.ne'
  have hd2B : 1 - 2 * B ≠ 0 := by
    simpa [B, mul_comm, mul_left_comm, mul_assoc] using hd2j.ne'
  have hd2B' : 1 - B * 2 ≠ 0 := by
    simpa [mul_comm] using hd2B
  have hdAB : 1 - (A + B) ≠ 0 := by
    simpa [A, B, add_mul, add_comm, add_left_comm, add_assoc] using hdkj.ne'
  have hdGammaB : 1 - B / (1 - B) ≠ 0 := by
    simpa [B, gamma] using hdenγj.ne'
  have hd2B_pos : (0 : ℝ) < 1 - 2 * B := by
    simpa [B, mul_comm, mul_left_comm, mul_assoc] using hd2j
  have hdAB_pos : (0 : ℝ) < 1 - (A + B) := by
    simpa [A, B, add_mul, add_comm, add_left_comm, add_assoc] using hdkj
  have key :
      (A + B) / (1 - (A + B)) -
          (A / (1 - A) + B / (1 - B)) /
            (1 - B / (1 - B)) =
        (B * (A - B)) /
          ((1 - A) * (1 - 2 * B) * (1 - (A + B))) := by
    have hden_simpl : 1 - B / (1 - B) = (1 - 2 * B) / (1 - B) := by
      field_simp [hdB]
      ring
    rw [hden_simpl]
    field_simp [hdA, hdB, hd2B, hd2B', hdAB]
    ring_nf
    norm_num [Nat.rawCast]
    change A * B * (Nat.rawCast 1 : ℝ) = A * B
    simp [Nat.rawCast]
  rw [key]
  apply div_nonneg
  · apply mul_nonneg
    · simpa [B] using mul_nonneg (by exact_mod_cast j.zero_le) fp.u_nonneg
    · simpa [A, B, sub_mul] using
        mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hjk : (j : ℝ) ≤ k)) fp.u_nonneg
  · exact le_of_lt (mul_pos (mul_pos hdk hd2B_pos) hdAB_pos)

/-- **Lemma 3.3 quotient rule, sharp branch**.

If `|θ_k| ≤ γ_k`, `|θ_j| ≤ γ_j`, and `j ≤ k`, then
`(1+θ_k)/(1+θ_j) = 1+θ_{k+j}`.  This is the first branch of the
second displayed relation in Higham Chapter 3 Lemma 3.3. -/
lemma gamma_div_le_branch (fp : FPModel) (k j : ℕ) (θk θj : ℝ)
    (hjk : j ≤ k)
    (hk : |θk| ≤ gamma fp k)
    (hj : |θj| ≤ gamma fp j)
    (hval : gammaValid fp (k + j)) :
    ∃ θ : ℝ, |θ| ≤ gamma fp (k + j) ∧
      (1 + θk) / (1 + θj) = 1 + θ := by
  have hvalk : gammaValid fp k := gammaValid_mono fp (by omega) hval
  have hvalj : gammaValid fp j := gammaValid_mono fp (by omega) hval
  have hval2j : gammaValid fp (2 * j) :=
    gammaValid_mono fp (by omega) hval
  have hγk_nonneg : 0 ≤ gamma fp k := gamma_nonneg fp hvalk
  have hγj_nonneg : 0 ≤ gamma fp j := gamma_nonneg fp hvalj
  have hju : (j : ℝ) * fp.u < 1 := by
    simpa [gammaValid] using hvalj
  have h2ju : 2 * (j : ℝ) * fp.u < 1 := by
    have h := hval2j
    unfold gammaValid at h
    push_cast at h
    linarith
  have hdj : (0 : ℝ) < 1 - (j : ℝ) * fp.u := by linarith
  have hγj_lt : gamma fp j < 1 := by
    unfold gamma
    rw [div_lt_one hdj]
    linarith
  have hθj_low : -gamma fp j ≤ θj := by
    linarith [neg_abs_le θj, hj]
  have hdenpos : (0 : ℝ) < 1 + θj := by linarith
  refine ⟨(θk - θj) / (1 + θj), ?_, ?_⟩
  · have hdenlower : 1 - gamma fp j ≤ 1 + θj := by linarith
    have hdenγpos : (0 : ℝ) < 1 - gamma fp j := by linarith
    have hnum : |θk - θj| ≤ gamma fp k + gamma fp j := by
      calc
        |θk - θj| ≤ |θk| + |θj| := by
          simpa [sub_eq_add_neg, abs_neg] using abs_add_le θk (-θj)
        _ ≤ gamma fp k + gamma fp j := add_le_add hk hj
    have hsum_nonneg : 0 ≤ gamma fp k + gamma fp j :=
      add_nonneg hγk_nonneg hγj_nonneg
    have hfrac1 :
        |θk - θj| / (1 + θj) ≤
          (gamma fp k + gamma fp j) / (1 + θj) :=
      div_le_div_of_nonneg_right hnum (le_of_lt hdenpos)
    have hfrac2 :
        (gamma fp k + gamma fp j) / (1 + θj) ≤
          (gamma fp k + gamma fp j) / (1 - gamma fp j) :=
      div_le_div_of_nonneg_left hsum_nonneg hdenγpos hdenlower
    have hgamma :=
      gamma_add_div_one_sub_gamma_le_of_le fp k j hjk hval
    rw [abs_div, abs_of_pos hdenpos]
    exact le_trans (le_trans hfrac1 hfrac2) hgamma
  · field_simp [hdenpos.ne']
    ring

/-- **Lemma 3.3 quotient rule, general/large-denominator branch**.

If `|θ_k| ≤ γ_k`, `|θ_j| ≤ γ_j`, and `j > k`, then the abstract quotient
can still be bounded as `1+θ_{k+2j}`.  The proof is the existing independent
denominator reciprocal rule, with denominator positivity derived from the
`gammaValid fp (k + 2*j)` guard. -/
lemma gamma_div_gt_branch (fp : FPModel) (k j : ℕ) (θk θj : ℝ)
    (_hgt : k < j)
    (hk : |θk| ≤ gamma fp k)
    (hj : |θj| ≤ gamma fp j)
    (hval : gammaValid fp (k + 2 * j)) :
    ∃ θ : ℝ, |θ| ≤ gamma fp (k + 2 * j) ∧
      (1 + θk) / (1 + θj) = 1 + θ := by
  have hval2j : gammaValid fp (2 * j) :=
    gammaValid_mono fp (by omega) hval
  have hvalj : gammaValid fp j := gammaValid_mono fp (by omega) hval
  have hju : (j : ℝ) * fp.u < 1 := by
    simpa [gammaValid] using hvalj
  have h2ju : 2 * (j : ℝ) * fp.u < 1 := by
    have h := hval2j
    unfold gammaValid at h
    push_cast at h
    linarith
  have hdj : (0 : ℝ) < 1 - (j : ℝ) * fp.u := by linarith
  have hγj_lt : gamma fp j < 1 := by
    unfold gamma
    rw [div_lt_one hdj]
    linarith
  have hθj_low : -gamma fp j ≤ θj := by
    linarith [neg_abs_le θj, hj]
  have hdenpos : (0 : ℝ) < 1 + θj := by linarith
  exact gamma_div fp k j θk θj hk hj hdenpos hval

-- ============================================================
-- §3.4  Additional Lemma 3.3 rules (standalone)
-- ============================================================

/-- **Lemma 3.3 rule 6** (standalone): γ(j) + γ(k) + γ(j)·γ(k) ≤ γ(j+k).

    This algebraic identity underlies both `gamma_mul` and `gamma_mono`.
    Proof: γ(j+k) − (γ(j)+γ(k)+γ(j)γ(k)) = j·k·u² / ((1−ju)(1−ku)(1−(j+k)u)) ≥ 0. -/
lemma gamma_sum_le (fp : FPModel) (j k : ℕ) (hval : gammaValid fp (j + k)) :
    gamma fp j + gamma fp k + gamma fp j * gamma fp k ≤ gamma fp (j + k) := by
  have hval' : (↑j + ↑k) * fp.u < 1 := by
    have h := hval; unfold gammaValid at h; push_cast at h; exact h
  have hju : (↑j : ℝ) * fp.u < 1 :=
    by linarith [mul_nonneg (by exact_mod_cast k.zero_le : (0:ℝ) ≤ ↑k) fp.u_nonneg]
  have hku : (↑k : ℝ) * fp.u < 1 :=
    by linarith [mul_nonneg (by exact_mod_cast j.zero_le : (0:ℝ) ≤ ↑j) fp.u_nonneg]
  have hdj  : (0 : ℝ) < 1 - ↑j * fp.u        := by linarith
  have hdk  : (0 : ℝ) < 1 - ↑k * fp.u        := by linarith
  have hdjk : (0 : ℝ) < 1 - (↑j + ↑k) * fp.u := by linarith
  unfold gamma; push_cast; rw [← sub_nonneg]
  have key : (↑j + ↑k) * fp.u / (1 - (↑j + ↑k) * fp.u) -
             (↑j * fp.u / (1 - ↑j * fp.u) + ↑k * fp.u / (1 - ↑k * fp.u) +
              ↑j * fp.u / (1 - ↑j * fp.u) * (↑k * fp.u / (1 - ↑k * fp.u))) =
             ↑j * ↑k * fp.u ^ 2 /
             ((1 - ↑j * fp.u) * (1 - ↑k * fp.u) * (1 - (↑j + ↑k) * fp.u)) := by
    field_simp [hdj.ne', hdk.ne', hdjk.ne']; ring
  rw [key]
  exact div_nonneg
    (mul_nonneg (mul_nonneg (by exact_mod_cast j.zero_le) (by exact_mod_cast k.zero_le))
                (sq_nonneg fp.u))
    (le_of_lt (mul_pos (mul_pos hdj hdk) hdjk))

/-- Absorb a repeated nonnegative local factor bounded by `gamma fp k` into the
    single Higham factor `gamma fp (n*k)`.

    This is the product-form analogue of replacing a sequence of first-order
    local constants by one larger accumulated gamma constant. -/
lemma one_add_pow_sub_one_le_gamma_mul_of_le_gamma
    (fp : FPModel) (n k : ℕ) {c : ℝ}
    (hc0 : 0 ≤ c) (hc : c ≤ gamma fp k)
    (hvalid : gammaValid fp (n * k)) :
    (1 + c) ^ n - 1 ≤ gamma fp (n * k) := by
  induction n with
  | zero =>
      simp [gamma]
  | succ n ih =>
      have hvalid_n : gammaValid fp (n * k) :=
        gammaValid_mono fp (by
          rw [Nat.succ_mul]
          exact Nat.le_add_right (n * k) k) hvalid
      have hvalid_step : gammaValid fp (n * k + k) := by
        simpa [Nat.succ_mul] using hvalid
      have hbase : (1 : ℝ) ≤ 1 + c := by linarith
      have hpow_ge_one : (1 : ℝ) ≤ (1 + c) ^ n := by
        exact one_le_pow₀ hbase
      have htheta_nonneg : 0 ≤ (1 + c) ^ n - 1 := by linarith
      have htheta_abs : |(1 + c) ^ n - 1| ≤ gamma fp (n * k) := by
        rw [abs_of_nonneg htheta_nonneg]
        exact ih hvalid_n
      have hc_abs : |c| ≤ gamma fp k := by
        rw [abs_of_nonneg hc0]
        exact hc
      rcases gamma_mul fp (n * k) k ((1 + c) ^ n - 1) c
          htheta_abs hc_abs hvalid_step with
        ⟨θ, hθ_abs, hprod⟩
      have hprod_pow : (1 + c) ^ (n + 1) = 1 + θ := by
        calc
          (1 + c) ^ (n + 1) = (1 + c) ^ n * (1 + c) := by
            rw [pow_succ]
          _ = (1 + ((1 + c) ^ n - 1)) * (1 + c) := by ring
          _ = 1 + θ := hprod
      have htheta_eq : (1 + c) ^ (n + 1) - 1 = θ := by linarith
      calc
        (1 + c) ^ (n + 1) - 1 = θ := htheta_eq
        _ ≤ |θ| := le_abs_self θ
        _ ≤ gamma fp (n * k + k) := hθ_abs
        _ = gamma fp ((n + 1) * k) := by rw [Nat.succ_mul]

/-- Absorb a repeated local `gamma fp k` factor followed by an additional
    `gamma fp n` solve factor into the single bound `gamma fp (n*k+n)`. -/
lemma one_add_pow_mul_one_add_gamma_sub_one_le_gamma_sum_of_le_gamma
    (fp : FPModel) (n k : ℕ) {c : ℝ}
    (hc0 : 0 ≤ c) (hc : c ≤ gamma fp k)
    (hvalid : gammaValid fp (n * k + n)) :
    (1 + c) ^ n * (1 + gamma fp n) - 1 ≤ gamma fp (n * k + n) := by
  have hvalid_nk : gammaValid fp (n * k) :=
    gammaValid_mono fp (Nat.le_add_right (n * k) n) hvalid
  have hvalid_n : gammaValid fp n :=
    gammaValid_mono fp (Nat.le_add_left n (n * k)) hvalid
  have htheta_le : (1 + c) ^ n - 1 ≤ gamma fp (n * k) :=
    one_add_pow_sub_one_le_gamma_mul_of_le_gamma fp n k hc0 hc hvalid_nk
  have hgamma_n_nonneg : 0 ≤ gamma fp n := gamma_nonneg fp hvalid_n
  have hone_theta_le :
      1 + ((1 + c) ^ n - 1) ≤ 1 + gamma fp (n * k) := by
    linarith
  have hmul :
      gamma fp n * (1 + ((1 + c) ^ n - 1)) ≤
        gamma fp n * (1 + gamma fp (n * k)) :=
    mul_le_mul_of_nonneg_left hone_theta_le hgamma_n_nonneg
  have hsum :
      gamma fp (n * k) + gamma fp n + gamma fp (n * k) * gamma fp n ≤
        gamma fp (n * k + n) :=
    gamma_sum_le fp (n * k) n hvalid
  calc
    (1 + c) ^ n * (1 + gamma fp n) - 1
        = ((1 + c) ^ n - 1) +
          gamma fp n * (1 + ((1 + c) ^ n - 1)) := by ring
    _ ≤ gamma fp (n * k) + gamma fp n * (1 + gamma fp (n * k)) := by
      exact add_le_add htheta_le hmul
    _ = gamma fp (n * k) + gamma fp n + gamma fp (n * k) * gamma fp n := by ring
    _ ≤ gamma fp (n * k + n) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hsum

/-- **Lemma 3.3 rule 5**: γ(k) + u ≤ γ(k+1).

    Proof: γ(k+1) − (γ(k)+u) = u²·(2k+1−k(k+1)u) / ((1−ku)(1−(k+1)u)) ≥ 0,
    since k(k+1)u < k ≤ 2k+1 from gammaValid fp (k+1). -/
lemma gamma_add_u_le (fp : FPModel) (k : ℕ) (hval : gammaValid fp (k + 1)) :
    gamma fp k + fp.u ≤ gamma fp (k + 1) := by
  have hku  : (↑k : ℝ) * fp.u < 1 := gammaValid_mono fp (Nat.le_succ k) hval
  have hk1u : ((↑k : ℝ) + 1) * fp.u < 1 := by
    have h := hval; unfold gammaValid at h; push_cast at h; exact h
  have hdk  : (0 : ℝ) < 1 - ↑k * fp.u        := by linarith
  have hdk1 : (0 : ℝ) < 1 - (↑k + 1) * fp.u  := by linarith
  unfold gamma; push_cast; rw [← sub_nonneg]
  have key : (↑k + 1) * fp.u / (1 - (↑k + 1) * fp.u) -
             (↑k * fp.u / (1 - ↑k * fp.u) + fp.u) =
             fp.u ^ 2 * (2 * ↑k + 1 - ↑k * (↑k + 1) * fp.u) /
             ((1 - ↑k * fp.u) * (1 - (↑k + 1) * fp.u)) := by
    field_simp [hdk.ne', hdk1.ne']; ring
  rw [key]
  apply div_nonneg
  · apply mul_nonneg (sq_nonneg fp.u)
    have hk0 : (0 : ℝ) ≤ ↑k := by exact_mod_cast k.zero_le
    have : ↑k * ((↑k + 1) * fp.u) ≤ ↑k * 1 :=
      mul_le_mul_of_nonneg_left (le_of_lt hk1u) hk0
    linarith
  · exact le_of_lt (mul_pos hdk hdk1)

/-- **Lemma 3.3 rule 4**: i·γ(k) ≤ γ(i·k) for i ≥ 1.

    Proof: i·(ku/(1−ku)) = iku/(1−ku) ≤ iku/(1−iku),
    since i ≥ 1 gives iku ≥ ku, hence 1−iku ≤ 1−ku (smaller denominator).
    Algebraically: γ(ik) − i·γ(k) = i(i−1)(ku)² / ((1−iku)(1−ku)) ≥ 0. -/
lemma gamma_nsmul_le (fp : FPModel) (i k : ℕ) (hi : 1 ≤ i)
    (hval : gammaValid fp (i * k)) :
    (i : ℝ) * gamma fp k ≤ gamma fp (i * k) := by
  have hiku : (↑i * ↑k) * fp.u < 1 := by
    have h := hval; unfold gammaValid at h; push_cast at h; linarith
  have hi1 : (1 : ℝ) ≤ ↑i := by exact_mod_cast hi
  have hk0 : (0 : ℝ) ≤ ↑k := by exact_mod_cast k.zero_le
  have hku : (↑k : ℝ) * fp.u < 1 := by
    nlinarith [mul_nonneg hk0 fp.u_nonneg]
  have hdiku : (0 : ℝ) < 1 - ↑i * ↑k * fp.u := by linarith
  have hdku  : (0 : ℝ) < 1 - ↑k * fp.u       := by linarith
  unfold gamma; push_cast; rw [← sub_nonneg]
  have key : ↑i * ↑k * fp.u / (1 - ↑i * ↑k * fp.u) -
             ↑i * (↑k * fp.u / (1 - ↑k * fp.u)) =
             ↑i * (↑i - 1) * (↑k * fp.u) ^ 2 /
             ((1 - ↑i * ↑k * fp.u) * (1 - ↑k * fp.u)) := by
    field_simp [hdiku.ne', hdku.ne']; ring
  rw [key]
  apply div_nonneg
  · apply mul_nonneg
    · exact mul_nonneg (by exact_mod_cast Nat.zero_le i) (by linarith)
    · exact sq_nonneg _
  · exact le_of_lt (mul_pos hdiku hdku)

/-- **Helper**: γ(k) < 1 whenever gammaValid fp (2k).

    Proof: gammaValid fp (2k) gives 2ku < 1, so ku < 1/2,
    hence ku/(1−ku) < 1 iff ku < 1−ku iff 2ku < 1. -/
lemma gamma_lt_one (fp : FPModel) (k : ℕ) (hval : gammaValid fp (2 * k)) :
    gamma fp k < 1 := by
  have hku : (↑k : ℝ) * fp.u < 1 :=
    gammaValid_mono fp (by omega) hval
  have h2ku : 2 * (↑k : ℝ) * fp.u < 1 := by
    have h := hval; unfold gammaValid at h; push_cast at h; linarith
  have hdk : (0 : ℝ) < 1 - ↑k * fp.u := by linarith
  unfold gamma
  rw [div_lt_one hdk]
  linarith

/-- **Lemma 3.3 rule 3**: γ(j)·γ(k) ≤ γ(min j k).

    WLOG j ≤ k (min = j).  Then γ(k) < 1 (from gammaValid fp (2k)),
    so γ(j)·γ(k) ≤ γ(j)·1 = γ(j).

    Precondition: gammaValid fp (2·k) (the larger index) ensures γ(k) < 1. -/
lemma gamma_prod_le (fp : FPModel) (j k : ℕ) (hjk : j ≤ k)
    (hval2k : gammaValid fp (2 * k)) :
    gamma fp j * gamma fp k ≤ gamma fp j := by
  have hval_j : gammaValid fp j :=
    gammaValid_mono fp (le_trans hjk (by omega)) hval2k
  have hγj    : 0 ≤ gamma fp j   := gamma_nonneg fp hval_j
  have hγk_lt : gamma fp k < 1   := gamma_lt_one fp k hval2k
  calc gamma fp j * gamma fp k
      ≤ gamma fp j * 1 := mul_le_mul_of_nonneg_left (le_of_lt hγk_lt) hγj
    _ = gamma fp j     := mul_one _

/-- **γ absorption rule**: 3γ(n) + γ(n)² ≤ γ(3n).

    This allows the LU solve backward error coefficient 3γ(n) + γ(n)²
    (from Theorem 9.4) to be absorbed into the cleaner γ(3n) bound.

    Proof: apply `gamma_sum_le` twice:
      3γ + γ² = (γ + γ + γ²) + γ ≤ γ(2n) + γ(n) ≤ γ(2n) + γ(n) + γ(2n)γ(n) ≤ γ(3n). -/
lemma three_gamma_plus_sq_le_gamma (fp : FPModel) (n : ℕ)
    (hval : gammaValid fp (3 * n)) :
    3 * gamma fp n + gamma fp n ^ 2 ≤ gamma fp (3 * n) := by
  have hval_nn : gammaValid fp (n + n) :=
    gammaValid_mono fp (by omega) hval
  have h1 : gamma fp n + gamma fp n + gamma fp n * gamma fp n ≤ gamma fp (n + n) :=
    gamma_sum_le fp n n hval_nn
  have h2 : gamma fp (n + n) + gamma fp n + gamma fp (n + n) * gamma fp n ≤
      gamma fp (n + n + n) :=
    gamma_sum_le fp (n + n) n (by rwa [show n + n + n = 3 * n from by omega])
  have hγ_nn : 0 ≤ gamma fp (n + n) := gamma_nonneg fp hval_nn
  have hγ_n : 0 ≤ gamma fp n := gamma_nonneg fp (gammaValid_mono fp (by omega) hval)
  calc 3 * gamma fp n + gamma fp n ^ 2
      = (gamma fp n + gamma fp n + gamma fp n * gamma fp n) + gamma fp n := by ring
    _ ≤ gamma fp (n + n) + gamma fp n := by linarith
    _ ≤ gamma fp (n + n) + gamma fp n + gamma fp (n + n) * gamma fp n := by
        linarith [mul_nonneg hγ_nn hγ_n]
    _ ≤ gamma fp (n + n + n) := h2
    _ = gamma fp (3 * n) := by congr 1; omega

end NumStability
