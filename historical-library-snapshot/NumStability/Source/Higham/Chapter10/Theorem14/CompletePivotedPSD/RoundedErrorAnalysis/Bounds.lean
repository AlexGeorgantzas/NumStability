import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.Cholesky.CholeskyDemmel
import NumStability.Algorithms.Cholesky.CholeskyFl
import NumStability.Algorithms.Cholesky.CholeskyNonsym
import NumStability.Algorithms.Cholesky.CholeskySpec
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LinearSystems.Cholesky.ErrorAnalysis.Certificates
import NumStability.Algorithms.LinearSystems.Cholesky.Perturbation.Basic
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.Basic
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.KahanMatrix
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.ScaledStage
import NumStability.Analysis.MatrixNorms.EntrywiseAbsolute.Basic
import NumStability.Analysis.MatrixNorms.SpectralExtrema.Basic
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter09.Problems
import NumStability.Source.Higham.Chapter09.Section01
import NumStability.Source.Higham.Chapter09.Section02
import NumStability.Source.Higham.Chapter09.Section03
import NumStability.Source.Higham.Chapter09.Section04
import NumStability.Source.Higham.Chapter09.Section05
import NumStability.Source.Higham.Chapter09.Section06
import NumStability.Source.Higham.Chapter09.Section08
import NumStability.Source.Higham.Chapter09.Section10
import NumStability.Source.Higham.Chapter09.Section11
import NumStability.Source.Higham.Chapter10.Equation07.AbsoluteFactorNorm.Endpoints
import NumStability.Source.Higham.Chapter10.Equation29.Mathias.Endpoints
import NumStability.Source.Higham.Chapter10.Equation30.ComplexPositiveDefinite.Endpoints
import NumStability.Source.Higham.Chapter10.Lemma11.PivotSequenceStability.Endpoints
import NumStability.Source.Higham.Chapter10.Lemma13.KahanSharpness.CompletePivotingBound
import NumStability.Source.Higham.Chapter10.Lemma13.KahanSharpness.Endpoints
import NumStability.Source.Higham.Chapter10.Problem01.PositiveSemidefiniteEntries.Basic
import NumStability.Source.Higham.Chapter10.Problem01.PositiveSemidefiniteEntries.EntryBounds.Results
import NumStability.Source.Higham.Chapter10.Problem04.UnpivotedGrowth.Basic
import NumStability.Source.Higham.Chapter10.Problem08.LeadingMinorsCounterexample.Basic
import NumStability.Source.Higham.Chapter10.Section01.Factorization.Basic
import NumStability.Source.Higham.Chapter10.Section02.ErrorAnalysis.Basic
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.Endpoints
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.Existence
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.SchurComplement
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.Termination
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.WNormBound
import NumStability.Source.Higham.Chapter10.Section04.PositiveDefiniteSymmetricPart.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem06.RoundedCholesky.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem07.FailureVacuity.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem08.ComponentwisePerturbation.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem08.NormwiseDiscrepancy.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.PsdErrorAnalysis

/-!
# Bounds

Canonical destination for 3 declaration(s) relocated from
`NumStability.Algorithms.Cholesky.CholeskyPSD` during wave R04. Declaration names, kinds, signatures and
visibilities are unchanged; authored-private declarations keep their
names and change only their mangled module owner, per the reviewed
B0008 private-normalization map.
-/

open scoped BigOperators

namespace NumStability

/-- **Computed factor rows are pivot-dominated** (the `c`-discharge for
    Theorem 10.14's domination hypothesis, one stage): if the exact
    working matrix is PSD with maximal pivot and floor `ρ`, and the
    computed working matrix is `ht`-close (`ht ≤ ρ/4`), then every
    computed off-pivot factor entry `fl(S̃_pj / √S̃_pp)` is bounded by
    `(1 + 4ht/ρ)(1+u)/(1−u)²` times the computed pivot entry
    `fl(√S̃_pp)` — the computed form of the (10.13) invariant, with the
    domination constant explicit. -/
theorem fl_factor_row_dominated (fp : FPModel) {n : ℕ}
    (S Stilde : Fin n → Fin n → ℝ) (p : Fin n) (ρ ht : ℝ)
    (hPSD : IsPosSemiDef n S)
    (hmax : ∀ j : Fin n, S j j ≤ S p p)
    (hfloorS : ρ ≤ S p p) (hρ : 0 < ρ)
    (hht : 0 ≤ ht) (hht2 : ht ≤ ρ / 4)
    (hclose : ∀ i j : Fin n, |S i j - Stilde i j| ≤ ht)
    (hu1 : fp.u < 1) :
    ∀ j : Fin n,
      |fp.fl_div (Stilde p j) (fp.fl_sqrt (Stilde p p))| ≤
      (1 + 4 * ht / ρ) * ((1 + fp.u) / (1 - fp.u) ^ 2) *
        |fp.fl_sqrt (Stilde p p)| := by
  intro j
  have hu0 := fp.u_nonneg
  have h1u : (0:ℝ) < 1 - fp.u := by linarith
  -- the computed pivot is well above zero
  have hSpp : ρ ≤ S p p := hfloorS
  have hStpp : ρ / 2 ≤ Stilde p p := by
    have h1 := abs_le.mp (hclose p p)
    linarith [h1.2]
  have hStpp0 : (0:ℝ) < Stilde p p := by linarith
  have hsq0 : (0:ℝ) < Real.sqrt (Stilde p p) :=
    Real.sqrt_pos.mpr hStpp0
  obtain ⟨δa, hδa, hsqrt⟩ := fp.model_sqrt (Stilde p p) hStpp0.le
  have ha := abs_le.mp hδa
  have h1a : (0:ℝ) < 1 + δa := by linarith [ha.1]
  have hfs0 : fp.fl_sqrt (Stilde p p) ≠ 0 := by
    rw [hsqrt]; positivity
  obtain ⟨δb, hδb, hdiv⟩ := fp.model_div (Stilde p j)
    (fp.fl_sqrt (Stilde p p)) hfs0
  have hb := abs_le.mp hδb
  -- numerator control through the exact PSD structure
  have hnum : |Stilde p j| ≤ Stilde p p * (1 + 4 * ht / ρ) := by
    have h1 : |Stilde p j| ≤ |S p j| + ht := by
      have h := hclose p j
      have h2 := abs_sub_abs_le_abs_sub (Stilde p j) (S p j)
      rw [abs_sub_comm (Stilde p j) (S p j)] at h2
      linarith
    have h2 : |S p j| ≤ S p p := by
      calc |S p j| ≤ Real.sqrt (S p p) * Real.sqrt (S j j) :=
            psd_abs_entry_le_sqrt_diag S hPSD p j
        _ ≤ Real.sqrt (S p p) * Real.sqrt (S p p) :=
            mul_le_mul_of_nonneg_left
              (Real.sqrt_le_sqrt (hmax j)) (Real.sqrt_nonneg _)
        _ = S p p := Real.mul_self_sqrt (by linarith)
    have h3 : S p p ≤ Stilde p p + ht := by
      have h := abs_le.mp (hclose p p)
      linarith [h.1]
    have h4 : Stilde p p + 2 * ht ≤
        Stilde p p * (1 + 4 * ht / ρ) := by
      rw [mul_add, mul_one]
      have : Stilde p p * (4 * ht / ρ) ≥ 2 * ht := by
        rw [ge_iff_le, show Stilde p p * (4 * ht / ρ) =
          Stilde p p * 4 * ht / ρ by ring, le_div_iff₀ hρ]
        nlinarith
      linarith
    linarith
  -- assemble through the model factors
  rw [hdiv, hsqrt]
  rw [abs_mul, abs_div, abs_mul, abs_of_pos hsq0, abs_of_pos h1a]
  have h1b : |1 + δb| ≤ 1 + fp.u := by
    rw [abs_le]; constructor <;> linarith [hb.1, hb.2]
  have hda : (1:ℝ) - fp.u ≤ 1 + δa := by linarith [ha.1]
  have hsqSt : Real.sqrt (Stilde p p) * Real.sqrt (Stilde p p) =
      Stilde p p := Real.mul_self_sqrt hStpp0.le
  -- |S̃ p j| / (√·(1+δa)) · |1+δb| ≤ target
  calc |Stilde p j| / (Real.sqrt (Stilde p p) * (1 + δa)) *
        |1 + δb|
      ≤ (Stilde p p * (1 + 4 * ht / ρ)) /
          (Real.sqrt (Stilde p p) * (1 - fp.u)) * (1 + fp.u) := by
        refine mul_le_mul ?_ h1b (abs_nonneg _) (by positivity)
        refine div_le_div₀ (by positivity) hnum (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hda (Real.sqrt_nonneg _)
    _ = (1 + 4 * ht / ρ) * ((1 + fp.u) / (1 - fp.u) ^ 2) *
          (Real.sqrt (Stilde p p) * (1 - fp.u)) := by
        field_simp
        nlinarith [hsqSt]
    _ ≤ (1 + 4 * ht / ρ) * ((1 + fp.u) / (1 - fp.u) ^ 2) *
          (Real.sqrt (Stilde p p) * (1 + δa)) := by
        refine mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hda (Real.sqrt_nonneg _)) ?_
        positivity

/-- **All computed factor rows are pivot-dominated across the run**
    (Theorem 10.14 `c`-discharge, composed): under the no-tie data and
    the rounding budget (bounded by `ρ/4`), at every stage `t < r` of
    the factor-form floating-point run, every computed off-pivot factor
    entry is at most `(1 + 4·h t/ρ)(1+u)/(1−u)²` times the computed
    pivot entry — the computed (10.13) invariant for the whole run,
    with per-stage explicit constants. -/
theorem fl_cpFactor_rows_dominated (fp : FPModel) {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hPSD : IsPosSemiDef n A) (r : ℕ)
    (δ ρ c : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hc : 0 ≤ c)
    (h5 : gammaValid fp 5)
    (h : ℕ → ℝ) (hh0 : h 0 = 0)
    (hhstep : ∀ t : ℕ, t < r →
      h t + (3 * c ^ 2 * h t + c * h t ^ 2) / (ρ / 2) ^ 2 +
        (fp.u * ((c + δ / 2) + (c + δ / 2) ^ 2 / (ρ / 2)) +
          (1 + fp.u) * gamma fp 5 * ((c + δ / 2) ^ 2 / (ρ / 2))) ≤
        h (t + 1))
    (hhhalf : ∀ t : ℕ, t < r → h t < δ / 2)
    (hht4 : ∀ t : ℕ, t < r → h t ≤ ρ / 4)
    (hgap : ∀ t : ℕ, t < r → ∀ i : Fin n, i ≠ cpPivot hn A t →
      cpState hn A t i i + δ ≤
        cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hfloor : ∀ t : ℕ, t < r →
      ρ ≤ cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hcap : ∀ t : ℕ, t < r → ∀ i j : Fin n,
      |cpState hn A t i j| ≤ c) :
    ∀ t : ℕ, t < r → ∀ j : Fin n,
      |fp.fl_div (fl_cpStateFactor fp hn A t (cpPivot hn A t) j)
        (fp.fl_sqrt (fl_cpStateFactor fp hn A t
          (cpPivot hn A t) (cpPivot hn A t)))| ≤
      (1 + 4 * h t / ρ) * ((1 + fp.u) / (1 - fp.u) ^ 2) *
        |fp.fl_sqrt (fl_cpStateFactor fp hn A t
          (cpPivot hn A t) (cpPivot hn A t))| := by
  intro t htr j
  have hρ0 : (0:ℝ) < ρ := lt_of_lt_of_le hδ hδρ
  have hu1 : fp.u < 1 := by
    unfold gammaValid at h5
    push_cast at h5
    nlinarith [fp.u_nonneg]
  -- stage data from the agreement induction and the exact invariants
  have hagree := fl_cpPivotFactor_sequence_agrees fp hn A r δ ρ c
    hδ hδρ hc h5 h hh0 hhstep hhhalf hgap hfloor hcap t
    (Nat.le_of_lt htr)
  have hclose := hagree.1
  have hSPSD : IsPosSemiDef n (cpState hn A t) :=
    cpState_isPosSemiDef hn A hPSD t fun s hs =>
      lt_of_lt_of_le hρ0 (hfloor s (lt_trans hs htr))
  have hht0 : 0 ≤ h t := by
    rcases Nat.eq_zero_or_pos t with rfl | ht0
    · rw [hh0]
    · have h1 := hhhalf t htr
      -- nonnegativity via the budget recurrence from stage t-1
      obtain ⟨t', rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht0.ne'
      have ht'r : t' < r := lt_trans (Nat.lt_succ_self t') htr
      have hstep := hhstep t' ht'r
      have haux : ∀ s : ℕ, s ≤ t' → 0 ≤ h s := by
        intro s
        induction s with
        | zero => intro _; rw [hh0]
        | succ s ihs =>
          intro hsr
          have hs' : s < r := by omega
          have h0 := ihs (by omega)
          have hst := hhstep s hs'
          have h1' : (0:ℝ) ≤
              (3 * c ^ 2 * h s + c * h s ^ 2) / (ρ / 2) ^ 2 := by
            positivity
          have h2' : (0:ℝ) ≤
              fp.u * ((c + δ / 2) + (c + δ / 2) ^ 2 / (ρ / 2)) +
              (1 + fp.u) * gamma fp 5 *
                ((c + δ / 2) ^ 2 / (ρ / 2)) := by
            have hγ := gamma_nonneg fp h5
            have hu0 := fp.u_nonneg
            refine add_nonneg (by positivity)
              (mul_nonneg (mul_nonneg (by positivity) hγ)
                (by positivity))
          linarith
      have h0 := haux t' le_rfl
      have h1' : (0:ℝ) ≤
          (3 * c ^ 2 * h t' + c * h t' ^ 2) / (ρ / 2) ^ 2 := by
        positivity
      have h2' : (0:ℝ) ≤
          fp.u * ((c + δ / 2) + (c + δ / 2) ^ 2 / (ρ / 2)) +
          (1 + fp.u) * gamma fp 5 * ((c + δ / 2) ^ 2 / (ρ / 2)) := by
        have hγ := gamma_nonneg fp h5
        have hu0 := fp.u_nonneg
        refine add_nonneg (by positivity)
          (mul_nonneg (mul_nonneg (by positivity) hγ)
            (by positivity))
      linarith
  exact fl_factor_row_dominated fp (cpState hn A t)
    (fl_cpStateFactor fp hn A t) (cpPivot hn A t) ρ (h t)
    hSPSD (cpPivot_max hn A t) (hfloor t htr) hρ0 hht0
    (hht4 t htr) hclose hu1 j

/-- **Theorem 10.14 for the algorithm as run, fully composed**: under
    the exact trace's no-tie data, the rounding budget (capped at
    `ρ/4`), `u ≤ 1/8`, commutative rounded multiplication, and `A` PSD
    symmetric, the computed pivoted factorization satisfies the
    componentwise backward-error bound
    `|∑_{t<r} r̃ᵗᵢr̃ᵗⱼ + S̃ᵣᵢⱼ − aᵢⱼ| ≤ r(u·cS + (2u+u²)·cR²)` with the
    explicit caps `cS = c + δ/2` and
    `cR = 2(1+u)²/(1−u)²·√(c + δ/2)` discharged from the agreement
    machinery — no cap hypotheses remain. -/
theorem higham10_14_as_run_backward_error (fp : FPModel) {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℝ) (r : ℕ)
    (δ ρ c : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hc : 0 ≤ c)
    (h5 : gammaValid fp 5) (hu8 : fp.u ≤ 1 / 8)
    (hmul : ∀ x y : ℝ, fp.fl_mul x y = fp.fl_mul y x)
    (hPSD : IsPosSemiDef n A)
    (h : ℕ → ℝ) (hh0 : h 0 = 0)
    (hhstep : ∀ t : ℕ, t < r →
      h t + (3 * c ^ 2 * h t + c * h t ^ 2) / (ρ / 2) ^ 2 +
        (fp.u * ((c + δ / 2) + (c + δ / 2) ^ 2 / (ρ / 2)) +
          (1 + fp.u) * gamma fp 5 * ((c + δ / 2) ^ 2 / (ρ / 2))) ≤
        h (t + 1))
    (hhhalf : ∀ t : ℕ, t < r → h t < δ / 2)
    (hht4 : ∀ t : ℕ, t < r → h t ≤ ρ / 4)
    (hgap : ∀ t : ℕ, t < r → ∀ i : Fin n, i ≠ cpPivot hn A t →
      cpState hn A t i i + δ ≤
        cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hfloor : ∀ t : ℕ, t < r →
      ρ ≤ cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hcap : ∀ t : ℕ, t < r → ∀ i j : Fin n,
      |cpState hn A t i j| ≤ c) :
    ∀ i j : Fin n,
      |(∑ t ∈ Finset.range r,
          fl_cpRowOf fp (fl_cpStateFactor fp hn A t)
            (fl_cpPivotFactor fp hn A t) i *
          fl_cpRowOf fp (fl_cpStateFactor fp hn A t)
            (fl_cpPivotFactor fp hn A t) j) +
        fl_cpStateFactor fp hn A r i j - A i j| ≤
      (r : ℝ) * (fp.u * (c + δ / 2) + (2 * fp.u + fp.u ^ 2) *
        (2 * (1 + fp.u) ^ 2 / (1 - fp.u) ^ 2 *
          Real.sqrt (c + δ / 2)) ^ 2) := by
  have hρ0 : (0:ℝ) < ρ := lt_of_lt_of_le hδ hδρ
  have hu0 := fp.u_nonneg
  have hu1 : fp.u < 1 := by linarith
  have h1u : (0:ℝ) < 1 - fp.u := by linarith
  have hcδ : (0:ℝ) ≤ c + δ / 2 := by linarith
  -- stage data shared by all discharges
  have hagree := fl_cpPivotFactor_sequence_agrees fp hn A r δ ρ c
    hδ hδρ hc h5 h hh0 hhstep hhhalf hgap hfloor hcap
  have hstage : ∀ t : ℕ, t < r →
      fl_cpPivotFactor fp hn A t = cpPivot hn A t := by
    intro t htr
    exact ((hagree (t + 1) (Nat.succ_le_of_lt htr)).2 t
      (Nat.lt_succ_self t)).symm
  have hclose : ∀ t : ℕ, t < r → ∀ i j : Fin n,
      |cpState hn A t i j - fl_cpStateFactor fp hn A t i j| ≤ h t :=
    fun t htr => (hagree t (Nat.le_of_lt htr)).1
  have hSfloor : ∀ t : ℕ, t < r → ρ / 2 ≤
      fl_cpStateFactor fp hn A t (cpPivot hn A t) (cpPivot hn A t) := by
    intro t htr
    have h1 := abs_le.mp (hclose t htr (cpPivot hn A t)
      (cpPivot hn A t))
    have h2 := hfloor t htr
    have h3 := hhhalf t htr
    linarith [h1.1, hδρ]
  -- pivot positivity for the fl states
  have hpos : ∀ t : ℕ, t < r →
      0 < fl_cpStateFactor fp hn A t (fl_cpPivotFactor fp hn A t)
        (fl_cpPivotFactor fp hn A t) := by
    intro t htr
    rw [hstage t htr]
    linarith [hSfloor t htr]
  -- state cap
  have hcapS : ∀ t : ℕ, t < r → ∀ i j : Fin n,
      |fl_cpStateFactor fp hn A t i j| ≤ c + δ / 2 := by
    intro t htr i j
    have h1 := hclose t htr i j
    have h2 := hcap t htr i j
    have h3 := abs_sub_abs_le_abs_sub
      (fl_cpStateFactor fp hn A t i j) (cpState hn A t i j)
    rw [abs_sub_comm (fl_cpStateFactor fp hn A t i j)
      (cpState hn A t i j)] at h3
    have h4 := hhhalf t htr
    linarith
  -- row cap: pivot entry via the sqrt model, off-pivot via domination
  have hcapR : ∀ t : ℕ, t < r → ∀ i : Fin n,
      |fl_cpRowOf fp (fl_cpStateFactor fp hn A t)
        (fl_cpPivotFactor fp hn A t) i| ≤
      2 * (1 + fp.u) ^ 2 / (1 - fp.u) ^ 2 *
        Real.sqrt (c + δ / 2) := by
    intro t htr i
    have hp := hstage t htr
    have hSp := hSfloor t htr
    have hSpos : (0:ℝ) < fl_cpStateFactor fp hn A t
        (cpPivot hn A t) (cpPivot hn A t) := by linarith
    -- the computed pivot entry
    obtain ⟨δa, hδa, hsqrt⟩ := fp.model_sqrt
      (fl_cpStateFactor fp hn A t (cpPivot hn A t) (cpPivot hn A t))
      hSpos.le
    have ha := abs_le.mp hδa
    have hsqle : Real.sqrt (fl_cpStateFactor fp hn A t
        (cpPivot hn A t) (cpPivot hn A t)) ≤
        Real.sqrt (c + δ / 2) := by
      apply Real.sqrt_le_sqrt
      have := hcapS t htr (cpPivot hn A t) (cpPivot hn A t)
      calc fl_cpStateFactor fp hn A t (cpPivot hn A t)
            (cpPivot hn A t)
          ≤ |fl_cpStateFactor fp hn A t (cpPivot hn A t)
            (cpPivot hn A t)| := le_abs_self _
        _ ≤ c + δ / 2 := this
    have hpivot_cap : |fp.fl_sqrt (fl_cpStateFactor fp hn A t
        (cpPivot hn A t) (cpPivot hn A t))| ≤
        (1 + fp.u) * Real.sqrt (c + δ / 2) := by
      rw [hsqrt, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      have h1a : |1 + δa| ≤ 1 + fp.u := by
        rw [abs_le]
        constructor <;> linarith [ha.1, ha.2]
      calc Real.sqrt _ * |1 + δa|
          ≤ Real.sqrt (c + δ / 2) * (1 + fp.u) :=
            mul_le_mul hsqle h1a (abs_nonneg _) (Real.sqrt_nonneg _)
        _ = (1 + fp.u) * Real.sqrt (c + δ / 2) := mul_comm _ _
    -- exact-state invariants at stage t for the domination lemma
    have hSPSD : IsPosSemiDef n (cpState hn A t) :=
      cpState_isPosSemiDef hn A hPSD t fun s hs =>
        lt_of_lt_of_le hρ0 (hfloor s (lt_trans hs htr))
    have hht0 : 0 ≤ h t := by
      have h1 := abs_nonneg (cpState hn A t (cpPivot hn A t)
        (cpPivot hn A t) - fl_cpStateFactor fp hn A t
        (cpPivot hn A t) (cpPivot hn A t))
      exact le_trans h1 (hclose t htr _ _)
    have hdom := fl_factor_row_dominated fp (cpState hn A t)
      (fl_cpStateFactor fp hn A t) (cpPivot hn A t) ρ (h t)
      hSPSD (cpPivot_max hn A t) (hfloor t htr) hρ0 hht0
      (hht4 t htr) (hclose t htr) hu1 i
    have hconst : (1 + 4 * h t / ρ) * ((1 + fp.u) / (1 - fp.u) ^ 2) ≤
        2 * (1 + fp.u) / (1 - fp.u) ^ 2 := by
      have h1 : 4 * h t / ρ ≤ 1 := by
        rw [div_le_one hρ0]
        linarith [hht4 t htr]
      have h2 : (0:ℝ) ≤ (1 + fp.u) / (1 - fp.u) ^ 2 := by positivity
      have h1' : 1 + 4 * h t / ρ ≤ 2 := by linarith
      calc (1 + 4 * h t / ρ) * ((1 + fp.u) / (1 - fp.u) ^ 2)
          ≤ 2 * ((1 + fp.u) / (1 - fp.u) ^ 2) :=
            mul_le_mul_of_nonneg_right h1' h2
        _ = 2 * (1 + fp.u) / (1 - fp.u) ^ 2 := by ring
    unfold fl_cpRowOf
    rw [hp]
    by_cases hip : i = cpPivot hn A t
    · rw [if_pos hip]
      refine hpivot_cap.trans ?_
      have hge1 : (1:ℝ) ≤ 2 * (1 + fp.u) / (1 - fp.u) ^ 2 := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith
      calc (1 + fp.u) * Real.sqrt (c + δ / 2)
          ≤ (2 * (1 + fp.u) / (1 - fp.u) ^ 2) *
            ((1 + fp.u) * Real.sqrt (c + δ / 2)) := by
            nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 + fp.u)
              (Real.sqrt_nonneg (c + δ / 2)), hge1]
        _ = 2 * (1 + fp.u) ^ 2 / (1 - fp.u) ^ 2 *
            Real.sqrt (c + δ / 2) := by ring
    · rw [if_neg hip]
      refine (hdom).trans ?_
      calc (1 + 4 * h t / ρ) * ((1 + fp.u) / (1 - fp.u) ^ 2) *
            |fp.fl_sqrt (fl_cpStateFactor fp hn A t
              (cpPivot hn A t) (cpPivot hn A t))|
          ≤ (2 * (1 + fp.u) / (1 - fp.u) ^ 2) *
            ((1 + fp.u) * Real.sqrt (c + δ / 2)) := by
            refine mul_le_mul hconst hpivot_cap (abs_nonneg _) ?_
            positivity
        _ = 2 * (1 + fp.u) ^ 2 / (1 - fp.u) ^ 2 *
            Real.sqrt (c + δ / 2) := by ring
  exact fl_cpFactor_gram_backward_error fp hn A r hmul hPSD.1 hu8
    hpos (c + δ / 2)
    (2 * (1 + fp.u) ^ 2 / (1 - fp.u) ^ 2 * Real.sqrt (c + δ / 2))
    hcapS hcapR

end NumStability

open scoped BigOperators

namespace NumStability

/-- **Theorem 10.14 for the concrete algorithm** (display (10.22)
    shape): the three-block backward-error certificate of the truncated
    computed factor `R̃ = fl_choleskyTrunc` after `r` completed stages —
    Demmel-stable computed block, trace-controlled border under the
    computed-pivot domination `c`, terminal Schur residual `η` on the
    trailing block. -/
theorem higham10_14_fl_psd_cholesky_backward_error (fp : FPModel)
    (n : ℕ) (A : Fin n → Fin n → ℝ) (hn1 : gammaValid fp (n + 1))
    (hγlt : gamma fp (n + 1) < 1)
    (hsymm : ∀ i j : Fin n, A i j = A j i) (r : ℕ)
    (hdz : ∀ i : Fin n, i.val < r → fl_cholesky fp n A i i ≠ 0)
    (hpiv : ∀ i : Fin n, i.val < r → 0 ≤ fl_cholPivot fp n A i)
    (c : ℝ) (hc : 0 ≤ c)
    (hdom : ∀ j : Fin n, r ≤ j.val → ∀ k : Fin n, k.val < r →
      |fl_cholesky fp n A k j| ≤ c * |fl_cholesky fp n A k k|)
    (η : ℝ)
    (htrail : ∀ i j : Fin n, r ≤ i.val → r ≤ j.val →
      |∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < r),
        fl_cholesky fp n A k i * fl_cholesky fp n A k j - A i j| ≤ η) :
    (∀ i j : Fin n, i.val < r → j.val < r →
      |∑ k : Fin n, fl_choleskyTrunc fp n A r k i *
        fl_choleskyTrunc fp n A r k j - A i j| ≤
      gamma fp (n + 1) / (1 - gamma fp (n + 1)) *
        (Real.sqrt (A i i) * Real.sqrt (A j j))) ∧
    (∀ i j : Fin n, i.val < r → r ≤ j.val →
      |∑ k : Fin n, fl_choleskyTrunc fp n A r k i *
        fl_choleskyTrunc fp n A r k j - A i j| ≤
      gamma fp (n + 1) * c / (1 - gamma fp (n + 1)) *
        (Real.sqrt (A i i) *
         Real.sqrt (∑ k ∈ Finset.univ.filter
          (fun k : Fin n => k.val < r), A k k))) ∧
    (∀ i j : Fin n, r ≤ i.val → j.val < r →
      |∑ k : Fin n, fl_choleskyTrunc fp n A r k i *
        fl_choleskyTrunc fp n A r k j - A i j| ≤
      gamma fp (n + 1) * c / (1 - gamma fp (n + 1)) *
        (Real.sqrt (A j j) *
         Real.sqrt (∑ k ∈ Finset.univ.filter
          (fun k : Fin n => k.val < r), A k k))) ∧
    (∀ i j : Fin n, r ≤ i.val → r ≤ j.val →
      |∑ k : Fin n, fl_choleskyTrunc fp n A r k i *
        fl_choleskyTrunc fp n A r k j - A i j| ≤ η) :=
  fl_choleskyTrunc_backward_error fp n A hn1 hγlt hsymm r hdz hpiv
    c hc hdom η htrail

end NumStability
