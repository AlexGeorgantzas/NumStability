import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Order.Monotone
import NumStability.Algorithms.StationaryIteration

/-!
# Higham Chapter 17, Equation 17.12

Canonical source-correspondence owner for the literal stationary-iteration series, the attained constant `c(A)`, and its bridge to finite partial-sum certificates.
-/

namespace NumStability

open scoped BigOperators

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- Geometric majorant for the entrywise terms of the series in Higham,
    Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.2,
    eq (17.12): each term `Σ_l |G^k|_{il} |M^{-1}|_{lj}` is bounded by
    `q^k · ‖M^{-1}‖₁`.  Scope note on the choice of majorant: every entry
    `|M^{-1}|_{lj}` is dominated by the `j`-th column sum, hence by the
    matrix 1-norm `‖M^{-1}‖₁` (the maximum column sum); this single uniform
    constant keeps all subsequent summability comparisons one-dimensional. -/
theorem matPow_entry_mul_sum_le_geometric (n : ℕ) (hn : 0 < n)
    (G M_inv : Fin n → Fin n → ℝ)
    (q : ℝ) (hG : infNorm G ≤ q) (i j : Fin n) (k : ℕ) :
    ∑ l : Fin n, |matPow n G k i l| * |M_inv l j| ≤ q ^ k * oneNorm M_inv := by
  have hcol : ∀ l : Fin n, |M_inv l j| ≤ oneNorm M_inv := fun l =>
    le_trans
      (Finset.single_le_sum (fun p _ => abs_nonneg (M_inv p j)) (Finset.mem_univ l))
      (col_sum_le_oneNorm M_inv j)
  calc ∑ l : Fin n, |matPow n G k i l| * |M_inv l j|
      ≤ ∑ l : Fin n, |matPow n G k i l| * oneNorm M_inv := by
        apply Finset.sum_le_sum
        intro l _
        exact mul_le_mul_of_nonneg_left (hcol l) (abs_nonneg _)
    _ = (∑ l : Fin n, |matPow n G k i l|) * oneNorm M_inv := by
        rw [Finset.sum_mul]
    _ ≤ infNorm (matPow n G k) * oneNorm M_inv :=
        mul_le_mul_of_nonneg_right (row_sum_le_infNorm _ i) (oneNorm_nonneg _)
    _ ≤ q ^ k * oneNorm M_inv :=
        mul_le_mul_of_nonneg_right
          ((infNorm_matPow_le hn G k).trans
            (pow_le_pow_left₀ (infNorm_nonneg G) hG k))
          (oneNorm_nonneg _)

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.2,
    eq (17.12): entrywise summability of the series
    `Σ_k Σ_l |G^k|_{il} |M^{-1}|_{lj}` under the norm certificate
    `‖G‖∞ ≤ q < 1`, by comparison with the geometric majorant
    `q^k · ‖M^{-1}‖₁` from `matPow_entry_mul_sum_le_geometric`. -/
theorem summable_matPow_entry_mul (n : ℕ) (hn : 0 < n)
    (G M_inv : Fin n → Fin n → ℝ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hG : infNorm G ≤ q) (i j : Fin n) :
    Summable (fun k => ∑ l : Fin n, |matPow n G k i l| * |M_inv l j|) :=
  Summable.of_nonneg_of_le
    (fun _ => Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    (fun k => matPow_entry_mul_sum_le_geometric n hn G M_inv q hG i j k)
    ((summable_geometric_of_lt_one hq0 hq1).mul_right (oneNorm M_inv))

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.2,
    eq (17.12): the literal entry of the infinite series
    `Σ_{k=0}^∞ |G^k M^{-1}|` at position `(i,j)`, in the componentwise form
    `Σ'_k Σ_l |G^k|_{il} |M^{-1}|_{lj}` used throughout the finite layer.
    Scope: like every real `tsum`, this evaluates to `0` when the series is
    not summable; the summability certificates above make it meaningful. -/
noncomputable def stationarySeriesEntry (n : ℕ) (G M_inv : Fin n → Fin n → ℝ)
    (i j : Fin n) : ℝ :=
  ∑' k : ℕ, ∑ l : Fin n, |matPow n G k i l| * |M_inv l j|

/-- The literal (17.12) series entries are nonnegative. -/
theorem stationarySeriesEntry_nonneg (n : ℕ) (G M_inv : Fin n → Fin n → ℝ)
    (i j : Fin n) :
    0 ≤ stationarySeriesEntry n G M_inv i j :=
  tsum_nonneg fun _ =>
    Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.2,
    eq (17.12): the literal series entry is bounded by
    `(1 - q)⁻¹ · ‖M^{-1}‖₁` under the norm certificate `‖G‖∞ ≤ q < 1`. -/
theorem stationarySeriesEntry_le (n : ℕ) (hn : 0 < n)
    (G M_inv : Fin n → Fin n → ℝ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hG : infNorm G ≤ q) (i j : Fin n) :
    stationarySeriesEntry n G M_inv i j ≤ (1 - q)⁻¹ * oneNorm M_inv :=
  calc stationarySeriesEntry n G M_inv i j
      ≤ ∑' k : ℕ, q ^ k * oneNorm M_inv :=
        Summable.tsum_le_tsum
          (fun k => matPow_entry_mul_sum_le_geometric n hn G M_inv q hG i j k)
          (summable_matPow_entry_mul n hn G M_inv q hq0 hq1 hG i j)
          ((summable_geometric_of_lt_one hq0 hq1).mul_right (oneNorm M_inv))
    _ = (1 - q)⁻¹ * oneNorm M_inv := by
        rw [tsum_mul_right, tsum_geometric_of_lt_one hq0 hq1]

/-- **The bridge from the literal (17.12) statement to every finite
    certificate** (Higham, Accuracy and Stability of Numerical Algorithms,
    2nd ed., §17.2, eq (17.12)): if the infinite series entries satisfy
    `Σ'_k Σ_l |G^k|_{il} |M^{-1}|_{lj} ≤ cA · |A^{-1}|_{ij}` and the
    entrywise series are summable, then the finite `PartialSumBound`
    certificate consumed by every finite forward theorem holds for ALL
    horizons `m` simultaneously. -/
theorem partialSumBound_of_stationarySeriesEntry_le (n : ℕ)
    (G M_inv A_inv : Fin n → Fin n → ℝ) (cA : ℝ)
    (hsum : ∀ i j, Summable
      (fun k => ∑ l : Fin n, |matPow n G k i l| * |M_inv l j|))
    (hle : ∀ i j, stationarySeriesEntry n G M_inv i j ≤ cA * |A_inv i j|)
    (m : ℕ) :
    PartialSumBound n G M_inv A_inv cA m := by
  intro i j
  calc ∑ k ∈ Finset.range (m + 1),
        ∑ l : Fin n, |matPow n G k i l| * |M_inv l j|
      ≤ stationarySeriesEntry n G M_inv i j :=
        Summable.sum_le_tsum (Finset.range (m + 1))
          (fun _ _ => Finset.sum_nonneg fun _ _ =>
            mul_nonneg (abs_nonneg _) (abs_nonneg _))
          (hsum i j)
    _ ≤ cA * |A_inv i j| := hle i j

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.2,
    eq (17.12): the set of admissible constants `c` for the literal
    componentwise series bound `Σ_{k=0}^∞ |G^k M^{-1}| ≤ c · |A^{-1}|`. -/
def CAValues (n : ℕ) (G M_inv A_inv : Fin n → Fin n → ℝ) : Set ℝ :=
  {c | 0 ≤ c ∧ ∀ i j, stationarySeriesEntry n G M_inv i j ≤ c * |A_inv i j|}

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.2,
    eq (17.12): the literal constant `c(A)` — the least admissible constant
    in the componentwise series bound, as an infimum.  Scope: `sInf` of an
    empty set is `0` in ℝ; the membership theorem `cALiteral_mem` carries the
    honest nonemptiness hypothesis. -/
noncomputable def cALiteral (n : ℕ) (G M_inv A_inv : Fin n → Fin n → ℝ) : ℝ :=
  sInf (CAValues n G M_inv A_inv)

/-- The admissible-constant set of eq (17.12) is closed: it is the
    intersection of `[0, ∞)` with finitely many closed half-line
    conditions, one per matrix entry. -/
theorem isClosed_CAValues (n : ℕ) (G M_inv A_inv : Fin n → Fin n → ℝ) :
    IsClosed (CAValues n G M_inv A_inv) := by
  have hrepr : CAValues n G M_inv A_inv =
      Set.Ici (0:ℝ) ∩ ⋂ i : Fin n, ⋂ j : Fin n,
        {c : ℝ | stationarySeriesEntry n G M_inv i j ≤ c * |A_inv i j|} := by
    ext c
    simp only [CAValues, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Ici,
      Set.mem_iInter]
  rw [hrepr]
  exact IsClosed.inter isClosed_Ici
    (isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_le continuous_const (continuous_mul_const _))

/-- **The literal `c(A)` of eq (17.12) is attained** (Higham, Accuracy and
    Stability of Numerical Algorithms, 2nd ed., §17.2, eq (17.12)): the
    infimum of the admissible constants is itself admissible, because the
    admissible set is closed, bounded below by `0`, and (by hypothesis)
    nonempty.  Scope note: nonemptiness is a genuine hypothesis — it can
    fail when some `|A^{-1}|_{ij} = 0` while the corresponding series entry
    is positive; the source implicitly assumes a finite `c(A)` exists.  A
    sufficient condition is provided by
    `CAValues_nonempty_of_entry_lower_bound`. -/
theorem cALiteral_mem (n : ℕ) (G M_inv A_inv : Fin n → Fin n → ℝ)
    (hne : (CAValues n G M_inv A_inv).Nonempty) :
    cALiteral n G M_inv A_inv ∈ CAValues n G M_inv A_inv :=
  (isClosed_CAValues n G M_inv A_inv).csInf_mem hne ⟨0, fun _ hc => hc.1⟩

/-- The attained literal `c(A)` is nonnegative. -/
theorem cALiteral_nonneg (n : ℕ) (G M_inv A_inv : Fin n → Fin n → ℝ)
    (hne : (CAValues n G M_inv A_inv).Nonempty) :
    0 ≤ cALiteral n G M_inv A_inv :=
  (cALiteral_mem n G M_inv A_inv hne).1

/-- Sufficient condition for the admissible set of eq (17.12) to be
    nonempty (Higham, Accuracy and Stability of Numerical Algorithms,
    2nd ed., §17.2, eq (17.12)): a norm certificate `‖G‖∞ ≤ q < 1` together
    with a uniform positive lower bound `δ ≤ |A^{-1}|_{ij}` on all entries.
    The witness is `c := (1 - q)⁻¹ · ‖M^{-1}‖₁ / δ`.  Scope: the entrywise
    positivity of `|A^{-1}|` is a strong (but honest) hypothesis; without
    some such majorization the set can be empty. -/
theorem CAValues_nonempty_of_entry_lower_bound (n : ℕ) (hn : 0 < n)
    (G M_inv A_inv : Fin n → Fin n → ℝ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hG : infNorm G ≤ q)
    (δ : ℝ) (hδ : 0 < δ) (hA : ∀ i j, δ ≤ |A_inv i j|) :
    (CAValues n G M_inv A_inv).Nonempty := by
  have hq' : (0:ℝ) < 1 - q := by linarith
  have hc0 : 0 ≤ (1 - q)⁻¹ * oneNorm M_inv / δ :=
    div_nonneg (mul_nonneg (inv_nonneg.mpr (le_of_lt hq')) (oneNorm_nonneg _))
      (le_of_lt hδ)
  refine ⟨(1 - q)⁻¹ * oneNorm M_inv / δ, hc0, fun i j => ?_⟩
  calc stationarySeriesEntry n G M_inv i j
      ≤ (1 - q)⁻¹ * oneNorm M_inv :=
        stationarySeriesEntry_le n hn G M_inv q hq0 hq1 hG i j
    _ = (1 - q)⁻¹ * oneNorm M_inv / δ * δ := by
        field_simp
    _ ≤ (1 - q)⁻¹ * oneNorm M_inv / δ * |A_inv i j| :=
        mul_le_mul_of_nonneg_left (hA i j) hc0

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.2,
    eq (17.12): the attained literal constant `c(A)` supplies the finite
    `PartialSumBound` certificate at EVERY horizon `m` simultaneously — the
    literal infinite statement of (17.12) specialised back to the finite
    layer. -/
theorem partialSumBound_cALiteral (n : ℕ)
    (G M_inv A_inv : Fin n → Fin n → ℝ)
    (hsum : ∀ i j, Summable
      (fun k => ∑ l : Fin n, |matPow n G k i l| * |M_inv l j|))
    (hne : (CAValues n G M_inv A_inv).Nonempty) (m : ℕ) :
    PartialSumBound n G M_inv A_inv (cALiteral n G M_inv A_inv) m :=
  partialSumBound_of_stationarySeriesEntry_le n G M_inv A_inv _ hsum
    (cALiteral_mem n G M_inv A_inv hne).2 m

end NumStability
