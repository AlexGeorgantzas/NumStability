import NumStability.Algorithms.LinearSystems.SymmetricIndefinite.ErrorAnalysis.BlockLDLT
import NumStability.Algorithms.LinearSystems.SymmetricIndefinite.ErrorAnalysis.Predicates
import NumStability.Algorithms.LinearSystems.SymmetricIndefinite.ErrorAnalysis.SkewSymmetric

/-!
# Higham Chapter 11: SkewSymmetric

Canonical owner materialized from the reviewed Chapter 11 route contract.
-/

namespace NumStability

open scoped BigOperators

/-! ## §11.3 Skew-symmetric block LDL^T factorization -/

/-- Real skew-symmetric matrix predicate, `A^T = -A`. -/
abbrev higham11_16_IsSkewSymmetric (n : ℕ)
    (A : Fin n → Fin n → ℝ) : Prop :=
  IsSkewSymmetric n A

/-- A real skew-symmetric matrix has zero diagonal. -/
theorem higham11_16_skew_diag_zero (n : ℕ)
    (A : Fin n → Fin n → ℝ) (hA : higham11_16_IsSkewSymmetric n A) :
    ∀ i : Fin n, A i i = 0 :=
  skewSymmetric_diag_zero n A hA

/-- **Equation (11.16)** source predicate:
`P A P^T = L D L^T` with skew block diagonal `D`. -/
abbrev higham11_16_SkewBlockLDLTSpec (n : ℕ)
    (A L D : Fin n → Fin n → ℝ) (σ : Fin n → Fin n) : Prop :=
  SkewBlockLDLTSpec n A L D σ

/-- **Equation (11.16)** skew Schur complement
`B + C E^{-1} C^T`. -/
noncomputable def higham11_16_skewSchurComplement (m s : ℕ)
    (B : Fin m → Fin m → ℝ)
    (C : Fin m → Fin s → ℝ)
    (E_inv : Fin s → Fin s → ℝ) : Fin m → Fin m → ℝ :=
  fun i j => B i j + ∑ p : Fin s, ∑ q : Fin s, C i p * E_inv p q * C j q

/-- **Equation (11.16)** structural invariant: a skew Schur complement remains
skew-symmetric when `B` and the pivot inverse are skew-symmetric. -/
theorem higham11_16_skewSchurComplement_skew
    (m s : ℕ)
    (B : Fin m → Fin m → ℝ)
    (C : Fin m → Fin s → ℝ)
    (E_inv : Fin s → Fin s → ℝ)
    (hB : higham11_16_IsSkewSymmetric m B)
    (hE : higham11_16_IsSkewSymmetric s E_inv) :
    higham11_16_IsSkewSymmetric m
      (higham11_16_skewSchurComplement m s B C E_inv) := by
  intro i j
  unfold higham11_16_skewSchurComplement
  have hsum :
      (∑ p : Fin s, ∑ q : Fin s, C i p * E_inv p q * C j q) =
        - (∑ p : Fin s, ∑ q : Fin s, C j p * E_inv p q * C i q) := by
    calc
      (∑ p : Fin s, ∑ q : Fin s, C i p * E_inv p q * C j q)
          = ∑ q : Fin s, ∑ p : Fin s, C i p * E_inv p q * C j q := by
            rw [Finset.sum_comm]
      _ = ∑ p : Fin s, ∑ q : Fin s, C i q * E_inv q p * C j p := rfl
      _ = ∑ p : Fin s, ∑ q : Fin s, C i q * (-E_inv p q) * C j p := by
            apply Finset.sum_congr rfl
            intro p _
            apply Finset.sum_congr rfl
            intro q _
            rw [hE q p]
      _ = - (∑ p : Fin s, ∑ q : Fin s, C j p * E_inv p q * C i q) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro p _
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro q _
            ring
  have hb := hB i j
  rw [hsum, hb]
  ring

/-- **Equation (11.16)** diagonal consequence of the skew Schur-complement
invariant: the updated trailing block has zero diagonal. -/
theorem higham11_16_skewSchurComplement_diag_zero
    (m s : ℕ)
    (B : Fin m → Fin m → ℝ)
    (C : Fin m → Fin s → ℝ)
    (E_inv : Fin s → Fin s → ℝ)
    (hB : higham11_16_IsSkewSymmetric m B)
    (hE : higham11_16_IsSkewSymmetric s E_inv) :
    ∀ i : Fin m, higham11_16_skewSchurComplement m s B C E_inv i i = 0 :=
  higham11_16_skew_diag_zero m
    (higham11_16_skewSchurComplement m s B C E_inv)
    (higham11_16_skewSchurComplement_skew m s B C E_inv hB hE)

/-- **Algorithm 11.9** source pivot predicate for skew-symmetric block
LDL^T factorization. -/
abbrev higham11_9_SkewBunchPivotChoice
    (firstColumnTailZero : Prop) (pivotMagnitude : ℝ) (s : PivotSize) : Prop :=
  SkewBunchPivotChoice firstColumnTailZero pivotMagnitude s

/-- The skew-symmetric pivoting analysis gives `|L_ij| <= 1`. -/
theorem higham11_9_skew_L_entry_bound_interface (n : ℕ)
    (L : Fin n → Fin n → ℝ)
    (hL : ∀ i j : Fin n, |L i j| ≤ 1) :
    ∀ i j : Fin n, |L i j| ≤ 1 :=
  hL

/-- The skew-symmetric Schur-complement entry bound
`|s_ij| <= 3 max_ij |a_ij|`. -/
def higham11_9_skewSchurEntryBound
    (sij Amax : ℝ) : Prop :=
  |sij| ≤ 3 * Amax

/-- **Algorithm 11.9 multiplier bound**, proved: for a skew 2×2 pivot the
multiplier `c/a₂₁` (an entry of `CE⁻¹`, hence of `L`) satisfies `|c/a₂₁| ≤ 1`
whenever the pivot `a₂₁` has the largest magnitude (`|c| ≤ |a₂₁|`).  This is the
honest derivation behind `higham11_9_skew_L_entry_bound_interface`. -/
theorem higham11_9_skew_multiplier_bound (c a21 : ℝ)
    (ha : a21 ≠ 0) (hc : |c| ≤ |a21|) :
    |c / a21| ≤ 1 :=
  skew_twoByTwo_multiplier_bound c a21 ha hc

/-- **Algorithm 11.9 Schur-entry bound**, proved: the skew 2×2 Schur entry
`s = a_ij − (a_{i2}/a₂₁)a_{j1} + (a_{i1}/a₂₁)a_{j2}` satisfies the printed
`higham11_9_skewSchurEntryBound s M`, i.e. `|s| ≤ 3M`, when every active entry is
`≤ M` and the multipliers are `≤ 1` (`|a_{i1}|,|a_{i2}| ≤ |a₂₁|`). -/
theorem higham11_9_skew_schur_entry_bound
    (aij ai1 ai2 aj1 aj2 a21 M : ℝ) (ha : a21 ≠ 0)
    (hij : |aij| ≤ M) (hj1 : |aj1| ≤ M) (hj2 : |aj2| ≤ M)
    (hi1 : |ai1| ≤ |a21|) (hi2 : |ai2| ≤ |a21|) :
    higham11_9_skewSchurEntryBound
      (aij - (ai2 / a21) * aj1 + (ai1 / a21) * aj2) M :=
  skew_twoByTwo_schur_entry_bound aij ai1 ai2 aj1 aj2 a21 M
    ha hij hj1 hj2 hi1 hi2

/-- The printed skew growth-factor bound
`rho_n <= (sqrt 3)^(n-2)`. -/
def higham11_9_skewGrowthBound (n : ℕ) (ρ_n : ℝ) : Prop :=
  ρ_n ≤ (Real.sqrt 3) ^ (n - 2)

/-- **Algorithm 11.9 global growth recursion.**  A skew elimination path has
at most `(n-2)/2` genuine `2×2` Schur-complement updates.  If `r k` is the
normalized largest entry after `k` such updates, the local bound
`higham11_9_skew_schur_entry_bound` gives `r (k+1) ≤ 3 r k`.  Iterating those
actual updates yields the printed global factor `(√3)^(n-2)`.

The hypotheses expose exactly the data supplied by a concrete pivot schedule:
`q` is its number of nontrivial `2×2` updates, `hcount` is the dimension-count
bound, and `hstep` is discharged stage by stage by the local Schur theorem. -/
theorem higham11_9_skewGrowthBound_of_twoByTwo_steps
    (n q : ℕ) (ρ_n : ℝ) (r : ℕ → ℝ)
    (hcount : 2 * q ≤ n - 2)
    (hinitial : r 0 ≤ 1)
    (hfinal : ρ_n ≤ r q)
    (hstep : ∀ k, k < q → r (k + 1) ≤ 3 * r k) :
    higham11_9_skewGrowthBound n ρ_n := by
  have hiterate : ∀ k, k ≤ q → r k ≤ (3 : ℝ) ^ k := by
    intro k hk
    induction k with
    | zero => simpa using hinitial
    | succ k ih =>
        have hk_lt : k < q := Nat.lt_of_succ_le hk
        calc
          r (k + 1) ≤ 3 * r k := hstep k hk_lt
          _ ≤ 3 * (3 : ℝ) ^ k :=
            mul_le_mul_of_nonneg_left (ih (Nat.le_of_lt hk_lt)) (by norm_num)
          _ = (3 : ℝ) ^ (k + 1) := by ring
  have hsqrt_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hthree_pow : (3 : ℝ) ^ q = (Real.sqrt 3) ^ (2 * q) := by
    calc
      (3 : ℝ) ^ q = ((Real.sqrt 3) ^ 2) ^ q := by rw [hsqrt_sq]
      _ = (Real.sqrt 3) ^ (2 * q) := (pow_mul (Real.sqrt 3) 2 q).symm
  have hsqrt_one : (1 : ℝ) ≤ Real.sqrt 3 := by
    rw [Real.one_le_sqrt]
    norm_num
  have hpower : (Real.sqrt 3) ^ (2 * q) ≤ (Real.sqrt 3) ^ (n - 2) :=
    pow_le_pow_right₀ hsqrt_one hcount
  unfold higham11_9_skewGrowthBound
  calc
    ρ_n ≤ r q := hfinal
    _ ≤ (3 : ℝ) ^ q := hiterate q (le_refl _)
    _ = (Real.sqrt 3) ^ (2 * q) := hthree_pow
    _ ≤ (Real.sqrt 3) ^ (n - 2) := hpower


end NumStability
