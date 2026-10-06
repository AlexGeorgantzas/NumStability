/-
Algorithms/Cholesky/AasenTridiagGEPPCh11Closure.lean

Chapter 11 audit, **Piece D** of the attempted faithful Theorem-11.8 (Aasen)
closure: the *middle-factor* backward-error input needed by the Aasen solve
chain.

For `P A Pᵀ = L̂ T̂ L̂ᵀ` (Aasen's method), the middle solve `T̂ y = z` for the
symmetric tridiagonal factor `T̂` must be discharged with a factorisation whose
*factor-norm growth* is controlled by `‖T̂‖∞` — **without** a diagonal-dominance
hypothesis (Aasen's `T̂` need not be diagonally dominant).

## What the printed GEPP norm argument actually requires

Higham's detailed analysis first obtains the componentwise middle perturbation
`|ΔT₁| ≤ γ₆ Πᵀ|M̂||Û|`.  The printed normwise conclusion then uses

    `‖M̂‖∞ ≤ 2`  and  `‖Û‖∞ ≤ 3 ‖T̂‖∞`.

The second inequality is valid and is proved below from the actual recursive
tridiagonal partial-pivoting trace.  The first shortcut is not valid for the
conventional accumulated lower-triangular GEPP factor.  The source observes
that `M̂` has at most one nonzero below the diagonal in each *column* and that
all multipliers are unit-bounded; this gives a column-norm bound, not the stated
infinity-norm bound.  When a later adjacent interchange is accumulated into
`M̂`, earlier multipliers can move into the same row.  The exact three-by-three
certificate `middleAccumCounter_exact_permuted_lu` in
`AasenMiddleGEPPCh11Counterexample` has

    `‖M̂‖∞ = 1 + 9/10 + 10/11 = 309/110 > 2`.

There is a second tempting replacement,

    `∀ i j, ∑ k, |M̂ i k| · |Û k j| ≤ 3 · |(Π·T̂) i j|`

but it too is false for genuine tridiagonal partial pivoting, because a row
interchange creates fill where the permuted input is zero.  Concretely, for

    T̂ = [[d0, c0, 0 ], [a1, d1, c1], [0, a2, d2]]   with |a1| > |d0|,

step 0 swaps rows 0 and 1, so after elimination `Û` acquires a second
super-diagonal entry `Û_{1,2} = -m1·c1 ≠ 0` (with multiplier `m1 = d0/a1`),
while the permuted matrix has `(Π·T̂)_{1,2} = 0` (row 1 of `Π·T̂` is the original
row 0 = `[d0, c0, 0]`).  Then

    (|M̂||Û|)_{1,2} = |m1|·|c1| + 1·|m1·c1| = 2|m1||c1| > 0 = 3·|(Π·T̂)_{1,2}|,

so the componentwise claim is violated.

The repository now has an exact recursive partial-pivoting trace, the
tridiagonal growth factor `ρ ≤ 2`, and the source-sharp upper-factor row bound
`‖Û‖∞ ≤ 3‖T̂‖∞`.  The certificate API still exposes only entrywise bounds for
the accumulated lower factor, yielding the valid but weaker reusable estimate
`‖M̂‖∞‖Û‖∞ ≤ 2n²‖T̂‖∞`.  More importantly, there is no rounded pivoted-GEPP
producer: the reusable rounded Doolittle loop performs no pivoting.  A faithful
closure therefore needs an operational adjacent-pivot/multiplier solve analysis
(the storage scheme used by tridiagonal solvers), rather than the invalid
accumulated-factor shortcut.

## Additional valid fallback: the §11.1.4 Bunch factorisation

Per the task's explicit fallback, we instead supply the middle-solve factor-norm
input from Bunch's method (Algorithm 11.6), whose factor-norm growth is
**already discharged without any dominance hypothesis** in
`BunchTridiagonalHFactorCh11Closure.hfactor_bound`:

    `higham11_4_bunchKaufmanProductEntry n L̂ D̂ i j ≤ hfactorConst fp · Amax`

(with the dimension-independent constant `c₀ = hfactorConst fp`).  Here we lift
that per-entry bound to the normwise factor-norm bound the Aasen assembly needs:

    `‖ |L̂||D̂||L̂ᵀ| ‖∞ ≤ (n · c₀) · ‖T̂‖∞`   (no dominance),

This is a useful dominance-free alternative factorization bound.  Its order-`n`
coefficient does not, however, fit the printed `γ_(15n+25)` radius, so it is not
advertised as a closure of Theorem 11.8.

No `sorry`/`admit`/`axiom`/`native_decide`; everything below is derived from the
already-closed Bunch factor-norm bound and the `infNorm` row-sum machinery.
-/
import NumStability.Algorithms.Cholesky.AasenGrowthCh11Closure
import NumStability.Algorithms.Cholesky.BunchTridiagonalHFactorCh11Closure

open scoped BigOperators

namespace NumStability.Ch11Closure.AasenDirect

open NumStability
open NumStability.Ch11Closure
open NumStability.Ch11Closure.Mixed
open NumStability.Ch11Closure.HFactor

/-- The nonnegative absolute Bunch factor-product matrix `|L̂||D̂||L̂ᵀ|` of the
Algorithm-11.6 factorisation of `T̂` recorded by the pivot schedule `s`.  This is
the middle-factor "factor norm" whose growth the Aasen solve chain must bound. -/
noncomputable def bunchAbsFactorProduct (fp : FPModel) {n : ℕ}
    (s : PivotSchedule n) (T : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j =>
    higham11_4_bunchKaufmanProductEntry n (flMixedL fp s T) (flMixedD fp s T) i j

/-- Every entry of the Bunch factor-product matrix is nonnegative. -/
theorem bunchAbsFactorProduct_nonneg (fp : FPModel) {n : ℕ}
    (s : PivotSchedule n) (T : Fin n → Fin n → ℝ) (i j : Fin n) :
    0 ≤ bunchAbsFactorProduct fp s T i j :=
  higham11_4_bunchKaufmanProductEntry_nonneg n
    (flMixedL fp s T) (flMixedD fp s T) i j

/-- **Piece D — Bunch middle-solve factor-norm bound (no dominance).**

For a symmetric tridiagonal `T̂` whose Algorithm-11.6 (Bunch) mixed-pivot run is
recorded by the schedule `s` with per-stage pivot data `TriPivotData` and local
scales bounded by `Amax`, the factor norm of the computed Bunch factorisation
obeys

    `‖ |L̂||D̂||L̂ᵀ| ‖∞ ≤ (n · c₀) · Amax`,   `c₀ = hfactorConst fp`,

with **no** diagonal-dominance hypothesis.  This is the middle-factor growth
input the Aasen solve chain needs; the dominance-free constant comes from the
already-closed per-entry bound `hfactor_bound`, lifted here to the normwise
`infNorm` via the row-sum count `n`. -/
theorem bunch_tridiag_absFactor_infNorm_le
    (fp : FPModel) (hval : gammaValid fp 3)
    {n : ℕ} (T : Fin n → Fin n → ℝ) (s : PivotSchedule n)
    (Amax : ℝ) (hAmax0 : 0 ≤ Amax)
    (hdata : TriPivotData fp Amax s T) :
    infNorm (bunchAbsFactorProduct fp s T) ≤ (n : ℝ) * hfactorConst fp * Amax := by
  have hentry :
      ∀ i j : Fin n, bunchAbsFactorProduct fp s T i j ≤ hfactorConst fp * Amax :=
    hfactor_bound fp hval Amax hAmax0 s T hdata
  apply infNorm_le_of_row_sum_le
  · intro i
    calc ∑ j : Fin n, |bunchAbsFactorProduct fp s T i j|
        = ∑ j : Fin n, bunchAbsFactorProduct fp s T i j :=
          Finset.sum_congr rfl
            (fun j _ => abs_of_nonneg (bunchAbsFactorProduct_nonneg fp s T i j))
      _ ≤ ∑ _j : Fin n, hfactorConst fp * Amax :=
          Finset.sum_le_sum (fun j _ => hentry i j)
      _ = (n : ℝ) * hfactorConst fp * Amax := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (hfactorConst_nonneg fp hval)) hAmax0

/-- **Piece D — Bunch middle-solve factor-norm bound in terms of `‖T̂‖∞`.**

Specialising the local scale to `Amax = ‖T̂‖∞` (a legitimate global bound, since
`|T̂ i j| ≤ ‖T̂‖∞`), the Bunch factor norm is controlled by `‖T̂‖∞`:

    `‖ |L̂||D̂||L̂ᵀ| ‖∞ ≤ (n · c₀) · ‖T̂‖∞`.

This is the `‖ |factors| ‖∞ ≤ c · ‖T̂‖∞` input requested by the Aasen assembly. -/
theorem bunch_tridiag_absFactor_infNorm_le_infNorm
    (fp : FPModel) (hval : gammaValid fp 3)
    {n : ℕ} (T : Fin n → Fin n → ℝ) (s : PivotSchedule n)
    (hdata : TriPivotData fp (infNorm T) s T) :
    infNorm (bunchAbsFactorProduct fp s T) ≤ ((n : ℝ) * hfactorConst fp) * infNorm T := by
  have h := bunch_tridiag_absFactor_infNorm_le fp hval T s (infNorm T)
    (infNorm_nonneg T) hdata
  -- `(n:ℝ) * c₀ * ‖T̂‖∞` and `((n:ℝ) * c₀) * ‖T̂‖∞` are the same term.
  simpa [mul_assoc] using h

/-- Matrix-product (`matMul`/`absMatrix`) restatement of the Bunch factor-norm
bound, matching the `|L̂||D̂||L̂ᵀ|` product form consumed by the Aasen
middle-solve budget machinery.  The two product matrices agree entrywise
(`higham11_4_bunchKaufmanProductEntry_eq_absLDLTProduct`), hence share an
`infNorm`. -/
theorem bunch_tridiag_absLDLTProduct_infNorm_le
    (fp : FPModel) (hval : gammaValid fp 3)
    {n : ℕ} (T : Fin n → Fin n → ℝ) (s : PivotSchedule n)
    (Amax : ℝ) (hAmax0 : 0 ≤ Amax)
    (hdata : TriPivotData fp Amax s T) :
    infNorm (higham11_4_absLDLTProduct n (flMixedL fp s T) (flMixedD fp s T)) ≤
      (n : ℝ) * hfactorConst fp * Amax := by
  have heq :
      higham11_4_absLDLTProduct n (flMixedL fp s T) (flMixedD fp s T) =
        bunchAbsFactorProduct fp s T := by
    funext i j
    exact
      (higham11_4_bunchKaufmanProductEntry_eq_absLDLTProduct n
        (flMixedL fp s T) (flMixedD fp s T) i j).symm
  rw [heq]
  exact bunch_tridiag_absFactor_infNorm_le fp hval T s Amax hAmax0 hdata

/-! ### Source-sharp upper-factor row bound for tridiagonal GEPP

The detailed proof behind Higham's Theorem 11.8 uses the special tridiagonal
GEPP estimate `‖Û‖∞ ≤ 3 ‖T̂‖∞`.  A max-entry growth estimate alone loses an
extra factor: the sharp row bound also uses that the pivot row of every active
tridiagonal stage has at most three entries.  The Chapter-9 active-stage
invariant already records exactly the facts needed for that row count.
-/

private theorem tridiag_active_row_zero_sum_le_three_mul
    {m : ℕ} {S : Fin (m + 1) → Fin (m + 1) → ℝ} {M : ℝ}
    (hM : 0 ≤ M)
    (hS : higham9_11_TridiagActiveBound (m + 1) M S) :
    (∑ j : Fin (m + 1), |S 0 j|) ≤ 3 * M := by
  cases m with
  | zero =>
      have h := hS.2.1 (0 : Fin 1) (0 : Fin 1) rfl rfl
      have h23 : 2 * M ≤ 3 * M := by linarith
      rw [Fin.sum_univ_one]
      exact le_trans h h23
  | succ k =>
      rw [Fin.sum_univ_succ]
      have h00 : |S (0 : Fin (k + 2)) 0| ≤ 2 * M :=
        hS.2.1 0 0 rfl rfl
      have htail : (∑ j : Fin (k + 1), |S 0 j.succ|) ≤ M := by
        cases k with
        | zero =>
            simpa using hS.2.2 (0 : Fin 2) (1 : Fin 2) (by simp)
        | succ l =>
            rw [Fin.sum_univ_succ]
            have hrest : (∑ j : Fin (l + 1), |S 0 j.succ.succ|) = 0 := by
              apply Finset.sum_eq_zero
              intro j _
              rw [hS.1 0 j.succ.succ]
              · simp
              · left
                simp
            rw [hrest, add_zero]
            exact hS.2.2 (0 : Fin (l + 3)) (1 : Fin (l + 3)) (by simp)
      linarith

private theorem tridiag_active_row_one_sum_le_three_mul
    {m : ℕ} {S : Fin (m + 2) → Fin (m + 2) → ℝ} {M : ℝ}
    (hM : 0 ≤ M)
    (hS : higham9_11_TridiagActiveBound (m + 2) M S) :
    (∑ j : Fin (m + 2), |S 1 j|) ≤ 3 * M := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  have h0 : |S (1 : Fin (m + 2)) 0| ≤ M := hS.2.2 1 0 (by simp)
  have h1 : |S (1 : Fin (m + 2)) 1| ≤ M := hS.2.2 1 1 (by simp)
  cases m with
  | zero =>
      simp
      linarith
  | succ l =>
      rw [Fin.sum_univ_succ]
      have h2 : |S (1 : Fin (l + 3)) 2| ≤ M := hS.2.2 1 2 (by simp)
      have hrest : (∑ j : Fin l, |S 1 j.succ.succ.succ|) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        rw [hS.1 1 j.succ.succ.succ]
        · simp
        · left
          simp
      rw [hrest]
      simp only [add_zero]
      norm_num at h0 h1 h2 ⊢
      linarith

/-- Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
Theorem 11.8 proof (and Higham's detailed symmetric-indefinite analysis,
Theorem 3.6): every row exposed by an exact tridiagonal GEPP trace has absolute
row sum at most three times the original active-stage scale.

Unlike the coarser max-entry conversion, this proof follows the actual pivot
row through the recursive trace.  A tridiagonal first-column pivot is in row
zero or one; its exposed row therefore contains at most two or three nonzeros,
respectively. -/
theorem tridiag_GEPPUTrace_row_sum_le_three_mul :
    ∀ {n : ℕ} {A U : Fin n → Fin n → ℝ},
      higham9_7_PartialPivotGEPPUTrace n A U →
      ∀ M : ℝ, 0 ≤ M →
        higham9_11_TridiagActiveBound n M A →
        ∀ i : Fin n, (∑ j : Fin n, |U i j|) ≤ 3 * M := by
  intro n A U htrace
  induction htrace with
  | done =>
      intro M _hM _hA i
      exact Fin.elim0 i
  | step hchoice hpivot hnext ih =>
      rename_i m A r U₁
      intro M hM hA i
      let sigma := higham9_7_firstPivotRowSwap r
      let Aperm := higham9_2_rowPermutedMatrix A sigma
      have htail :=
        higham9_11_tridiagActive_schur_preserved hM hA hchoice hpivot
      by_cases hi : i = 0
      · subst i
        have hr : r.val ≤ 1 :=
          higham9_11_tridiag_pivot_val_le_one hA.1 hpivot
        have hrow : (∑ j : Fin (m + 1), |A r j|) ≤ 3 * M := by
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hr with hr0 | hr1
          · have hre : r = 0 := Fin.ext hr0
            subst r
            exact tridiag_active_row_zero_sum_le_three_mul hM hA
          · cases m with
            | zero =>
                have : r.val = 0 := by omega
                omega
            | succ k =>
                have hre : r = (1 : Fin (k + 2)) := Fin.ext hr1
                subst r
                exact tridiag_active_row_one_sum_le_three_mul hM hA
        simpa [luFirstStepU, Aperm, sigma, higham9_2_rowPermutedMatrix,
          higham9_7_firstPivotRowSwap] using hrow
      · have hrec := ih M hM htail (i.pred hi)
        rw [Fin.sum_univ_succ]
        simpa [luFirstStepU, hi] using hrec

/-- Higham Theorem 11.8's source-sharp tridiagonal-GEPP upper-factor estimate:

`‖Û‖∞ ≤ 3 ‖T̂‖∞`.

This is obtained from the actual recursive partial-pivoting trace and the
Chapter-9 tridiagonal active-stage invariant, with no free growth or support
hypothesis. -/
theorem tridiag_GEPPUTrace_infNorm_le_three_mul_infNorm
    {n : ℕ} (T U : Fin n → Fin n → ℝ)
    (hTri : IsTridiagonal n T)
    (htrace : higham9_7_PartialPivotGEPPUTrace n T U) :
    infNorm U ≤ 3 * infNorm T := by
  have hactive : higham9_11_TridiagActiveBound n (infNorm T) T := by
    refine ⟨hTri, ?_, ?_⟩
    · intro i j _hi _hj
      have hentry : |T i j| ≤ infNorm T := by
        calc
          |T i j| ≤ ∑ k : Fin n, |T i k| :=
            Finset.single_le_sum (fun k _ => abs_nonneg (T i k))
              (Finset.mem_univ j)
          _ ≤ infNorm T := row_sum_le_infNorm T i
      have hnonneg := infNorm_nonneg T
      linarith
    · intro i j _hij
      calc
        |T i j| ≤ ∑ k : Fin n, |T i k| :=
          Finset.single_le_sum (fun k _ => abs_nonneg (T i k))
            (Finset.mem_univ j)
        _ ≤ infNorm T := row_sum_le_infNorm T i
  apply infNorm_le_of_row_sum_le
  · exact tridiag_GEPPUTrace_row_sum_le_three_mul htrace
      (infNorm T) (infNorm_nonneg T) hactive
  · exact mul_nonneg (by norm_num) (infNorm_nonneg T)

/-! ### Exact tridiagonal-GEPP factor-norm consequence

The Chapter-9 trace now proves the source growth fact `max |U| ≤ 2 max |T|`
and constructs an exact permuted `LU` certificate with `|L i j| ≤ 1`.  The
available certificate API does not yet expose the sharper band support of the
factors, so converting both max-entry estimates to row-sum norms costs two
factors of `n`. -/

/-- **Unconditional exact-GEPP factor-norm bound available from the current
trace API.**  Every exact partial-pivoting trace for a tridiagonal `T` supplies
permuted factors with

    `‖L‖∞ ‖U‖∞ ≤ 2 n² ‖T‖∞`.

This is derived only from the actual GEPP trace, its unit multiplier bound, and
the proved tridiagonal growth factor `rho ≤ 2`; it is not a target-scale
hypothesis.  It records the strongest bound exposed by those reusable APIs.
The coefficient is too large to replace the coefficient-one hypothesis in the
linear-radius Theorem-11.8 wrapper. -/
theorem tridiag_GEPP_exists_factor_infNorm_product_le_two_n_sq
    {n : ℕ} (hn : 0 < n) (T Utrace : Fin n → Fin n → ℝ)
    (hTri : IsTridiagonal n T)
    (htrace : higham9_7_PartialPivotGEPPUTrace n T Utrace) :
    ∃ L U : Fin n → Fin n → ℝ, ∃ sigma : Fin n → Fin n,
      higham9_2_PermutedLUFactSpec n T L U sigma ∧
      (∀ i j : Fin n, |L i j| ≤ 1) ∧
      infNorm L * infNorm U ≤
        (2 * (n : ℝ) ^ 2) * infNorm T := by
  obtain ⟨L, U, sigma, hLU, hLentry, hUtrace⟩ :=
    higham9_7_PartialPivotGEPPUTrace_exists_PermutedLUFactSpec_L_bound_maxEntryNorm_le
      htrace
  refine ⟨L, U, sigma, hLU, hLentry, ?_⟩
  have hcast_nonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hLnorm : infNorm L ≤ (n : ℝ) := by
    apply infNorm_le_of_row_sum_le
    · intro i
      calc
        ∑ j : Fin n, |L i j| ≤ ∑ _j : Fin n, (1 : ℝ) := by
          exact Finset.sum_le_sum (fun j _ => hLentry i j)
        _ = (n : ℝ) := by simp
    · exact hcast_nonneg
  have htraceMax : maxEntryNorm hn Utrace ≤ 2 * maxEntryNorm hn T := by
    apply maxEntryNorm_le_of_entry_le_bound
    intro i j
    exact higham9_11_tridiag_GEPPUTrace_entry_abs_le_two_mul hn T Utrace
      hTri htrace i j
  have hUnorm : infNorm U ≤ (n : ℝ) * (2 * infNorm T) := by
    calc
      infNorm U ≤ (n : ℝ) * maxEntryNorm hn U :=
        infNorm_le_card_mul_maxEntryNorm hn U
      _ ≤ (n : ℝ) * maxEntryNorm hn Utrace :=
        mul_le_mul_of_nonneg_left (hUtrace hn) hcast_nonneg
      _ ≤ (n : ℝ) * (2 * maxEntryNorm hn T) :=
        mul_le_mul_of_nonneg_left htraceMax hcast_nonneg
      _ ≤ (n : ℝ) * (2 * infNorm T) := by
        gcongr
        exact maxEntryNorm_le_infNorm hn T
  calc
    infNorm L * infNorm U
        ≤ (n : ℝ) * ((n : ℝ) * (2 * infNorm T)) :=
          mul_le_mul hLnorm hUnorm (infNorm_nonneg U) hcast_nonneg
    _ = (2 * (n : ℝ) ^ 2) * infNorm T := by ring

end NumStability.Ch11Closure.AasenDirect
