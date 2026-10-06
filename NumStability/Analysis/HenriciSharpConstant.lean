/-
Analysis/HenriciSharpConstant.lean

**Toward Henrici's SHARP departure-from-normality constant** (Higham, *Accuracy
and Stability of Numerical Algorithms*, 2nd ed., §18.1, p. 345).

Higham states the *sharp* Henrici bound (squared form)
```
      Δ_F(A)² = ‖N‖_F² ≤ ( (n³−n)/12 )^{1/2} · ‖A*A − A A*‖_F ,        (Henrici★)
```
with the SHARP constant `((n³−n)/12)^{1/2}` (Henrici 1962; Eberlein).  The
companion file `HenriciExtremal.lean` proves the *shape* of this inequality with
the explicit but non-sharp constant `cₙ = Σ_{m=1}^{n-1} √m`, obtained by
bounding each block mass `Bₘ ≤ √m·‖C‖_F` separately and summing.

This file IMPROVES that constant by replacing the term-by-term block-mass
Cauchy–Schwarz with a single **global, trace-weighted Cauchy–Schwarz** applied
to the `n` real diagonal entries `dᵢ = commDiagRe T i` of the self-commutator.
The pivot is an exact reindexing identity (Fubini across the cut index `m`):
```
      Σ_{m ∈ range n} Bₘ  =  − Σ_i (n−1−i)·dᵢ ,
```
so that one Cauchy–Schwarz over the *whole* diagonal gives
```
      ‖N‖_F² ≤ Σ_{m} Bₘ = −Σ_i (n−1−i) dᵢ
              ≤ ( Σ_{i} (n−1−i)² )^{1/2} · ( Σ_i dᵢ² )^{1/2}
              ≤ ( Σ_{k∈range n} k² )^{1/2} · ‖C‖_F .
```

--------------------------------------------------------------------------------
WHAT THIS FILE PROVES (all unconditional over `ℂ`, IMPORT-ONLY, reusing the
`selfComm / frobSq / blockMass / commDiagRe / frobNormC` machinery of
`HenriciExtremal.lean`).

Let `T` be upper-triangular with strict-upper part `N`, `C = selfComm T`.

1. **Reindexing identity** (`sum_blockMass_eq_neg_weighted_diag`):
   ```
        Σ_{m ∈ range n} blockMass T m  =  − Σ i, (n − 1 − i.val)·commDiagRe T i.
   ```
   A clean Fubini swap of the double sum `Σ_m Σ_{i<m}` using the
   telescoping identity `Σ_{i<m} dᵢ = −Bₘ` of `HenriciExtremal.lean`.

2. **Global trace-weighted Cauchy–Schwarz** (`sum_blockMass_le_sharpWeight`):
   ```
        Σ_{m ∈ range n} blockMass T m  ≤  ( Σ_{k∈range n} k² )^{1/2} · ‖C‖_F .
   ```

3. **Improved Henrici constant** (`henriciSharpConst`, `henriciSharpConst_eq_closedForm`):
   `Kₙ = ( Σ_{k∈range n} (k:ℝ)² )^{1/2}`, with the closed form
   `Σ_{k∈range n} k² = (n−1)·n·(2n−1)/6`, so `Kₙ = ((n−1)n(2n−1)/6)^{1/2}`.

4. **Improved Henrici inequality** (`henrici_frobSq_le_sharp`,
   `henrici_departure_le_sharp_of_schur`):
   ```
        ‖N‖_F²  ≤  Kₙ · ‖Tᴴ T − T Tᴴ‖_F ,      and (via the Schur form)
        Δ_F(A)² ≤  Kₙ · ‖Aᴴ A − A Aᴴ‖_F .
   ```

5. **The improvement is real** (`henriciSharpConst_le_henriciConst`):
   `Kₙ ≤ cₙ = Σ_{m<n} √m` for all `n` — the new constant is never worse than the
   `HenriciExtremal.lean` one, and is strictly smaller for `n ≥ 3`
   (leading order `√(n³/3) ≈ 0.577·n^{3/2}` versus `(2/3)·n^{3/2} ≈ 0.667·n^{3/2}`).

HONESTY LEDGER.
* Items 1–5 are UNCONDITIONAL theorems; the route is elementary (telescoping +
  Fubini + one global Cauchy–Schwarz + `Σ dᵢ² ≤ frobSq C`).  No hypothesis
  smuggles the conclusion.
* `Kₙ = ((n−1)n(2n−1)/6)^{1/2}` is STILL NOT Higham's sharp constant
  `((n³−n)/12)^{1/2} = ((n−1)n(n+1)/12)^{1/2}`.  The ratio is
  `Kₙ / sharp = ( 2(2n−1)/(n+1) )^{1/2} → 2` as `n → ∞`: the global
  Cauchy–Schwarz is a bounded factor (`≤ 2`) above sharp, because (a) it uses
  the *linear* weights `(n−1−i)` rather than the true extremal weights, (b) it
  discards the off-diagonal Frobenius mass of `C` in `Σ dᵢ² ≤ frobSq C`, and
  (c) it inflates `‖N‖_F² = Σ_{i<j}|Tᵢⱼ|²` to the weighted `Σ_{i<j}(j−i)|Tᵢⱼ|²`.
  Attaining the sharp constant requires solving the Henrici/Eberlein variational
  extremum `max ‖N‖_F² / ‖C‖_F` (a structured-quadratic-form eigenvalue problem),
  which is beyond the elementary route here and the current Mathlib API.  This
  file therefore delivers a *concrete, closed-form, strictly improved* constant
  and documents precisely the residual factor to the sharp value.

Reference: N. J. Higham, *ASNA* 2nd ed., §18.1, p. 345 (Henrici display,
sharp constant `((n³−n)/12)^{1/2}`).
-/

import NumStability.Analysis.HenriciExtremal
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Sqrt

open scoped BigOperators Matrix
open Matrix Complex

namespace NumStability

variable {n : ℕ}

/-! ### Reindexing: the summed block mass as a single weighted diagonal sum -/

/-- **Fubini reindexing of the summed block mass.**  Summing the telescoping
identity `Σ_{i.val < m} commDiagRe T i = − blockMass T m` over the cut index
`m ∈ range n` and swapping the order of summation, the coefficient of each
`commDiagRe T i` is `#{ m ∈ range n : i.val < m } = n − 1 − i.val`.  Hence
```
      Σ_{m ∈ range n} blockMass T m  =  − Σ i, (n − 1 − i.val) · commDiagRe T i.
```
Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345. -/
lemma sum_blockMass_eq_neg_weighted_diag (T : Matrix (Fin n) (Fin n) ℂ)
    (hTtri : ∀ i j, j < i → T i j = 0) :
    (∑ m ∈ Finset.range n, blockMass T m)
      = - ∑ i, ((n - 1 - i.val : ℕ) : ℝ) * commDiagRe T i := by
  classical
  -- Per-`i` cardinality identity used throughout.
  have hcard : ∀ i : Fin n, ((Finset.range n).filter (fun m => i.val < m)).card
      = n - 1 - i.val := by
    intro i
    have hset : (Finset.range n).filter (fun m => i.val < m)
        = Finset.Ico (i.val + 1) n := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [hset, Nat.card_Ico]; omega
  -- Step 1: rewrite each blockMass as the partial-trace expression.
  have hstep : (∑ m ∈ Finset.range n, blockMass T m)
      = ∑ m ∈ Finset.range n,
          ∑ i, (if i.val < m then (- commDiagRe T i) else 0) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    have h := partialTrace_eq_neg_blockMass T hTtri m
    rw [Finset.sum_filter] at h
    -- h : ∑ i, (if i.val < m then commDiagRe T i else 0) = - blockMass T m
    have h2 : (∑ i, (if i.val < m then (- commDiagRe T i) else 0))
        = - ∑ i, (if i.val < m then commDiagRe T i else 0) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hc : i.val < m <;> simp [hc]
    rw [h2, h, neg_neg]
  rw [hstep, Finset.sum_comm]
  -- Step 2: match termwise in `i`, summing the indicator over the cuts `m`.
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcard i]
  ring

/-! ### The global trace-weighted Cauchy–Schwarz bound -/

/-- **Global Cauchy–Schwarz bound on the summed block mass.**  With
`wᵢ = n − 1 − i.val`, one Cauchy–Schwarz on the reindexed sum gives
```
      Σ_{m ∈ range n} blockMass T m  ≤  ( Σ_i wᵢ² )^{1/2} · frobNormC (selfComm T),
```
using `Σ_i (commDiagRe T i)² ≤ frobSq (selfComm T)`.  Because the left side is a
sum of nonnegative block masses, the absolute value in Cauchy–Schwarz is not
needed.  Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345. -/
lemma sum_blockMass_le_sharpWeight (T : Matrix (Fin n) (Fin n) ℂ)
    (hTtri : ∀ i j, j < i → T i j = 0) :
    (∑ m ∈ Finset.range n, blockMass T m)
      ≤ Real.sqrt (∑ i : Fin n, ((n - 1 - i.val : ℕ) : ℝ) ^ 2) * frobNormC (selfComm T) := by
  classical
  set w : Fin n → ℝ := fun i => ((n - 1 - i.val : ℕ) : ℝ) with hw
  set d : Fin n → ℝ := fun i => commDiagRe T i with hd
  -- The summed block mass equals −Σ wᵢ dᵢ ≤ |Σ wᵢ dᵢ| ≤ √(Σwᵢ²)·√(Σdᵢ²).
  have hEq : (∑ m ∈ Finset.range n, blockMass T m) = - ∑ i, w i * d i :=
    sum_blockMass_eq_neg_weighted_diag T hTtri
  -- Cauchy–Schwarz: (Σ wᵢ dᵢ)² ≤ (Σ wᵢ²)(Σ dᵢ²).
  have hcs : (∑ i, w i * d i) ^ 2 ≤ (∑ i, (w i) ^ 2) * (∑ i, (d i) ^ 2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n)) w d
    simpa using h
  -- Σ dᵢ² ≤ frobSq C.
  have hd_le : (∑ i, (d i) ^ 2) ≤ frobSq (selfComm T) :=
    sum_commDiagRe_sq_le_frobSq T
  have hw_nonneg : 0 ≤ ∑ i, (w i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hd_nonneg : 0 ≤ ∑ i, (d i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  -- (Σ wᵢ dᵢ)² ≤ (Σwᵢ²)·frobSq C.
  have hsq : (∑ i, w i * d i) ^ 2 ≤ (∑ i, (w i) ^ 2) * frobSq (selfComm T) := by
    refine le_trans hcs ?_
    exact mul_le_mul_of_nonneg_left hd_le hw_nonneg
  -- The LHS is nonnegative (sum of nonneg block masses), so LHS = √(LHS²) ≤ √RHS.
  have hLHS_nonneg : 0 ≤ ∑ m ∈ Finset.range n, blockMass T m :=
    Finset.sum_nonneg fun m _ => blockMass_nonneg T m
  -- LHS = -Σwᵢdᵢ, and (Σwᵢdᵢ)² = (LHS)², so LHS ≤ |Σwᵢdᵢ| = √((Σwᵢdᵢ)²).
  have hLHS_sq : (∑ m ∈ Finset.range n, blockMass T m) ^ 2 = (∑ i, w i * d i) ^ 2 := by
    rw [hEq, neg_sq]
  have hchain : (∑ m ∈ Finset.range n, blockMass T m) ^ 2
      ≤ (∑ i, (w i) ^ 2) * frobSq (selfComm T) := by
    rw [hLHS_sq]; exact hsq
  calc (∑ m ∈ Finset.range n, blockMass T m)
      = Real.sqrt ((∑ m ∈ Finset.range n, blockMass T m) ^ 2) := by
        rw [Real.sqrt_sq hLHS_nonneg]
    _ ≤ Real.sqrt ((∑ i, (w i) ^ 2) * frobSq (selfComm T)) := Real.sqrt_le_sqrt hchain
    _ = Real.sqrt (∑ i, (w i) ^ 2) * frobNormC (selfComm T) := by
        rw [Real.sqrt_mul hw_nonneg]; rfl

/-! ### The improved Henrici constant and its closed form -/

/-- **The improved (still non-sharp) Henrici constant**
`Kₙ = ( Σ_{i} (n − 1 − i.val)² )^{1/2} = ( Σ_{k ∈ range n} k² )^{1/2}`, obtained
from the global trace-weighted Cauchy–Schwarz.  Its closed form is
`((n−1)n(2n−1)/6)^{1/2}` (see `henriciSharpConst_eq_closedForm`).  Higham's SHARP
constant is `((n³−n)/12)^{1/2}`; `henriciSharpConst` improves the
`HenriciExtremal.henriciConst` value `Σ_{m<n}√m` (see the header ledger).
Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345. -/
noncomputable def henriciSharpConst (n : ℕ) : ℝ :=
  Real.sqrt (∑ k ∈ Finset.range n, (k : ℝ) ^ 2)

/-- `henriciSharpConst n ≥ 0`. -/
lemma henriciSharpConst_nonneg (n : ℕ) : 0 ≤ henriciSharpConst n :=
  Real.sqrt_nonneg _

/-- The weight sum `Σ_i (n − 1 − i.val)²` (indexed over `Fin n`) equals the plain
`Σ_{k ∈ range n} k²`: the map `i ↦ n − 1 − i.val` permutes `range n`.
Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345. -/
lemma sum_weight_sq_eq_sum_range_sq (n : ℕ) :
    (∑ i : Fin n, ((n - 1 - i.val : ℕ) : ℝ) ^ 2) = ∑ k ∈ Finset.range n, (k : ℝ) ^ 2 := by
  classical
  -- Convert the Fin-sum to a range-sum, then reflect k ↦ n-1-k.
  rw [Fin.sum_univ_eq_sum_range (fun k => ((n - 1 - k : ℕ) : ℝ) ^ 2) n]
  exact Finset.sum_range_reflect (fun k => ((k : ℕ) : ℝ) ^ 2) n

/-- **Closed form of the improved constant.**
`Σ_{k ∈ range n} k² = (n−1)·n·(2n−1)/6`, hence
`henriciSharpConst n = ((n−1)·n·(2n−1)/6)^{1/2}`.
Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345 (cf. the combinatorial sum
`Σ (j−i)² = (n³−n)/12` behind the sharp constant). -/
lemma sum_range_sq_closedForm (n : ℕ) :
    (∑ k ∈ Finset.range n, (k : ℝ) ^ 2)
      = ((n : ℝ) - 1) * n * (2 * n - 1) / 6 := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- Closed form for the constant itself. -/
lemma henriciSharpConst_eq_closedForm (n : ℕ) :
    henriciSharpConst n = Real.sqrt (((n : ℝ) - 1) * n * (2 * n - 1) / 6) := by
  unfold henriciSharpConst
  rw [sum_range_sq_closedForm]

/-! ### The improved Henrici inequality -/

/-- **Henrici's departure-from-normality inequality with the improved constant.**
For upper-triangular `T` with strict-upper part `N`,
```
      ‖N‖_F²  ≤  henriciSharpConst n · ‖Tᴴ T − T Tᴴ‖_F .
```
Proof: `‖N‖_F² ≤ Σ_m blockMass T m` (`frobSq_strictUpper_le_sum_blockMass`), and
`Σ_m blockMass T m ≤ Kₙ · ‖C‖_F` by the global trace-weighted Cauchy–Schwarz
(`sum_blockMass_le_sharpWeight`), after rewriting the weight sum
(`sum_weight_sq_eq_sum_range_sq`).  This is Higham's Henrici display with the
concrete improved constant `Kₙ = ((n−1)n(2n−1)/6)^{1/2}` in place of the sharp
`((n³−n)/12)^{1/2}`.  Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345. -/
theorem henrici_frobSq_le_sharp (T N : Matrix (Fin n) (Fin n) ℂ)
    (hTtri : ∀ i j, j < i → T i j = 0)
    (hN : ∀ i j, N i j = if j > i then T i j else 0) :
    frobSq N ≤ henriciSharpConst n * frobNormC (selfComm T) := by
  have h1 : frobSq N ≤ ∑ m ∈ Finset.range n, blockMass T m :=
    frobSq_strictUpper_le_sum_blockMass T N hN
  have h2 : (∑ m ∈ Finset.range n, blockMass T m)
      ≤ Real.sqrt (∑ i : Fin n, ((n - 1 - i.val : ℕ) : ℝ) ^ 2) * frobNormC (selfComm T) :=
    sum_blockMass_le_sharpWeight T hTtri
  have h3 : Real.sqrt (∑ i : Fin n, ((n - 1 - i.val : ℕ) : ℝ) ^ 2)
      = henriciSharpConst n := by
    unfold henriciSharpConst; rw [sum_weight_sq_eq_sum_range_sq]
  rw [h3] at h2
  exact le_trans h1 h2

/-- **The improved Henrici inequality transported to `A` via its Schur form.**
If `Uᴴ A U = T = D + N` is a Schur form of `A`, then
```
      Δ_F(A)² = frobSq N  ≤  henriciSharpConst n · ‖Aᴴ A − A Aᴴ‖_F ,
```
the commutator norm being the unitarily invariant Frobenius norm of
`Aᴴ A − A Aᴴ` (`frobNormC_selfComm_unitary_conj`).  Reference: Higham, *ASNA*
2nd ed., §18.1, p. 345. -/
theorem henrici_departure_le_sharp_of_schur
    (A U T N : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hUeq : Uᴴ * A * U = T)
    (hTtri : ∀ i j, j < i → T i j = 0)
    (hN : ∀ i j, N i j = if j > i then T i j else 0) :
    departureFSq N ≤ henriciSharpConst n * frobNormC (selfComm A) := by
  rw [departureFSq_eq]
  have hbase := henrici_frobSq_le_sharp T N hTtri hN
  rw [← hUeq, frobNormC_selfComm_unitary_conj A U hU] at hbase
  exact hbase

/-! ### The improvement over the `HenriciExtremal.lean` constant -/

/-- Gauss's sum `Σ_{m ∈ range n} m = n(n−1)/2` over `ℝ`.
Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345 (auxiliary combinatorial sum). -/
lemma sum_range_id_real (n : ℕ) :
    (∑ m ∈ Finset.range n, (m : ℝ)) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- **Lower bound for the partial `√`-sum via concavity of `√`.**
For every `n`, `Real.sqrt (n - 1) * n / 2 ≤ Σ_{m ∈ range n} √m`.  Proof: the chord
bound `m ≤ √m · √(n−1)` for `m ≤ n−1` (equivalently `m² ≤ m·(n−1)`, i.e.
concavity of `√`) gives, after dividing by `√(n−1)`, the termwise estimate
`m / √(n−1) ≤ √m`; summing `Σ_{m<n} m = n(n−1)/2` yields the claim.
Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345 (auxiliary comparison). -/
lemma sqrt_sum_ge_half (n : ℕ) :
    Real.sqrt ((n : ℝ) - 1) * n / 2 ≤ ∑ m ∈ Finset.range n, Real.sqrt m := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · simp
    · simp
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hsqrt_pos : 0 < Real.sqrt ((n : ℝ) - 1) :=
      Real.sqrt_pos.mpr (by linarith)
    have hterm : ∀ m ∈ Finset.range n,
        (m : ℝ) / Real.sqrt ((n : ℝ) - 1) ≤ Real.sqrt m := by
      intro m hm
      rw [Finset.mem_range] at hm
      have hmn1 : (m : ℝ) ≤ (n : ℝ) - 1 := by
        have : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hm
        linarith
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hkey : (m : ℝ) ≤ Real.sqrt m * Real.sqrt ((n : ℝ) - 1) := by
        rw [← Real.sqrt_mul hm0]
        -- m ≤ √(m·(n−1)):  let s = √(m·(n−1)); s ≥ 0, s² = m·(n−1) ≥ m² ; so m ≤ s.
        have hrad : (0 : ℝ) ≤ (m : ℝ) * ((n : ℝ) - 1) := by nlinarith [hm0, hn1]
        have hss : Real.sqrt ((m : ℝ) * ((n : ℝ) - 1)) * Real.sqrt ((m : ℝ) * ((n : ℝ) - 1))
            = (m : ℝ) * ((n : ℝ) - 1) := Real.mul_self_sqrt hrad
        have hsnn : 0 ≤ Real.sqrt ((m : ℝ) * ((n : ℝ) - 1)) := Real.sqrt_nonneg _
        nlinarith [hss, hsnn, hm0, hmn1]
      rw [div_le_iff₀ hsqrt_pos]
      linarith [hkey]
    have hsum : (∑ m ∈ Finset.range n, (m : ℝ) / Real.sqrt ((n : ℝ) - 1))
        ≤ ∑ m ∈ Finset.range n, Real.sqrt m :=
      Finset.sum_le_sum hterm
    have hsumval : (∑ m ∈ Finset.range n, (m : ℝ) / Real.sqrt ((n : ℝ) - 1))
        = (∑ m ∈ Finset.range n, (m : ℝ)) / Real.sqrt ((n : ℝ) - 1) := by
      rw [Finset.sum_div]
    rw [hsumval, sum_range_id_real] at hsum
    refine le_trans ?_ hsum
    rw [le_div_iff₀ hsqrt_pos]
    have hsq : Real.sqrt ((n : ℝ) - 1) * Real.sqrt ((n : ℝ) - 1) = (n : ℝ) - 1 :=
      Real.mul_self_sqrt (by linarith)
    nlinarith [hsq, hsqrt_pos, Nat.cast_nonneg (α := ℝ) n]

/-- **Sum of squares dominated by the square of the `√`-sum.**
`Σ_{k ∈ range n} k² ≤ (Σ_{m ∈ range n} √m)²`, proved by induction on `n`; the
inductive step uses `sqrt_sum_ge_half` to absorb the new term `p²`.
Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345 (auxiliary comparison). -/
lemma sum_range_sq_le_henriciConst_sq (n : ℕ) :
    (∑ k ∈ Finset.range n, (k : ℝ) ^ 2) ≤ (henriciConst n) ^ 2 := by
  induction n with
  | zero => simp [henriciConst]
  | succ p ih =>
      have hstep : (∑ k ∈ Finset.range (p + 1), (k : ℝ) ^ 2)
          = (∑ k ∈ Finset.range p, (k : ℝ) ^ 2) + (p : ℝ) ^ 2 := by
        rw [Finset.sum_range_succ]
      have hcstep : henriciConst (p + 1) = henriciConst p + Real.sqrt p := by
        unfold henriciConst; rw [Finset.sum_range_succ]
      rw [hstep, hcstep]
      have hexpand : (henriciConst p + Real.sqrt p) ^ 2
          = (henriciConst p) ^ 2 + 2 * Real.sqrt p * henriciConst p + (Real.sqrt p) ^ 2 := by
        ring
      rw [hexpand]
      have hsp : (Real.sqrt p) ^ 2 = (p : ℝ) := Real.sq_sqrt (Nat.cast_nonneg p)
      rw [hsp]
      have hlow : Real.sqrt ((p : ℝ) - 1) * p / 2 ≤ henriciConst p := by
        have := sqrt_sum_ge_half p
        unfold henriciConst; exact this
      -- Reduce to: p² ≤ 2·√p·henriciConst p + p.
      have hgoal : (p : ℝ) ^ 2 ≤ 2 * Real.sqrt p * henriciConst p + (p : ℝ) := by
        rcases Nat.eq_zero_or_pos p with hp0 | hp0
        · subst hp0; simp
        · have hsqrt_p_nonneg : 0 ≤ Real.sqrt p := Real.sqrt_nonneg _
          have h1 : 2 * Real.sqrt p * (Real.sqrt ((p : ℝ) - 1) * p / 2)
              ≤ 2 * Real.sqrt p * henriciConst p := by
            apply mul_le_mul_of_nonneg_left hlow
            positivity
          have h2 : 2 * Real.sqrt p * (Real.sqrt ((p : ℝ) - 1) * p / 2)
              = Real.sqrt ((p : ℝ) * ((p : ℝ) - 1)) * p := by
            rw [Real.sqrt_mul (Nat.cast_nonneg p)]; ring
          have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp0
          -- √(p(p−1)) ≥ p−1:  s := √(p(p−1)) ≥ 0, s² = p(p−1) ≥ (p−1)², so s ≥ p−1.
          have hrad : (0 : ℝ) ≤ (p : ℝ) * ((p : ℝ) - 1) := by nlinarith [hp1]
          have hss : Real.sqrt ((p : ℝ) * ((p : ℝ) - 1)) * Real.sqrt ((p : ℝ) * ((p : ℝ) - 1))
              = (p : ℝ) * ((p : ℝ) - 1) := Real.mul_self_sqrt hrad
          have hsnn : 0 ≤ Real.sqrt ((p : ℝ) * ((p : ℝ) - 1)) := Real.sqrt_nonneg _
          have h3 : (p : ℝ) - 1 ≤ Real.sqrt ((p : ℝ) * ((p : ℝ) - 1)) := by
            nlinarith [hss, hsnn, hp1]
          have h4 : ((p : ℝ) - 1) * p ≤ Real.sqrt ((p : ℝ) * ((p : ℝ) - 1)) * p := by
            apply mul_le_mul_of_nonneg_right h3 (Nat.cast_nonneg p)
          nlinarith [h1, h2, h4]
      nlinarith [ih, hgoal]

/-- **The improved constant never exceeds the `HenriciExtremal.lean` constant.**
`henriciSharpConst n ≤ henriciConst n = Σ_{m<n} √m`, so the trace-weighted bound
is never worse than the term-by-term one.  (It is strictly smaller for `n ≥ 3`;
numerically `K₃ = √5 ≈ 2.236 < 2.414 = c₃`.)  Proof: comparing squares reduces to
`Σ_{k<n} k² ≤ (Σ_{m<n} √m)²` (`sum_range_sq_le_henriciConst_sq`).
Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345. -/
lemma henriciSharpConst_le_henriciConst (n : ℕ) :
    henriciSharpConst n ≤ henriciConst n := by
  have hc_nonneg : 0 ≤ henriciConst n := henriciConst_nonneg n
  rw [← Real.sqrt_sq hc_nonneg]
  unfold henriciSharpConst
  exact Real.sqrt_le_sqrt (sum_range_sq_le_henriciConst_sq n)

end NumStability
