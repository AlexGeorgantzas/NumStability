/-
Analysis/HenriciSharpConstantExact.lean

**Henrici's SHARP departure-from-normality constant `((n³−n)/12)^{1/2}`**
(Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., §18.1,
p. 345).

Higham states the *sharp* Henrici bound (squared form)
```
      Δ_F(A)² = ‖N‖_F² ≤ ( (n³−n)/12 )^{1/2} · ‖A*A − A A*‖_F ,        (Henrici★)
```
with the SHARP constant `((n³−n)/12)^{1/2}` (Henrici 1962; Eberlein).  The
companion files reach only weaker constants along the *obvious* route:
* `HenriciExtremal.lean` : `cₙ = Σ_{m<n} √m` (term-by-term block-mass CS);
* `HenriciSharpConstant.lean` (Wave-9) : `Kₙ = ((n−1)n(2n−1)/6)^{1/2}` via a
  single global CS with the *linear* weights `wᵢ = n−1−i` on the commutator
  diagonal `dᵢ = commDiagRe T i`, giving `Σ dᵢ² ≥ (Σ wᵢ dᵢ)²/Σwᵢ²` with the
  weight-sum `Σ wᵢ² = (n−1)n(2n−1)/6`.  That constant is a bounded factor `→ 2`
  above sharp because the *uncentered* weights `wᵢ` were used.

--------------------------------------------------------------------------------
THE NEW ROUTE (this file): CENTERED weights + the trace-zero constraint.

The single missing ingredient in Wave-9 is that the commutator diagonal is
*trace-free*: `Σᵢ dᵢ = tr(TᴴT − TTᴴ) = 0` (`sum_commDiagRe_eq_zero`, proved here,
unconditional — no triangularity).  Because `Σᵢ dᵢ = 0`, the linear weight
`wᵢ = n−1−i` in the Wave-9 reindexing
```
      Σ_{m∈range n} blockMass T m  =  − Σᵢ (n−1−i)·dᵢ        (Wave-9 pivot)
```
may be replaced by its **centering** `wᵢ − w̄` for FREE (`w̄ = (n−1)/2` the mean):
subtracting a constant from every weight changes `Σ wᵢ dᵢ` by `w̄·Σdᵢ = 0`.
Hence, with the centered weight `cᵢ = i − (n−1)/2`,
```
      Σ_{m∈range n} blockMass T m  =  Σᵢ cᵢ · dᵢ            (centered pivot)
```
and ONE Cauchy–Schwarz on the *centered* weights gives the SHARP constant:
```
      (Σ_m blockMass)² = (Σᵢ cᵢ dᵢ)²
                       ≤ (Σᵢ cᵢ²)·(Σᵢ dᵢ²)
                       = ((n³−n)/12)·(Σᵢ dᵢ²)              (★ combinatorial identity)
                       ≤ ((n³−n)/12)·‖C‖_F² .
```
The decisive combinatorial identity is the *variance-of-the-uniform* sum
```
      Σ_{i∈Fin n} ( i − (n−1)/2 )²  =  (n³−n)/12 ,           (centered_sq_eq_exactSharp)
```
NOT `Σ_{i<j}(j−i)²` (which equals `binom(n+2,4)`, a different quantity); the
correct combinatorial content behind `((n³−n)/12)^{1/2}` is the *centered second
moment* of `{0,…,n−1}`.  (The linear sum `Σ_{i<j}(j−i) = (n³−n)/6` is twice this.)

Chaining `‖N‖_F² ≤ Σ_m blockMass` (`frobSq_strictUpper_le_sum_blockMass`) with the
square root of `(★)` yields the sharp bound.

--------------------------------------------------------------------------------
WHAT THIS FILE PROVES (all unconditional over `ℂ`, IMPORT-ONLY, reusing the
`selfComm / frobSq / blockMass / commDiagRe / frobNormC` machinery and the
Wave-9 reindexing `sum_blockMass_eq_neg_weighted_diag`).

Let `T` be upper-triangular with strict-upper part `N`, `C = selfComm T`.

1. **Trace-free commutator diagonal** (`sum_commDiagRe_eq_zero`):
   `Σᵢ commDiagRe T i = 0`  (unconditional; `tr C = 0`).

2. **Centered pivot** (`sum_blockMass_eq_centered_diag`):
   `Σ_{m∈range n} blockMass T m = Σᵢ ((i:ℝ) − (n−1)/2)·commDiagRe T i`.

3. **Sharp combinatorial identity** (`centered_sq_eq_exactSharp`):
   `Σ_{i∈Fin n} ((i:ℝ) − (n−1)/2)² = (n³−n)/12`.

4. **Sharp global Cauchy–Schwarz** (`sum_blockMass_le_exactSharp`):
   `Σ_{m∈range n} blockMass T m ≤ ((n³−n)/12)^{1/2}·frobNormC (selfComm T)`.

5. **THE SHARP HENRICI BOUND**
   (`henrici_frobSq_le_exactSharp`, `henrici_departure_le_exactSharp_of_schur`):
   ```
        ‖N‖_F²  ≤  ((n³−n)/12)^{1/2} · ‖Tᴴ T − T Tᴴ‖_F ,     and (via Schur form)
        Δ_F(A)² ≤  ((n³−n)/12)^{1/2} · ‖Aᴴ A − A Aᴴ‖_F .
   ```
   `henriciExactSharpConst n := ((n³−n)/12)^{1/2}` is Higham's SHARP constant.

6. **The new constant beats Wave-9** (`henriciExactSharpConst_le_henriciSharpConst`):
   `((n³−n)/12)^{1/2} ≤ ((n−1)n(2n−1)/6)^{1/2}`, i.e. the centered bound never
   exceeds the uncentered Wave-9 bound (strictly smaller for `n ≥ 3`).

7. **TIGHTNESS WITNESS** (`henriciWitness`, `frobSq_henriciWitness`,
   `selfComm_henriciWitness_diag`, `frobSq_selfComm_henriciWitness`,
   `henriciWitness_attains_exactSharp`):
   the graded bidiagonal matrix `Wₙ` with `Wₙ i (i+1) = √( (i+1)(n−1−i)/2 )`
   (all other entries `0`) is strictly upper-triangular, has
   `frobSq Wₙ = (n³−n)/12`, has *diagonal* self-commutator with
   `frobSq (selfComm Wₙ) = (n³−n)/12`, and therefore attains equality
   ```
        frobSq Wₙ  =  ((n³−n)/12)^{1/2} · frobNormC (selfComm Wₙ) ,
   ```
   proving the constant `((n³−n)/12)^{1/2}` **cannot be improved**.

HONESTY LEDGER.
* Items 1–7 are UNCONDITIONAL theorems; the route is elementary (trace-zero +
  Wave-9 reindexing + centering (free by `Σdᵢ=0`) + one global Cauchy–Schwarz +
  the centered-second-moment identity + `Σ dᵢ² ≤ frobSq C`).  No hypothesis
  smuggles the conclusion; the strengthenings used (`Σ dᵢ = 0`, `Σ dᵢ² ≤ frobSq C`)
  are honest facts about the real object.
* The upper bound (items 1–5) attains Higham's SHARP constant `((n³−n)/12)^{1/2}`
  exactly — this is FULL CLOSURE of the Henrici display.
* The witness (item 7) certifies sharpness: `henriciWitness` realizes equality
  in item 5 for every `n`, so no smaller constant is valid.  The residual `Σ dᵢ²
  ≤ frobSq C` used in the general bound is EQUALITY for the witness (its
  commutator is diagonal), and the CS step is equality (its `dᵢ ∝ cᵢ`), so the
  two inequalities composing the bound are simultaneously tight — the constant is
  the exact extremum of `‖N‖_F²/‖C‖_F`.

Reference: N. J. Higham, *ASNA* 2nd ed., §18.1, p. 345 (Henrici display, sharp
constant `((n³−n)/12)^{1/2}`).
-/

import NumStability.Analysis.HenriciSharpConstant
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Sqrt

open scoped BigOperators Matrix
open Matrix Complex

namespace NumStability

variable {n : ℕ}

/-! ### 1. The commutator diagonal is trace-free -/

/-- **The self-commutator diagonal is trace-free.**  `Σᵢ commDiagRe T i = 0`,
because `commDiagRe T i = (column-mass) − (row-mass)` and the two masses sum to
the same total `Σ_{a,b} |T a b|²` after reindexing.  This is `tr(TᴴT − TTᴴ) = 0`;
it holds for *every* matrix `T` (no triangularity needed) and is the ingredient
missing from the Wave-9 argument.  Reference: Higham, *ASNA* 2nd ed., §18.1,
p. 345. -/
lemma sum_commDiagRe_eq_zero (T : Matrix (Fin n) (Fin n) ℂ) :
    (∑ i, commDiagRe T i) = 0 := by
  unfold commDiagRe
  rw [Finset.sum_sub_distrib]
  have h1 : (∑ i, ∑ k, Complex.normSq (T k i)) = ∑ i, ∑ k, Complex.normSq (T i k) := by
    rw [Finset.sum_comm]
  rw [h1]; ring

/-! ### 2. The centered reindexing pivot -/

/-- **Centered pivot for the summed block mass.**  Combining the Wave-9
reindexing `Σ_m blockMass T m = − Σᵢ (n−1−i)·dᵢ` with the trace-free identity
`Σᵢ dᵢ = 0`, the *uncentered* weight `n−1−i` may be replaced by the *centered*
weight `cᵢ = i − (n−1)/2` (subtracting the mean `(n−1)/2` costs
`(n−1)/2·Σdᵢ = 0`):
```
      Σ_{m∈range n} blockMass T m  =  Σᵢ ((i:ℝ) − (n−1)/2)·commDiagRe T i.
```
Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345. -/
lemma sum_blockMass_eq_centered_diag (T : Matrix (Fin n) (Fin n) ℂ)
    (hTtri : ∀ i j, j < i → T i j = 0) :
    (∑ m ∈ Finset.range n, blockMass T m)
      = ∑ i, ((i.val : ℝ) - ((n : ℝ) - 1)/2) * commDiagRe T i := by
  rw [sum_blockMass_eq_neg_weighted_diag T hTtri]
  -- rewrite the ℕ-cast weight n−1−i as the real (n−1)−i
  have hcast : ∀ i : Fin n, ((n - 1 - i.val : ℕ) : ℝ) = (n : ℝ) - 1 - (i.val : ℝ) := by
    intro i
    have hlt : i.val < n := i.isLt
    have h1 : (1 : ℕ) ≤ n := by omega
    have hle : i.val ≤ n - 1 := by omega
    rw [Nat.cast_sub hle, Nat.cast_sub h1]; push_cast; ring
  rw [Finset.sum_congr rfl (fun i _ => by rw [hcast i])]
  -- use Σ d = 0 to swap uncentered for centered weights
  have htz := sum_commDiagRe_eq_zero T
  rw [← Finset.sum_neg_distrib, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  have hcollapse : ∀ i : Fin n, (-(((n:ℝ) - 1 - (i.val:ℝ)) * commDiagRe T i)
      - (((i.val:ℝ) - ((n:ℝ) - 1)/2) * commDiagRe T i))
      = (-((n:ℝ) - 1)/2) * commDiagRe T i := fun i => by ring
  rw [Finset.sum_congr rfl (fun i _ => hcollapse i), ← Finset.mul_sum, htz, mul_zero]

/-! ### 3. The sharp combinatorial identity (centered second moment) -/

/-- **The centered-second-moment identity.**
`Σ_{i∈Fin n} ( (i:ℝ) − (n−1)/2 )² = (n³−n)/12`.  This is the true combinatorial
content of Higham's sharp constant: the variance-type sum of `{0,…,n−1}` about
its mean `(n−1)/2`.  Proof: expand `(i − (n−1)/2)² = i² − (n−1)i + (n−1)²/4` and
substitute the Wave-9 closed forms `Σ_{k<n} k² = (n−1)n(2n−1)/6` and
`Σ_{k<n} k = n(n−1)/2`.  Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345 (sharp
constant `((n³−n)/12)^{1/2}`). -/
lemma centered_sq_eq_exactSharp (n : ℕ) :
    (∑ i : Fin n, ((i.val : ℝ) - ((n : ℝ) - 1)/2)^2) = ((n : ℝ)^3 - n)/12 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => ((k : ℝ) - ((n : ℝ) - 1)/2)^2) n]
  have hexp : ∀ k : ℕ, ((k : ℝ) - ((n : ℝ) - 1)/2)^2
      = (k : ℝ)^2 - ((n : ℝ) - 1) * (k : ℝ) + ((n : ℝ) - 1)^2/4 := fun k => by ring
  rw [Finset.sum_congr rfl (fun k _ => hexp k)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_range_sq_closedForm,
      ← Finset.mul_sum, sum_range_id_real, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
  ring

/-- `(n³−n)/12 ≥ 0` (it is a sum of squares by `centered_sq_eq_exactSharp`). -/
lemma exactSharp_nonneg (n : ℕ) : 0 ≤ ((n : ℝ)^3 - n)/12 := by
  rw [← centered_sq_eq_exactSharp n]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-! ### 4. The sharp global Cauchy–Schwarz bound -/

/-- **Sharp global Cauchy–Schwarz bound on the summed block mass.**  Using the
centered pivot and one Cauchy–Schwarz on the centered weights,
```
      Σ_{m∈range n} blockMass T m  ≤  ((n³−n)/12)^{1/2} · frobNormC (selfComm T),
```
with `Σᵢ (commDiagRe T i)² ≤ frobSq (selfComm T)`.  Because the left side is a
sum of nonnegative block masses, no absolute value is needed.  Reference: Higham,
*ASNA* 2nd ed., §18.1, p. 345. -/
lemma sum_blockMass_le_exactSharp (T : Matrix (Fin n) (Fin n) ℂ)
    (hTtri : ∀ i j, j < i → T i j = 0) :
    (∑ m ∈ Finset.range n, blockMass T m)
      ≤ Real.sqrt (((n : ℝ)^3 - n)/12) * frobNormC (selfComm T) := by
  classical
  set c : Fin n → ℝ := fun i => (i.val : ℝ) - ((n : ℝ) - 1)/2 with hc
  set d : Fin n → ℝ := fun i => commDiagRe T i with hd
  have hEq : (∑ m ∈ Finset.range n, blockMass T m) = ∑ i, c i * d i :=
    sum_blockMass_eq_centered_diag T hTtri
  -- Cauchy–Schwarz on the centered weights.
  have hcs : (∑ i, c i * d i) ^ 2 ≤ (∑ i, (c i) ^ 2) * (∑ i, (d i) ^ 2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n)) c d
    simpa using h
  have hcsum : (∑ i, (c i) ^ 2) = ((n : ℝ)^3 - n)/12 := centered_sq_eq_exactSharp n
  have hd_le : (∑ i, (d i) ^ 2) ≤ frobSq (selfComm T) := sum_commDiagRe_sq_le_frobSq T
  have hc_nonneg : 0 ≤ ((n : ℝ)^3 - n)/12 := exactSharp_nonneg n
  have hsq : (∑ i, c i * d i) ^ 2 ≤ (((n : ℝ)^3 - n)/12) * frobSq (selfComm T) := by
    rw [← hcsum]
    exact le_trans hcs (mul_le_mul_of_nonneg_left hd_le (by rw [hcsum]; exact hc_nonneg))
  have hLHS_nonneg : 0 ≤ ∑ m ∈ Finset.range n, blockMass T m :=
    Finset.sum_nonneg fun m _ => blockMass_nonneg T m
  have hLHS_sq : (∑ m ∈ Finset.range n, blockMass T m) ^ 2 = (∑ i, c i * d i) ^ 2 := by
    rw [hEq]
  have hchain : (∑ m ∈ Finset.range n, blockMass T m) ^ 2
      ≤ (((n : ℝ)^3 - n)/12) * frobSq (selfComm T) := by rw [hLHS_sq]; exact hsq
  calc (∑ m ∈ Finset.range n, blockMass T m)
      = Real.sqrt ((∑ m ∈ Finset.range n, blockMass T m) ^ 2) := by
        rw [Real.sqrt_sq hLHS_nonneg]
    _ ≤ Real.sqrt ((((n : ℝ)^3 - n)/12) * frobSq (selfComm T)) := Real.sqrt_le_sqrt hchain
    _ = Real.sqrt (((n : ℝ)^3 - n)/12) * frobNormC (selfComm T) := by
        rw [Real.sqrt_mul hc_nonneg]; rfl

/-! ### 5. Higham's sharp Henrici constant and bound -/

/-- **Higham's SHARP Henrici departure constant** `((n³−n)/12)^{1/2}`
(Henrici 1962; Eberlein), realized here by the centered global Cauchy–Schwarz.
Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345. -/
noncomputable def henriciExactSharpConst (n : ℕ) : ℝ :=
  Real.sqrt (((n : ℝ)^3 - n)/12)

/-- `henriciExactSharpConst n ≥ 0`. -/
lemma henriciExactSharpConst_nonneg (n : ℕ) : 0 ≤ henriciExactSharpConst n :=
  Real.sqrt_nonneg _

/-- **THE SHARP HENRICI INEQUALITY.**  For upper-triangular `T` with strict-upper
part `N`,
```
      ‖N‖_F²  ≤  ((n³−n)/12)^{1/2} · ‖Tᴴ T − T Tᴴ‖_F .
```
Proof: `‖N‖_F² ≤ Σ_m blockMass T m` (`frobSq_strictUpper_le_sum_blockMass`), and
`Σ_m blockMass T m ≤ ((n³−n)/12)^{1/2}·‖C‖_F` by the sharp centered global
Cauchy–Schwarz (`sum_blockMass_le_exactSharp`).  This is Higham's Henrici display
with the SHARP constant `((n³−n)/12)^{1/2}`.  Reference: Higham, *ASNA* 2nd ed.,
§18.1, p. 345. -/
theorem henrici_frobSq_le_exactSharp (T N : Matrix (Fin n) (Fin n) ℂ)
    (hTtri : ∀ i j, j < i → T i j = 0)
    (hN : ∀ i j, N i j = if j > i then T i j else 0) :
    frobSq N ≤ henriciExactSharpConst n * frobNormC (selfComm T) := by
  have h1 : frobSq N ≤ ∑ m ∈ Finset.range n, blockMass T m :=
    frobSq_strictUpper_le_sum_blockMass T N hN
  exact le_trans h1 (sum_blockMass_le_exactSharp T hTtri)

/-- **The sharp Henrici inequality transported to `A` via its Schur form.**
If `Uᴴ A U = T = D + N` is a Schur form of `A`, then
```
      Δ_F(A)² = frobSq N  ≤  ((n³−n)/12)^{1/2} · ‖Aᴴ A − A Aᴴ‖_F ,
```
the commutator norm being the unitarily invariant Frobenius norm of
`Aᴴ A − A Aᴴ` (`frobNormC_selfComm_unitary_conj`).  This is Higham's Henrici
display (§18.1, p. 345) at full sharp strength.  Reference: Higham, *ASNA* 2nd
ed., §18.1, p. 345. -/
theorem henrici_departure_le_exactSharp_of_schur
    (A U T N : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hUeq : Uᴴ * A * U = T)
    (hTtri : ∀ i j, j < i → T i j = 0)
    (hN : ∀ i j, N i j = if j > i then T i j else 0) :
    departureFSq N ≤ henriciExactSharpConst n * frobNormC (selfComm A) := by
  rw [departureFSq_eq]
  have hbase := henrici_frobSq_le_exactSharp T N hTtri hN
  rw [← hUeq, frobNormC_selfComm_unitary_conj A U hU] at hbase
  exact hbase

/-! ### 6. The sharp constant improves on Wave-9 -/

/-- **The sharp constant never exceeds the Wave-9 constant.**
`henriciExactSharpConst n = ((n³−n)/12)^{1/2} ≤ ((n−1)n(2n−1)/6)^{1/2} =
henriciSharpConst n`.  Reduces to `(n³−n)/12 ≤ (n−1)n(2n−1)/6` under the square
root, i.e. `(n−1)n(n+1)/12 ≤ (n−1)n(2n−1)/6 ⟺ (n+1) ≤ 2(2n−1) ⟺ 0 ≤ 3n−3`,
which holds for `n ≥ 1` (and trivially at `n = 0`).  Reference: Higham, *ASNA*
2nd ed., §18.1, p. 345. -/
lemma henriciExactSharpConst_le_henriciSharpConst (n : ℕ) :
    henriciExactSharpConst n ≤ henriciSharpConst n := by
  unfold henriciExactSharpConst
  rw [henriciSharpConst_eq_closedForm]
  apply Real.sqrt_le_sqrt
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; norm_num
  · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hpos
    have hfac : (0 : ℝ) ≤ ((n : ℝ) - 1) * n := by nlinarith
    nlinarith [hfac, h1]

/-! ### 7. Tightness witness: the graded bidiagonal extremal matrix -/

/-- The per-superdiagonal squared weight of the extremal matrix,
`e i = (i+1)(n−1−i)/2` (as a real number).  This is the partial sum
`Σ_{k≤i} ((n−1)/2 − k)` that makes the commutator diagonal proportional to the
centered weight `cᵢ`.  Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345
(extremal construction for the sharp constant). -/
noncomputable def witnessWeight (n : ℕ) (i : ℕ) : ℝ :=
  ((i : ℝ) + 1) * ((n : ℝ) - 1 - (i : ℝ)) / 2

/-- **Henrici's tightness witness `Wₙ`.**  The graded bidiagonal (single
super-diagonal) matrix with `Wₙ i j = √(witnessWeight n i.val)` when `j = i+1`
and `0` otherwise.  It is strictly upper-triangular (nilpotent), and — as shown
below — attains equality in the sharp Henrici bound for every `n`, certifying
that `((n³−n)/12)^{1/2}` cannot be improved.  Reference: Higham, *ASNA* 2nd ed.,
§18.1, p. 345 (extremal construction). -/
noncomputable def henriciWitness (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of (fun i j : Fin n =>
    if j.val = i.val + 1 then (Real.sqrt (witnessWeight n i.val) : ℂ) else 0)

/-- `henriciWitness` is upper-triangular: entries below the diagonal vanish
(indeed all entries off the first super-diagonal vanish).  Reference: Higham,
*ASNA* 2nd ed., §18.1, p. 345. -/
lemma henriciWitness_triangular (n : ℕ) :
    ∀ i j : Fin n, j < i → henriciWitness n i j = 0 := by
  intro i j hji
  unfold henriciWitness
  simp only [Matrix.of_apply]
  rw [if_neg]
  have : j.val < i.val := hji
  omega

/-- `henriciWitness` equals its own strict-upper part (it is strictly upper
triangular).  Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345. -/
lemma henriciWitness_strictUpper (n : ℕ) :
    ∀ i j : Fin n, henriciWitness n i j = if j > i then henriciWitness n i j else 0 := by
  intro i j
  by_cases h : j > i
  · rw [if_pos h]
  · rw [if_neg h]
    unfold henriciWitness
    simp only [Matrix.of_apply]
    rw [if_neg]
    have : ¬ (i.val < j.val) := by
      simp only [gt_iff_lt, Fin.lt_def] at h; omega
    omega

/-- `witnessWeight n k ≥ 0` for `k < n`: the factor `n−1−k ≥ 0` on that range.
Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345. -/
lemma witnessWeight_nonneg (n k : ℕ) (hk : k < n) : 0 ≤ witnessWeight n k := by
  unfold witnessWeight
  have h2 : (0 : ℝ) ≤ (n : ℝ) - 1 - (k : ℝ) := by
    have : (k : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hk
    linarith
  positivity

/-- **Sum of the witness weights** `Σ_{i∈Fin n} witnessWeight n i.val = (n³−n)/12`.
(The `i = n−1` term vanishes, so the full `Fin n` sum equals the "active" sum over
`i ≤ n−2`.)  Proof by expansion into the Wave-9 closed forms `Σ k`, `Σ k²`.
Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345. -/
lemma sum_witnessWeight_eq (n : ℕ) :
    (∑ i : Fin n, witnessWeight n i.val) = ((n : ℝ)^3 - n)/12 := by
  unfold witnessWeight
  rw [Fin.sum_univ_eq_sum_range (fun k => ((k : ℝ) + 1) * ((n : ℝ) - 1 - (k : ℝ)) / 2) n]
  have hexp : ∀ k : ℕ, ((k : ℝ) + 1) * ((n : ℝ) - 1 - (k : ℝ)) / 2
      = ((n : ℝ) - 1)/2 * (k : ℝ) + ((n : ℝ) - 1)/2 - (k : ℝ)^2/2 - (k : ℝ)/2 := fun k => by ring
  rw [Finset.sum_congr rfl (fun k _ => hexp k)]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, sum_range_id_real, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h1 : (∑ k ∈ Finset.range n, (k : ℝ)^2/2) = (∑ k ∈ Finset.range n, (k : ℝ)^2)/2 := by
    rw [Finset.sum_div]
  have h2 : (∑ k ∈ Finset.range n, (k : ℝ)/2) = (∑ k ∈ Finset.range n, (k : ℝ))/2 := by
    rw [Finset.sum_div]
  rw [h1, h2, sum_range_sq_closedForm, sum_range_id_real]
  ring

/-- **Frobenius mass of the witness** `frobSq (henriciWitness n) = (n³−n)/12`.
Each row `i` contributes exactly `witnessWeight n i.val` (its single super-diagonal
entry `√(witnessWeight n i.val)`, whose `normSq` is `witnessWeight n i.val`; the
last row `i = n−1` contributes `0`, consistent with `witnessWeight n (n−1) = 0`).
Summing gives `Σ_i witnessWeight n i.val = (n³−n)/12`.  So `‖N‖_F² = (n³−n)/12` for
the witness.  Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345. -/
lemma frobSq_henriciWitness (n : ℕ) :
    frobSq (henriciWitness n) = ((n : ℝ)^3 - n)/12 := by
  classical
  have hrow : ∀ i : Fin n, (∑ j, Complex.normSq (henriciWitness n i j)) = witnessWeight n i.val := by
    intro i
    unfold henriciWitness; simp only [Matrix.of_apply]
    by_cases hlt : i.val + 1 < n
    · rw [Finset.sum_eq_single (⟨i.val + 1, hlt⟩ : Fin n)]
      · rw [if_pos rfl, Complex.normSq_ofReal]
        exact Real.mul_self_sqrt (witnessWeight_nonneg n i.val i.isLt)
      · intro j _ hj
        rw [if_neg (fun hc => hj (Fin.ext hc)), Complex.normSq_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    · have hn : 0 < n := i.pos
      have hival : i.val = n - 1 := by have := i.isLt; omega
      have hsum0 : (∑ j : Fin n,
          Complex.normSq (if j.val = i.val + 1 then (Real.sqrt (witnessWeight n i.val) : ℂ) else 0)) = 0 := by
        apply Finset.sum_eq_zero; intro j _
        rw [if_neg (by have := j.isLt; omega), Complex.normSq_zero]
      rw [hsum0, hival]
      unfold witnessWeight
      have h1 : (1 : ℕ) ≤ n := hn
      have hz : ((n : ℝ) - 1 - ((n - 1 : ℕ) : ℝ)) = 0 := by
        rw [Nat.cast_sub h1]; push_cast; ring
      rw [hz]; ring
  unfold frobSq
  rw [Finset.sum_congr rfl (fun i _ => hrow i), sum_witnessWeight_eq]

/-- **Commutator diagonal of the witness equals the centered weight.**
`commDiagRe (henriciWitness n) i = (i:ℝ) − (n−1)/2`.  The column-mass in column `i`
is `witnessWeight n (i−1)` (for `i > 0`, else `0`); the row-mass in row `i` is
`witnessWeight n i`; their difference telescopes to `i − (n−1)/2` (the same centered
weight `cᵢ` as in the sharp bound).  So the witness's commutator diagonal is EXACTLY
the CS-extremal direction, making the Cauchy–Schwarz step an equality.  Reference:
Higham, *ASNA* 2nd ed., §18.1, p. 345. -/
lemma commDiagRe_henriciWitness (n : ℕ) (i : Fin n) :
    commDiagRe (henriciWitness n) i = (i.val : ℝ) - ((n : ℝ) - 1)/2 := by
  classical
  have hcol : (∑ k, Complex.normSq (henriciWitness n k i))
      = (if 0 < i.val then witnessWeight n (i.val - 1) else 0) := by
    unfold henriciWitness; simp only [Matrix.of_apply]
    by_cases hpos : 0 < i.val
    · rw [if_pos hpos]
      have hk : i.val - 1 < n := by have := i.isLt; omega
      rw [Finset.sum_eq_single (⟨i.val - 1, hk⟩ : Fin n)]
      · rw [if_pos (show i.val = (⟨i.val - 1, hk⟩ : Fin n).val + 1 by simp; omega),
            Complex.normSq_ofReal]
        exact Real.mul_self_sqrt (witnessWeight_nonneg n (i.val - 1) hk)
      · intro k _ hk2
        rw [if_neg, Complex.normSq_zero]
        intro hc; apply hk2; apply Fin.ext; show k.val = i.val - 1; omega
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [if_neg hpos]
      apply Finset.sum_eq_zero; intro k _
      rw [if_neg (by omega), Complex.normSq_zero]
  have hrow : (∑ k, Complex.normSq (henriciWitness n i k)) = witnessWeight n i.val := by
    unfold henriciWitness; simp only [Matrix.of_apply]
    by_cases hlt : i.val + 1 < n
    · rw [Finset.sum_eq_single (⟨i.val + 1, hlt⟩ : Fin n)]
      · rw [if_pos rfl, Complex.normSq_ofReal]
        exact Real.mul_self_sqrt (witnessWeight_nonneg n i.val i.isLt)
      · intro j _ hj
        rw [if_neg (fun hc => hj (Fin.ext hc)), Complex.normSq_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    · have hn : 0 < n := i.pos
      have hival : i.val = n - 1 := by have := i.isLt; omega
      have hsum0 : (∑ j : Fin n,
          Complex.normSq (if j.val = i.val + 1 then (Real.sqrt (witnessWeight n i.val) : ℂ) else 0)) = 0 := by
        apply Finset.sum_eq_zero; intro j _
        rw [if_neg (by have := j.isLt; omega), Complex.normSq_zero]
      rw [hsum0, hival]
      unfold witnessWeight
      have h1 : (1 : ℕ) ≤ n := hn
      have hz : ((n : ℝ) - 1 - ((n - 1 : ℕ) : ℝ)) = 0 := by
        rw [Nat.cast_sub h1]; push_cast; ring
      rw [hz]; ring
  unfold commDiagRe
  rw [hcol, hrow]
  by_cases hpos : 0 < i.val
  · rw [if_pos hpos]
    unfold witnessWeight
    have hcast : ((i.val - 1 : ℕ) : ℝ) = (i.val : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ i.val)]; push_cast; ring
    rw [hcast]; ring
  · rw [if_neg hpos]
    have : i.val = 0 := by omega
    rw [this]; unfold witnessWeight; push_cast; ring

/-- **The witness self-commutator is diagonal (zero off the diagonal).**  For a
single super-diagonal matrix, both `WᴴW` and `WWᴴ` are diagonal, so their
difference `selfComm W` has no off-diagonal mass.  Reference: Higham, *ASNA* 2nd
ed., §18.1, p. 345. -/
lemma selfComm_henriciWitness_offdiag (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (selfComm (henriciWitness n)) i j = 0 := by
  classical
  have hWhW : ((henriciWitness n)ᴴ * (henriciWitness n)) i j = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    rw [Matrix.conjTranspose_apply]
    unfold henriciWitness; simp only [Matrix.of_apply]
    by_cases h1 : i.val = k.val + 1
    · by_cases h2 : j.val = k.val + 1
      · exact absurd (Fin.ext (by omega : i.val = j.val)) hij
      · rw [if_neg h2, mul_zero]
    · rw [if_neg h1, star_zero, zero_mul]
  have hWWh : ((henriciWitness n) * (henriciWitness n)ᴴ) i j = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    rw [Matrix.conjTranspose_apply]
    unfold henriciWitness; simp only [Matrix.of_apply]
    by_cases h1 : k.val = i.val + 1
    · by_cases h2 : k.val = j.val + 1
      · exact absurd (Fin.ext (by omega : i.val = j.val)) hij
      · rw [if_neg h2, star_zero, mul_zero]
    · rw [if_neg h1, zero_mul]
  unfold selfComm
  rw [Matrix.sub_apply, hWhW, hWWh, sub_zero]

/-- **Frobenius mass of the witness commutator** `frobSq (selfComm (henriciWitness n))
= (n³−n)/12`.  Since `selfComm W` is diagonal (`selfComm_henriciWitness_offdiag`)
with real diagonal `commDiagRe W i = i − (n−1)/2` (`commDiagRe_henriciWitness`,
`commDiag_ofReal`), `frobSq = Σ_i (i − (n−1)/2)² = (n³−n)/12` by
`centered_sq_eq_exactSharp`.  So `‖C‖_F² = (n³−n)/12` for the witness — equal to
`‖N‖_F²`.  Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345. -/
lemma frobSq_selfComm_henriciWitness (n : ℕ) :
    frobSq (selfComm (henriciWitness n)) = ((n : ℝ)^3 - n)/12 := by
  classical
  have hdiag : frobSq (selfComm (henriciWitness n))
      = ∑ i : Fin n, ((i.val : ℝ) - ((n : ℝ) - 1)/2)^2 := by
    unfold frobSq
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · rw [commDiag_ofReal, commDiagRe_henriciWitness, Complex.normSq_ofReal, sq]
    · intro j _ hji
      rw [selfComm_henriciWitness_offdiag n i j (fun h => hji h.symm), Complex.normSq_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [hdiag, centered_sq_eq_exactSharp]

/-- **THE TIGHTNESS WITNESS.**  The graded bidiagonal `Wₙ = henriciWitness n`
attains equality in the sharp Henrici bound:
```
      frobSq Wₙ  =  henriciExactSharpConst n · frobNormC (selfComm Wₙ) ,
```
because both `frobSq Wₙ = (n³−n)/12` (`frobSq_henriciWitness`) and
`frobSq (selfComm Wₙ) = (n³−n)/12` (`frobSq_selfComm_henriciWitness`), so
`frobNormC (selfComm Wₙ) = ((n³−n)/12)^{1/2}` and the RHS is
`((n³−n)/12)^{1/2}·((n³−n)/12)^{1/2} = (n³−n)/12 = frobSq Wₙ`.  Since `Wₙ` is
strictly upper-triangular (`henriciWitness_strictUpper`), it is its own
departure-from-normality part `N`, and the sharp inequality
`henrici_frobSq_le_exactSharp` holds with EQUALITY here.  Therefore the constant
`((n³−n)/12)^{1/2}` is the best possible — it cannot be lowered.  Reference:
Higham, *ASNA* 2nd ed., §18.1, p. 345 (Henrici's sharp constant is attained). -/
theorem henriciWitness_attains_exactSharp (n : ℕ) :
    frobSq (henriciWitness n)
      = henriciExactSharpConst n * frobNormC (selfComm (henriciWitness n)) := by
  unfold henriciExactSharpConst frobNormC
  rw [frobSq_selfComm_henriciWitness, frobSq_henriciWitness]
  -- goal: (n³−n)/12 = √((n³−n)/12) · √((n³−n)/12)
  exact (Real.mul_self_sqrt (exactSharp_nonneg n)).symm

end NumStability
