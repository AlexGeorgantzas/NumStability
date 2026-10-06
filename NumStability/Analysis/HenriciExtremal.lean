/-
Analysis/HenriciExtremal.lean

**Henrici's departure-from-normality inequality** (Higham, *Accuracy and
Stability of Numerical Algorithms*, 2nd ed., §18.1, p. 345).

Higham states, for the Schur form `Uᴴ A U = T = D + N` (`D` diagonal, `N`
strictly upper-triangular) the Henrici bound
```
      Δ_F(A) = ( ‖A‖_F² − Σ_i |λ_i|² )^{1/2}
             ≤ ( (n³−n)/12 )^{1/4} · ‖A*A − A A*‖_F^{1/2}.            (Henrici)
```
Squaring, and writing `Δ_F(A)² = ‖N‖_F²` (the Frobenius Pythagorean identity of
`MatrixPowersHenrici.lean`), this is
```
      ‖N‖_F² ≤ ( (n³−n)/12 )^{1/2} · ‖A*A − A A*‖_F.                  (Henrici²)
```
Because the Frobenius norm and the commutator are unitarily invariant, the
right-hand side may be evaluated at the Schur factor `T` itself:
`‖A*A − A A*‖_F = ‖Tᴴ T − T Tᴴ‖_F`.  Hence the whole inequality is an
*extremal estimate over strictly-upper-triangular matrices `N`* relating the
Frobenius mass of `N` to the Frobenius norm of the commutator of `T = D + N`.

--------------------------------------------------------------------------------
WHAT THIS FILE PROVES (all unconditional over `ℂ`).

Let `T` be upper-triangular with strict-upper part `N`, and let
`C = Tᴴ T − T Tᴴ` be its self-commutator.

1. **Diagonal of the commutator is real and telescopes**
   (`commDiag_apply`, `commDiag_ofReal`): `C i i = (∑ k, |T k i|²) − (∑ k, |T i k|²)`,
   a real number.

2. **Summation-by-parts / block identity** (`partialTrace_eq_neg_blockMass`):  for
   every cut `m`,
   ```
        ∑_{i < m} C i i  =  − ∑_{i < m} ∑_{j ≥ m} |T i j|²,
   ```
   i.e. the partial trace of the commutator equals *minus* the Frobenius mass of
   the strict-upper block sitting in rows `< m`, columns `≥ m`.  (This is the
   exact cancellation that powers Henrici's derivation.)

3. **Block mass bounded by the commutator** (`blockMass_le`):  writing
   `Bₘ = ∑_{i<m} ∑_{j≥m} |T i j|²` and `‖C‖_F = √(frobSq C)`,
   ```
        Bₘ ≤ √m · ‖C‖_F,
   ```
   by Cauchy–Schwarz on the `m` real diagonal commutator entries.

4. **Weighted mass identity** (`sum_blockMass_eq_weighted`):
   `∑_{m ∈ range n} Bₘ = ∑ i, ∑ j, (cutWeight n i j) · |T i j|²`, where
   `cutWeight n i j = #{m ∈ range n : i < m ≤ j}` equals `j − i` on the
   strict-upper support and is `≥ 1` there (`one_le_cutWeight_of_lt`).  Hence
   `‖N‖_F² ≤ ∑_{m} Bₘ` (`frobSq_strictUpper_le_sum_blockMass`).

5. **Henrici inequality with an explicit (non-sharp) constant**
   (`henrici_frobSq_le`, `henrici_departure_le_of_schur`):
   ```
        ‖N‖_F²  ≤  cₙ · ‖Tᴴ T − T Tᴴ‖_F,      cₙ = ∑_{m=1}^{n-1} √m,
   ```
   and, transported through the Schur form and the unitary invariance of the
   commutator (`henrici_departure_le_of_schur`),
   ```
        Δ_F(A)²  ≤  cₙ · ‖Aᴴ A − A Aᴴ‖_F.
   ```

HONESTY LEDGER.
* Items 1–5 are UNCONDITIONAL theorems.  The route is complete and elementary:
  the telescoping identity (2) + Cauchy–Schwarz (3) + the weight `j − i ≥ 1`
  (4).  No hypothesis smuggles the conclusion.
* The constant delivered is `cₙ = ∑_{m=1}^{n-1} √m`, which is *weaker* than
  Higham's SHARP constant `((n³−n)/12)^{1/2}`.  The sharp constant is the
  maximum of a quadratic form over strictly-upper matrices (the Henrici/Eberlein
  variational problem) and is NOT proved here; obtaining it from `cₙ` requires
  that extremal analysis, which is beyond the elementary telescoping route and
  the current Mathlib API.  The statement is therefore honest: it proves the
  Henrici inequality *shape* with a concrete constant, and flags precisely the
  gap to the sharp constant.  `cₙ ≤ √(n·(n³−n)/12)`-type comparisons are not
  asserted; only the honest bound with `cₙ` is claimed.

Reference: N. J. Higham, *ASNA* 2nd ed., §18.1, p. 345 (Henrici display).
-/

import NumStability.Analysis.MatrixPowersHenrici
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Real.Sqrt

open scoped BigOperators Matrix
open Matrix Complex

namespace NumStability

variable {n : ℕ}

/-! ### The self-commutator and its (real) diagonal -/

/-- The self-commutator `C = Tᴴ T − T Tᴴ`.
Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345 (`A*A − A A*`). -/
noncomputable def selfComm (T : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Tᴴ * T - T * Tᴴ

/-- **Diagonal of the self-commutator, as a real difference of squared moduli.**
`(Tᴴ T − T Tᴴ) i i = (∑ k, |T k i|²) − (∑ k, |T i k|²)`, embedded in `ℂ`.
Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345. -/
lemma commDiag_apply (T : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    (selfComm T) i i
      = ((∑ k, Complex.normSq (T k i)) - (∑ k, Complex.normSq (T i k)) : ℝ) := by
  have hcol : (Tᴴ * T) i i = ((∑ k, Complex.normSq (T k i) : ℝ) : ℂ) := by
    rw [Matrix.mul_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.conjTranspose_apply, Complex.normSq_eq_conj_mul_self (z := T k i),
        Complex.star_def]
  have hrow : (T * Tᴴ) i i = ((∑ k, Complex.normSq (T i k) : ℝ) : ℂ) := by
    rw [Matrix.mul_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.conjTranspose_apply, Complex.normSq_eq_conj_mul_self (z := T i k),
        Complex.star_def, mul_comm]
  unfold selfComm
  rw [Matrix.sub_apply, hcol, hrow, ← Complex.ofReal_sub]

/-- The commutator diagonal entry as a *real* number (its `Complex.re`, equal to
the difference of column- and row-mass).  Reference: Higham, *ASNA* 2nd ed.,
§18.1, p. 345. -/
noncomputable def commDiagRe (T : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : ℝ :=
  (∑ k, Complex.normSq (T k i)) - (∑ k, Complex.normSq (T i k))

/-- `(selfComm T) i i` is the real number `commDiagRe T i` embedded in `ℂ`. -/
lemma commDiag_ofReal (T : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    (selfComm T) i i = (commDiagRe T i : ℂ) := commDiag_apply T i

/-! ### The block mass and the telescoping (partial-trace) identity -/

/-- The Frobenius mass of the strict-upper block with rows `< m`, columns `≥ m`:
`Bₘ = ∑_{i.val < m} ∑_{j.val ≥ m} |T i j|²`.
Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345. -/
def blockMass (T : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < m),
    ∑ j ∈ Finset.univ.filter (fun j : Fin n => m ≤ j.val),
      Complex.normSq (T i j)

/-- `blockMass` is a sum of squared moduli, hence nonnegative. -/
lemma blockMass_nonneg (T : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) :
    0 ≤ blockMass T m :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-- **Telescoping / partial-trace identity.**  For upper-triangular `T`
(`T i j = 0` when `j < i`) and any cut `m`,
```
      ∑_{i.val < m} (selfComm T) i i  =  − blockMass T m   (as a real number),
```
i.e. the partial trace of the self-commutator down to row `m` equals *minus* the
Frobenius mass of the strict-upper block above the cut.  The proof splits the
column index into `< m` (antisymmetric, cancels) and `≥ m` (below-diagonal terms
vanish by triangularity).  Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345. -/
lemma partialTrace_eq_neg_blockMass (T : Matrix (Fin n) (Fin n) ℂ)
    (hTtri : ∀ i j, j < i → T i j = 0) (m : ℕ) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < m), commDiagRe T i)
      = - blockMass T m := by
  classical
  set Slt : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => i.val < m) with hSlt
  set Sge : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => m ≤ j.val) with hSge
  -- Expand each commDiagRe and split the k-sum over Slt ⊔ Sge (a partition of univ).
  have hsplit : ∀ i : Fin n,
      commDiagRe T i
        = (∑ k ∈ Slt, (Complex.normSq (T k i) - Complex.normSq (T i k)))
          + (∑ k ∈ Sge, (Complex.normSq (T k i) - Complex.normSq (T i k))) := by
    intro i
    unfold commDiagRe
    rw [← Finset.sum_sub_distrib]
    have huniv : (Slt ∪ Sge) = Finset.univ := by
      ext x
      simp only [hSlt, hSge, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and, iff_true]
      exact Nat.lt_or_ge x.val m
    have hdisj : Disjoint Slt Sge := by
      rw [Finset.disjoint_left]; intro x hx hx'
      simp only [hSlt, hSge, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
      omega
    rw [← huniv, Finset.sum_union hdisj]
  -- Rewrite the target LHS via hsplit.
  rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib]
  -- Part A: the Slt×Slt double sum is antisymmetric ⇒ 0.
  have hA : (∑ i ∈ Slt, ∑ k ∈ Slt,
      (Complex.normSq (T k i) - Complex.normSq (T i k))) = 0 := by
    -- swapping names i,k negates the summand ⇒ the sum equals its own negation.
    have hswap : (∑ i ∈ Slt, ∑ k ∈ Slt,
        (Complex.normSq (T k i) - Complex.normSq (T i k)))
        = - ∑ i ∈ Slt, ∑ k ∈ Slt,
          (Complex.normSq (T k i) - Complex.normSq (T i k)) := by
      conv_lhs => rw [Finset.sum_comm]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    linarith [hswap]
  -- Part B: the Slt×Sge double sum: T k i = 0 (below diagonal), leaving -blockMass.
  have hB : (∑ i ∈ Slt, ∑ k ∈ Sge,
      (Complex.normSq (T k i) - Complex.normSq (T i k))) = - blockMass T m := by
    unfold blockMass
    rw [← hSlt, ← hSge, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hik : i.val < k.val := by
      simp only [hSlt, hSge, Finset.mem_filter, Finset.mem_univ, true_and] at hi hk
      omega
    have hzero : T k i = 0 := hTtri k i (by exact Fin.lt_def.mpr hik)
    rw [hzero, Complex.normSq_zero]
    ring
  rw [hA, hB, zero_add]

/-! ### The commutator diagonal is controlled by `‖C‖_F` -/

/-- `normSq (C i i) = (commDiagRe T i)²` for `C = selfComm T`, since `C i i` is
real.  Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345. -/
lemma normSq_commDiag (T : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    Complex.normSq ((selfComm T) i i) = (commDiagRe T i) ^ 2 := by
  rw [commDiag_ofReal, Complex.normSq_ofReal, sq]

/-- **Diagonal `ℓ²` mass ≤ full Frobenius mass.**  For any matrix `C`,
`∑ i, normSq (C i i) ≤ frobSq C`.  Reference: Higham, *ASNA* 2nd ed., §18.1,
p. 344-345 (`‖·‖_F`). -/
lemma sum_diag_normSq_le_frobSq (C : Matrix (Fin n) (Fin n) ℂ) :
    (∑ i, Complex.normSq (C i i)) ≤ frobSq C := by
  unfold frobSq
  refine Finset.sum_le_sum fun i _ => ?_
  refine Finset.single_le_sum (f := fun j => Complex.normSq (C i j))
    (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i)

/-- **Sum of squared commutator-diagonal entries is ≤ `frobSq (selfComm T)`.**
Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345. -/
lemma sum_commDiagRe_sq_le_frobSq (T : Matrix (Fin n) (Fin n) ℂ) :
    (∑ i, (commDiagRe T i) ^ 2) ≤ frobSq (selfComm T) := by
  have h : (∑ i, (commDiagRe T i) ^ 2) = ∑ i, Complex.normSq ((selfComm T) i i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [normSq_commDiag]
  rw [h]
  exact sum_diag_normSq_le_frobSq (selfComm T)

/-! ### The commutator Frobenius norm `‖C‖_F = √(frobSq C)` -/

/-- The Frobenius norm (not squared) of a matrix: `√(frobSq C)`.
Reference: Higham, *ASNA* 2nd ed., §18.1, p. 344-345 (`‖·‖_F`). -/
noncomputable def frobNormC (C : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  Real.sqrt (frobSq C)

/-- `frobNormC C ≥ 0`. -/
lemma frobNormC_nonneg (C : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ frobNormC C :=
  Real.sqrt_nonneg _

/-- **Cauchy–Schwarz bound on the block mass.**  For upper-triangular `T`,
`blockMass T m ≤ √m · frobNormC (selfComm T)`.  Proof: `blockMass T m =
−∑_{i<m} commDiagRe T i`, so by Cauchy–Schwarz over the `m` diagonal entries
`(blockMass T m)² ≤ m · ∑ (commDiagRe)² ≤ m · frobSq C`; take square roots.
Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345. -/
lemma blockMass_le (T : Matrix (Fin n) (Fin n) ℂ)
    (hTtri : ∀ i j, j < i → T i j = 0) (m : ℕ) :
    blockMass T m ≤ Real.sqrt m * frobNormC (selfComm T) := by
  classical
  set Slt : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => i.val < m) with hSlt
  -- blockMass = -∑_{i∈Slt} commDiagRe.
  have hbm : blockMass T m = - ∑ i ∈ Slt, commDiagRe T i := by
    rw [partialTrace_eq_neg_blockMass T hTtri m, neg_neg]
  -- Cauchy–Schwarz: (∑ 1·commDiagRe)² ≤ (∑ 1²)(∑ commDiagRe²).
  have hcs : (∑ i ∈ Slt, commDiagRe T i) ^ 2
      ≤ (∑ _i ∈ Slt, (1:ℝ) ^ 2) * (∑ i ∈ Slt, (commDiagRe T i) ^ 2) := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Slt (fun _ => (1:ℝ)) (fun i => commDiagRe T i)
    simpa using this
  -- ∑_{Slt} 1 = card Slt ≤ m.
  have hcard : (Slt.card : ℝ) ≤ m := by
    have hle : Slt.card ≤ (Finset.range m).card := by
      refine Finset.card_le_card_of_injOn (fun i => i.val) ?_ ?_
      · intro i hi
        rw [Finset.mem_coe, hSlt, Finset.mem_filter] at hi
        simp only [Finset.coe_range, Set.mem_Iio]; exact hi.2
      · intro a _ b _ hab; exact Fin.val_injective hab
    rw [Finset.card_range] at hle
    exact_mod_cast hle
  -- Assemble the squared bound.
  have hcomm_nonneg : 0 ≤ ∑ i ∈ Slt, (commDiagRe T i) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsum_sq_le : (∑ i ∈ Slt, (commDiagRe T i) ^ 2) ≤ frobSq (selfComm T) := by
    refine le_trans ?_ (sum_commDiagRe_sq_le_frobSq T)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Slt)
      (fun i _ _ => sq_nonneg _)
  have hbm_sq : (blockMass T m) ^ 2
      ≤ (m : ℝ) * frobSq (selfComm T) := by
    rw [hbm, neg_sq]
    calc (∑ i ∈ Slt, commDiagRe T i) ^ 2
        ≤ (∑ _i ∈ Slt, (1:ℝ) ^ 2) * (∑ i ∈ Slt, (commDiagRe T i) ^ 2) := hcs
      _ = (Slt.card : ℝ) * (∑ i ∈ Slt, (commDiagRe T i) ^ 2) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ (m : ℝ) * frobSq (selfComm T) := by
            apply mul_le_mul hcard hsum_sq_le hcomm_nonneg
            exact le_trans (Nat.cast_nonneg _) hcard
  -- Take square roots: blockMass ≥ 0, so blockMass = √(blockMass²) ≤ √(m·frobSq) = √m·√frobSq.
  have hbm_nonneg : 0 ≤ blockMass T m := blockMass_nonneg T m
  calc blockMass T m
      = Real.sqrt ((blockMass T m) ^ 2) := by rw [Real.sqrt_sq hbm_nonneg]
    _ ≤ Real.sqrt ((m : ℝ) * frobSq (selfComm T)) := Real.sqrt_le_sqrt hbm_sq
    _ = Real.sqrt m * frobNormC (selfComm T) := by
          rw [Real.sqrt_mul (Nat.cast_nonneg m)]; rfl

/-! ### The weighted-mass identity and the lower bound on `‖N‖_F²` -/

/-- The per-entry weight `w i j = #{ m ∈ range n : i.val < m ≤ j.val }`.  This
counts the cuts `m` for which entry `(i,j)` lies in the strict-upper block.
Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345. -/
def cutWeight (m0 : ℕ) (i j : Fin n) : ℕ :=
  ((Finset.range m0).filter (fun m => i.val < m ∧ m ≤ j.val)).card

/-- **Sum of block masses = weighted Frobenius sum.**  Fubini across the cut
index `m`:
```
      ∑_{m ∈ range n} blockMass T m
        = ∑ i, ∑ j, (cutWeight n i j : ℝ) · |T i j|².
```
Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345. -/
lemma sum_blockMass_eq_weighted (T : Matrix (Fin n) (Fin n) ℂ) :
    (∑ m ∈ Finset.range n, blockMass T m)
      = ∑ i, ∑ j, (cutWeight n i j : ℝ) * Complex.normSq (T i j) := by
  classical
  -- Expand blockMass filters back to full sums with indicators.
  have step1 : (∑ m ∈ Finset.range n, blockMass T m)
      = ∑ m ∈ Finset.range n, ∑ i, ∑ j,
          (if i.val < m ∧ m ≤ j.val then Complex.normSq (T i j) else 0) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    unfold blockMass
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_filter]
    by_cases hi : i.val < m
    · simp only [hi, true_and, if_true]
    · simp only [hi, false_and, if_false]
      rw [Finset.sum_eq_zero]; intro j _; rfl
  rw [step1]
  -- Swap the m-sum to the innermost position.
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  -- ∑_m (if cond then normSq else 0) = (card of cond-set) • normSq = weight * normSq.
  unfold cutWeight
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/-- Each `cutWeight n i j` is nonnegative-valued and, on the strict-upper support
(`i.val < j.val`), is at least `1`: the cut `m = i.val + 1` satisfies
`i.val < m ≤ j.val`, and `m < n` since `m ≤ j.val < n`.
Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345. -/
lemma one_le_cutWeight_of_lt (i j : Fin n) (hij : i.val < j.val) :
    1 ≤ cutWeight n i j := by
  classical
  unfold cutWeight
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos]
  refine ⟨i.val + 1, ?_⟩
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨?_, ?_, ?_⟩
  · exact lt_of_le_of_lt hij j.isLt
  · omega
  · omega

/-- **Lower bound: `frobSq N ≤ ∑_{m ∈ range n} blockMass T m`.**  Here `N` is the
strict-upper part `N i j = if i < j then T i j else 0`.  Because every
strict-upper entry has cut-weight `≥ 1` and all weights/masses are nonnegative,
the weighted sum dominates the plain Frobenius mass of `N`.
Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345. -/
lemma frobSq_strictUpper_le_sum_blockMass (T N : Matrix (Fin n) (Fin n) ℂ)
    (hN : ∀ i j, N i j = if j > i then T i j else 0) :
    frobSq N ≤ ∑ m ∈ Finset.range n, blockMass T m := by
  classical
  rw [sum_blockMass_eq_weighted]
  unfold frobSq
  refine Finset.sum_le_sum fun i _ => ?_
  refine Finset.sum_le_sum fun j _ => ?_
  rw [hN i j]
  by_cases hij : j > i
  · rw [if_pos hij]
    have hw : (1 : ℝ) ≤ (cutWeight n i j : ℝ) := by
      have := one_le_cutWeight_of_lt i j (Fin.lt_def.mp hij)
      exact_mod_cast this
    calc Complex.normSq (T i j) = 1 * Complex.normSq (T i j) := (one_mul _).symm
      _ ≤ (cutWeight n i j : ℝ) * Complex.normSq (T i j) :=
            mul_le_mul_of_nonneg_right hw (Complex.normSq_nonneg _)
  · rw [if_neg hij, Complex.normSq_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)

/-! ### The Henrici inequality with an explicit constant -/

/-- **Henrici's departure constant (this file's explicit, non-sharp value)**
`cₙ = ∑_{m ∈ range n} √m = ∑_{m=1}^{n-1} √m`.  Higham's SHARP constant is
`((n³−n)/12)^{1/2}`; `henriciConst` is provably valid but weaker (see the file
header honesty ledger).  Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345. -/
noncomputable def henriciConst (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.range n, Real.sqrt m

/-- `henriciConst n ≥ 0`. -/
lemma henriciConst_nonneg (n : ℕ) : 0 ≤ henriciConst n :=
  Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _

/-- **Henrici's departure-from-normality inequality (explicit-constant form).**
For upper-triangular `T` with strict-upper part `N`,
```
      ‖N‖_F²  ≤  henriciConst n · ‖Tᴴ T − T Tᴴ‖_F.
```
This is the squared Henrici bound `Δ_F² ≤ c · ‖A*A − A A*‖_F` evaluated at the
Schur factor (`henriciConst n` in place of Higham's sharp `((n³−n)/12)^{1/2}`).
Proof: sum the block-mass bound `blockMass T m ≤ √m · ‖C‖_F` over the cuts
`m ∈ range n`, using `frobSq N ≤ ∑_m blockMass T m`.
Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345 (Henrici display). -/
theorem henrici_frobSq_le (T N : Matrix (Fin n) (Fin n) ℂ)
    (hTtri : ∀ i j, j < i → T i j = 0)
    (hN : ∀ i j, N i j = if j > i then T i j else 0) :
    frobSq N ≤ henriciConst n * frobNormC (selfComm T) := by
  calc frobSq N ≤ ∑ m ∈ Finset.range n, blockMass T m :=
        frobSq_strictUpper_le_sum_blockMass T N hN
    _ ≤ ∑ m ∈ Finset.range n, Real.sqrt m * frobNormC (selfComm T) :=
        Finset.sum_le_sum fun m _ => blockMass_le T hTtri m
    _ = henriciConst n * frobNormC (selfComm T) := by
        unfold henriciConst
        rw [Finset.sum_mul]

/-! ### Transport through the Schur form (unitary invariance of the commutator) -/

/-- **Unitary invariance of the self-commutator's Frobenius norm.**  For unitary
`U` and `T = Uᴴ A U`, `frobNormC (selfComm T) = frobNormC (selfComm A)`.  The
commutator conjugates, `selfComm (Uᴴ A U) = Uᴴ (selfComm A) U`, and `frobSq` is
unitarily invariant (`frobSq_unitary_conj`).
Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345 (the commutator norm is
computed on the Schur factor). -/
lemma frobNormC_selfComm_unitary_conj (A U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    frobNormC (selfComm (Uᴴ * A * U)) = frobNormC (selfComm A) := by
  have hUUh : U * Uᴴ = 1 := by
    have := (Matrix.mem_unitaryGroup_iff (A := U)).mp hU
    rwa [Matrix.star_eq_conjTranspose] at this
  have hUhU : Uᴴ * U = 1 := by
    have := (Matrix.mem_unitaryGroup_iff' (A := U)).mp hU
    rwa [Matrix.star_eq_conjTranspose] at this
  -- selfComm (Uᴴ A U) = Uᴴ (selfComm A) U.
  have hconj : selfComm (Uᴴ * A * U) = Uᴴ * (selfComm A) * U := by
    unfold selfComm
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, Matrix.mul_sub, Matrix.sub_mul]
    congr 1
    · -- (Uᴴ Aᴴ U)(Uᴴ A U) = Uᴴ (Aᴴ A) U
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc U Uᴴ (A * U), hUUh, Matrix.one_mul]
    · -- (Uᴴ A U)(Uᴴ Aᴴ U) = Uᴴ (A Aᴴ) U
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc U Uᴴ (Aᴴ * U), hUUh, Matrix.one_mul]
  unfold frobNormC
  rw [hconj, frobSq_unitary_conj (selfComm A) U hU]

/-- **Henrici's inequality transported to `A` via its Schur form.**  If
`Uᴴ A U = T = D + N` is a Schur form of `A`, then the (squared) departure from
normality obeys
```
      Δ_F(A)² = frobSq N  ≤  henriciConst n · ‖Aᴴ A − A Aᴴ‖_F,
```
where the commutator norm is the *unitarily invariant* Frobenius norm of
`Aᴴ A − A Aᴴ` (equal to that of `Tᴴ T − T Tᴴ`).  This is Higham's Henrici
display with the explicit constant `henriciConst n` in place of the sharp
`((n³−n)/12)^{1/2}`.  Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345. -/
theorem henrici_departure_le_of_schur
    (A U T N : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hUeq : Uᴴ * A * U = T)
    (hTtri : ∀ i j, j < i → T i j = 0)
    (hN : ∀ i j, N i j = if j > i then T i j else 0) :
    departureFSq N ≤ henriciConst n * frobNormC (selfComm A) := by
  rw [departureFSq_eq]
  have hbase := henrici_frobSq_le T N hTtri hN
  rw [← hUeq, frobNormC_selfComm_unitary_conj A U hU] at hbase
  exact hbase

end NumStability
