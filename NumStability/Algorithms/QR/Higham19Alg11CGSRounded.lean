import NumStability.Algorithms.QR.GramSchmidt
import NumStability.Algorithms.Norm2

/-!
# Rounded classical Gram-Schmidt (Higham Algorithm 19.11)

Source: N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
SIAM 2002, Chapter 19 (QR factorization), Algorithm 19.11 (classical
Gram-Schmidt, CGS), page 373; the error analysis of the underlying inner
products and normalization uses Lemma 3.4 / equations (3.3)-(3.5) (page 63) and
the `gamma`/`gamma-tilde` device of page 68 and page 357.

The repository already carries the *exact*-arithmetic CGS skeleton
(`ClassicalGramSchmidtState`, `classicalGramSchmidtResidual`,
`Algorithm19_11.State`) in `GramSchmidt.lean`, but no floating-point CGS kernel.
This file supplies:

* `fl_classicalGramSchmidt`, the rounded CGS loop assembled entirely from the
  repository's rounded inner-product (`fl_dotProduct`), rounded Euclidean-norm
  (`fl_norm2`) and rounded-division (`FPModel.fl_div`) kernels;
* `ClassicalGramSchmidtRoundedState`, the honest floating-point analogue of the
  exact `ClassicalGramSchmidtState`: each defining equation of Algorithm 19.11
  holds up to an explicit, bounded perturbation, under a nonzero
  *computed*-residual-norm hypothesis (the honest CGS analogue of the MGS
  nonzero-pivot hypothesis);
* `fl_classicalGramSchmidt_roundedState`, the theorem that the kernel meets that
  contract with a `gamma`-class column error.

## Honest statement strength

Higham leaves the integer constant `c` in `gamma-tilde_n = gamma_{cn}`
unspecified (page 357).  Accordingly every bound proved here is stated with an
*explicit* `gamma fp (index)` whose integer index is what the proof actually
delivers (never the printed `c`), and is documented as a `gamma-tilde`-class
constant rather than the printed constant.  No conclusion is smuggled into a
hypothesis.
-/

namespace NumStability

open scoped BigOperators

noncomputable section

/-!
## The rounded CGS kernel

For column `j` the exact algorithm computes, in order,

* `r_ij = q_i^T a_j` for `i < j`   (inner products, length `m`);
* `s_j  = a_j - sum_{k<j} r_kj q_k` (the residual);
* `r_jj = ||s_j||_2`;
* `q_j  = s_j / r_jj`.

We reuse `fl_dotProduct` for the off-diagonal `r_ij`, model the residual entry
`s_ij` as one length-`(j+1)` rounded dot product of the coefficient row
`[1, -r_0j, ..., -r_{j-1,j}]` against the data row `[a_ij, q_i0, ..., q_i(j-1)]`
(this is exactly Higham's inner-product view of the projection subtraction,
§3.1, equation (3.3), page 63), `fl_norm2` for `r_jj`, and `FPModel.fl_div` for
the componentwise normalization.

The mutual dependence of column `j` on columns `< j` is resolved by an
incremental `Nat` recursion `flCGSAux`: stage `t` holds a `(Q, R)` pair whose
columns `< t` already equal the CGS-computed columns, and whose remaining
columns are placeholder zeros.  `fl_classicalGramSchmidt` reads off stage `n`.
-/

/-- Coefficient row `[1, -r_0j, ..., -r_{j-1,j}]` used to form the residual entry
of CGS column `j` as a single rounded dot product (Higham Alg. 19.11, the
`a_j - sum_{k<j} r_kj q_k` line, page 373). -/
def flCGSCoeff {n : Nat} (R : Fin n -> Fin n -> Real) (j : Fin n) :
    Fin (j.val + 1) -> Real :=
  fun t =>
    if _h : t.val = 0 then 1
    else
      -(R ⟨t.val - 1, by omega⟩ j)

/-- Data row `[a_ij, q_i0, ..., q_i(j-1)]` paired with `flCGSCoeff` to form the
residual entry of CGS column `j` at row `i` (Higham Alg. 19.11, page 373). -/
def flCGSRow {m n : Nat} (A Q : Fin m -> Fin n -> Real) (i : Fin m) (j : Fin n) :
    Fin (j.val + 1) -> Real :=
  fun t =>
    if _h : t.val = 0 then A i j
    else
      Q i ⟨t.val - 1, by omega⟩

/-- Rounded residual entry `s_ij` of CGS column `j` at row `i`, computed as one
length-`(j+1)` rounded dot product of the coefficient row against the data row
(Higham Alg. 19.11, page 373; inner-product model of §3.1, equation (3.3),
page 63). -/
def flCGSResidualEntry {m n : Nat} (fp : FPModel)
    (A Q : Fin m -> Fin n -> Real) (R : Fin n -> Fin n -> Real)
    (i : Fin m) (j : Fin n) : Real :=
  fl_dotProduct fp (j.val + 1) (flCGSCoeff R j) (flCGSRow A Q i j)

/-- The rounded residual column `s_j` of CGS column `j` (Higham Alg. 19.11,
page 373). -/
def flCGSResidual {m n : Nat} (fp : FPModel)
    (A Q : Fin m -> Fin n -> Real) (R : Fin n -> Fin n -> Real)
    (j : Fin n) : Fin m -> Real :=
  fun i => flCGSResidualEntry fp A Q R i j

/-- Stage-1 `R` update inside one CGS step: fill the strict-upper column-`j`
entries with the rounded inner products `r_ij = fl(q_i^T a_j)`, leaving the
diagonal, the lower part and all other columns as in the incoming `R`.  The
residual of column `j` reads only these off-diagonal entries. -/
def flCGSRoff {m n : Nat} (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (Q : Fin m -> Fin n -> Real) (R : Fin n -> Fin n -> Real) (j : Fin n) :
    Fin n -> Fin n -> Real :=
  fun i k =>
    if k = j then
      if i.val < j.val then fl_dotProduct fp m (fun r => Q r i) (fun r => A r j)
      else R i k
    else R i k

/-- One incremental CGS stage: given the `(Q, R)` pair with columns `< j`
already filled, fill column `j`.

Row `j` of `R` above the diagonal gets the rounded inner products
`r_ij = fl(q_i^T a_j)` (via `flCGSRoff`); the diagonal `r_jj` gets `fl_norm2` of
the rounded residual `s_j`; and column `j` of `Q` gets the componentwise rounded
quotient `fl(s_ij / r_jj)`.  Entries outside column `j` are copied through
unchanged (Higham Alg. 19.11, page 373). -/
def flCGSStep {m n : Nat} (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (QR : (Fin m -> Fin n -> Real) × (Fin n -> Fin n -> Real)) (j : Fin n) :
    (Fin m -> Fin n -> Real) × (Fin n -> Fin n -> Real) :=
  let Q := QR.1
  let R := QR.2
  let Roff : Fin n -> Fin n -> Real := flCGSRoff fp A Q R j
  let rjj : Real := fl_norm2 fp m (flCGSResidual fp A Q Roff j)
  let R' : Fin n -> Fin n -> Real := fun i k =>
    if k = j then (if i = j then rjj else Roff i k) else R i k
  let Q' : Fin m -> Fin n -> Real := fun i k =>
    if k = j then fp.fl_div (flCGSResidualEntry fp A Q Roff i j) rjj
    else Q i k
  (Q', R')

/-- Incremental CGS data after processing columns `0, ..., t-1`.  Columns `< t`
of both factors equal the CGS-computed columns; the remaining columns are
placeholder zeros (Higham Alg. 19.11, page 373). -/
def flCGSAux {m n : Nat} (fp : FPModel) (A : Fin m -> Fin n -> Real) :
    Nat -> (Fin m -> Fin n -> Real) × (Fin n -> Fin n -> Real)
  | 0 => (fun _ _ => 0, fun _ _ => 0)
  | t + 1 =>
      if ht : t < n then
        flCGSStep fp A (flCGSAux fp A t) ⟨t, ht⟩
      else
        flCGSAux fp A t

/-- Computed CGS factor `Q-hat` (Higham Alg. 19.11, page 373). -/
def fl_classicalGramSchmidtQ {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) : Fin m -> Fin n -> Real :=
  (flCGSAux fp A n).1

/-- Computed CGS factor `R-hat` (Higham Alg. 19.11, page 373). -/
def fl_classicalGramSchmidtR {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) : Fin n -> Fin n -> Real :=
  (flCGSAux fp A n).2

/-- The rounded classical Gram-Schmidt kernel of Higham Algorithm 19.11
(page 373), packaged as the computed `(Q-hat, R-hat)` pair. -/
def fl_classicalGramSchmidt {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) :
    (Fin m -> Fin n -> Real) × (Fin n -> Fin n -> Real) :=
  (fl_classicalGramSchmidtQ fp A, fl_classicalGramSchmidtR fp A)

/-- Reindex a `Fin n` sum guarded by `k.val < j.val` to a `Fin j.val` sum.  This
is the bookkeeping bridge between the algorithm's projection sum (indexed over
`Fin n` as in `classicalGramSchmidtResidual`) and the length-`(j+1)` dot-product
tail (indexed over `Fin j.val`). -/
theorem flCGS_sum_guard_eq {n : Nat} (j : Fin n) (F : Fin n -> Real) :
    (∑ k : Fin n, if k.val < j.val then F k else 0) =
      ∑ t : Fin j.val, F ⟨t.val, Nat.lt_trans t.isLt j.isLt⟩ := by
  rw [← Finset.sum_filter]
  refine (Finset.sum_bij'
    (i := fun (t : Fin j.val) (_ : t ∈ (Finset.univ : Finset (Fin j.val))) =>
      (⟨t.val, Nat.lt_trans t.isLt j.isLt⟩ : Fin n))
    (j := fun (k : Fin n) (hk : k ∈ (Finset.univ.filter (fun k => k.val < j.val))) =>
      (⟨k.val, (Finset.mem_filter.mp hk).2⟩ : Fin j.val))
    ?_ ?_ ?_ ?_ ?_).symm
  · intro t _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, t.isLt⟩
  · intro k _
    exact Finset.mem_univ _
  · intro t _; rfl
  · intro k _; rfl
  · intro t _; rfl

/-!
## Residual backward error (the load-bearing atom)

The following lemma is the honest floating-point core of Algorithm 19.11.  It
holds for *arbitrary* `Q` and `R`, so it is independent of the recursion: the
computed residual entry equals the exact classical Gram-Schmidt residual formula
`A_ij - sum_{k<j} R_kj Q_ik` perturbed by a term bounded by
`gamma fp (j+1)` times `|A_ij| + sum_{k<j} |R_kj| |Q_ik|`.  This is exactly the
inner-product backward error of Higham §3.1, equation (3.3) (page 63) applied to
the projection-subtraction line of the algorithm.
-/

/-- Expand the coefficient/data-row dot product of `flCGSResidualEntry` into the
`A` term and the projection terms, exposing the componentwise dot-product
relative errors of Higham §3.1, equation (3.3) (page 63).  The projection sum is
written over `Fin j.val`, one term per already-computed column. -/
theorem flCGSResidualEntry_backward_error {m n : Nat} (fp : FPModel)
    (A Q : Fin m -> Fin n -> Real) (R : Fin n -> Fin n -> Real)
    (i : Fin m) (j : Fin n) (hj : gammaValid fp (j.val + 1)) :
    ∃ eta : Fin (j.val + 1) -> Real,
      (∀ t, |eta t| ≤ gamma fp (j.val + 1)) ∧
      flCGSResidualEntry fp A Q R i j =
        A i j * (1 + eta 0) -
          ∑ t : Fin j.val,
            R ⟨t.val, Nat.lt_trans t.isLt j.isLt⟩ j *
              Q i ⟨t.val, Nat.lt_trans t.isLt j.isLt⟩ * (1 + eta t.succ) := by
  obtain ⟨eta, heta, hdot⟩ :=
    dotProduct_backward_error fp (j.val + 1)
      (flCGSCoeff R j) (flCGSRow A Q i j) hj
  refine ⟨eta, heta, ?_⟩
  rw [flCGSResidualEntry, hdot]
  -- Split off index 0 and re-index the tail sum over `Fin j.val`.
  rw [Fin.sum_univ_succ]
  have h0 :
      flCGSCoeff R j 0 * flCGSRow A Q i j 0 * (1 + eta 0) =
        A i j * (1 + eta 0) := by
    simp [flCGSCoeff, flCGSRow]
  rw [h0]
  -- The tail term at `t.succ` is `-(R k j) * Q i k` with `k = ⟨t.val,_⟩`.
  have htail :
      (∑ t : Fin j.val,
          flCGSCoeff R j t.succ * flCGSRow A Q i j t.succ *
            (1 + eta t.succ)) =
        -∑ t : Fin j.val,
          R ⟨t.val, Nat.lt_trans t.isLt j.isLt⟩ j *
            Q i ⟨t.val, Nat.lt_trans t.isLt j.isLt⟩ * (1 + eta t.succ) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro t _
    have hcoeff :
        flCGSCoeff R j t.succ = -(R ⟨t.val, Nat.lt_trans t.isLt j.isLt⟩ j) := by
      simp only [flCGSCoeff, Fin.val_succ]
      rw [dif_neg (by omega)]
      congr 2
    have hrow :
        flCGSRow A Q i j t.succ = Q i ⟨t.val, Nat.lt_trans t.isLt j.isLt⟩ := by
      simp only [flCGSRow, Fin.val_succ]
      rw [dif_neg (by omega)]
      congr 2
    rw [hcoeff, hrow]
    ring
  rw [htail]
  ring

/-- The exact classical Gram-Schmidt residual formula rewritten with its
projection sum reindexed over `Fin j.val` (using `flCGS_sum_guard_eq`).  This is
the exact object the computed residual is compared against. -/
theorem classicalGramSchmidtResidual_eq_finTail {m n : Nat}
    (A Q : Fin m -> Fin n -> Real) (R : Fin n -> Fin n -> Real)
    (i : Fin m) (j : Fin n) :
    classicalGramSchmidtResidual A Q R j i =
      A i j -
        ∑ t : Fin j.val,
          R ⟨t.val, Nat.lt_trans t.isLt j.isLt⟩ j *
            Q i ⟨t.val, Nat.lt_trans t.isLt j.isLt⟩ := by
  rw [classicalGramSchmidtResidual]
  congr 1
  exact flCGS_sum_guard_eq j (fun k => R k j * Q i k)

/-- **Rounded CGS residual, columnwise backward error** (Higham Alg. 19.11,
page 373; inner-product model of §3.1, equation (3.3), page 63).

The computed residual entry `s_ij` differs from the exact classical
Gram-Schmidt residual `(a_j - sum_{k<j} r_kj q_k)_i` by a perturbation bounded
by `gamma fp (j+1)` times the sum of magnitudes `|A_ij| + sum_{k<j} |R_kj Q_ik|`
of the terms that entered the projection subtraction.  This holds for arbitrary
`Q` and `R`; it is the honest floating-point core of the algorithm and is
independent of the CGS recursion. -/
theorem flCGSResidual_backward_error {m n : Nat} (fp : FPModel)
    (A Q : Fin m -> Fin n -> Real) (R : Fin n -> Fin n -> Real)
    (i : Fin m) (j : Fin n) (hj : gammaValid fp (j.val + 1)) :
    |flCGSResidualEntry fp A Q R i j -
        classicalGramSchmidtResidual A Q R j i| ≤
      gamma fp (j.val + 1) *
        (|A i j| +
          ∑ t : Fin j.val,
            |R ⟨t.val, Nat.lt_trans t.isLt j.isLt⟩ j| *
              |Q i ⟨t.val, Nat.lt_trans t.isLt j.isLt⟩|) := by
  obtain ⟨eta, heta, hexp⟩ :=
    flCGSResidualEntry_backward_error fp A Q R i j hj
  rw [hexp, classicalGramSchmidtResidual_eq_finTail]
  -- The difference is `A i j * eta 0 - sum R Q eta t.succ`.
  have hdiff :
      (A i j * (1 + eta 0) -
          ∑ t : Fin j.val,
            R ⟨t.val, Nat.lt_trans t.isLt j.isLt⟩ j *
              Q i ⟨t.val, Nat.lt_trans t.isLt j.isLt⟩ * (1 + eta t.succ)) -
        (A i j -
          ∑ t : Fin j.val,
            R ⟨t.val, Nat.lt_trans t.isLt j.isLt⟩ j *
              Q i ⟨t.val, Nat.lt_trans t.isLt j.isLt⟩) =
      A i j * eta 0 -
        ∑ t : Fin j.val,
          R ⟨t.val, Nat.lt_trans t.isLt j.isLt⟩ j *
            Q i ⟨t.val, Nat.lt_trans t.isLt j.isLt⟩ * eta t.succ := by
    have hsum :
        (∑ t : Fin j.val,
            R ⟨t.val, Nat.lt_trans t.isLt j.isLt⟩ j *
              Q i ⟨t.val, Nat.lt_trans t.isLt j.isLt⟩ * (1 + eta t.succ)) -
          (∑ t : Fin j.val,
            R ⟨t.val, Nat.lt_trans t.isLt j.isLt⟩ j *
              Q i ⟨t.val, Nat.lt_trans t.isLt j.isLt⟩) =
          ∑ t : Fin j.val,
            R ⟨t.val, Nat.lt_trans t.isLt j.isLt⟩ j *
              Q i ⟨t.val, Nat.lt_trans t.isLt j.isLt⟩ * eta t.succ := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro t _
      ring
    linarith [hsum]
  rw [hdiff]
  -- Triangle inequality and termwise `|eta| ≤ gamma` bound.
  set g := gamma fp (j.val + 1) with hg
  calc
    |A i j * eta 0 -
          ∑ t : Fin j.val,
            R ⟨t.val, Nat.lt_trans t.isLt j.isLt⟩ j *
              Q i ⟨t.val, Nat.lt_trans t.isLt j.isLt⟩ * eta t.succ|
        ≤ |A i j * eta 0| +
            |∑ t : Fin j.val,
              R ⟨t.val, Nat.lt_trans t.isLt j.isLt⟩ j *
                Q i ⟨t.val, Nat.lt_trans t.isLt j.isLt⟩ * eta t.succ| :=
          abs_sub _ _
    _ ≤ |A i j| * g +
            ∑ t : Fin j.val,
              |R ⟨t.val, Nat.lt_trans t.isLt j.isLt⟩ j| *
                |Q i ⟨t.val, Nat.lt_trans t.isLt j.isLt⟩| * g := by
          apply add_le_add
          · rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (heta 0) (abs_nonneg _)
          · refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
            apply Finset.sum_le_sum
            intro t _
            rw [abs_mul, abs_mul]
            exact mul_le_mul_of_nonneg_left (heta t.succ)
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = g * (|A i j| +
            ∑ t : Fin j.val,
              |R ⟨t.val, Nat.lt_trans t.isLt j.isLt⟩ j| *
                |Q i ⟨t.val, Nat.lt_trans t.isLt j.isLt⟩|) := by
          rw [mul_add, Finset.mul_sum]
          congr 1
          · ring
          · apply Finset.sum_congr rfl
            intro t _
            ring

/-!
## Locality and stability of the incremental recursion

`flCGSStep` writes only its own column `j`; consequently every column `< t` of
`flCGSAux fp A t` is frozen under all later stages.  These bookkeeping lemmas
connect the recursion to the per-column backward-error atoms above.
-/

/-- `flCGSStep` leaves columns other than `j` of the `R` factor unchanged. -/
theorem flCGSStep_R_of_ne {m n : Nat} (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (QR : (Fin m -> Fin n -> Real) × (Fin n -> Fin n -> Real))
    (j : Fin n) (i k : Fin n) (hk : k ≠ j) :
    (flCGSStep fp A QR j).2 i k = QR.2 i k := by
  simp [flCGSStep, hk]

/-- `flCGSStep` leaves columns other than `j` of the `Q` factor unchanged. -/
theorem flCGSStep_Q_of_ne {m n : Nat} (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (QR : (Fin m -> Fin n -> Real) × (Fin n -> Fin n -> Real))
    (j : Fin n) (i : Fin m) (k : Fin n) (hk : k ≠ j) :
    (flCGSStep fp A QR j).1 i k = QR.1 i k := by
  simp [flCGSStep, hk]

/-- `flCGSRoff` fills the strict-upper column-`j` entries with the rounded inner
products (Higham Alg. 19.11, page 373). -/
theorem flCGSRoff_offDiag {m n : Nat} (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (Q : Fin m -> Fin n -> Real) (R : Fin n -> Fin n -> Real)
    (j : Fin n) (i : Fin n) (hij : i.val < j.val) :
    flCGSRoff fp A Q R j i j =
      fl_dotProduct fp m (fun r => Q r i) (fun r => A r j) := by
  simp only [flCGSRoff, if_true]
  rw [if_pos hij]

/-- The off-diagonal `R` entries in column `j` produced by `flCGSStep` are the
rounded inner products `fl(q_i^T a_j)` (Higham Alg. 19.11, page 373). -/
theorem flCGSStep_R_offDiag {m n : Nat} (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (QR : (Fin m -> Fin n -> Real) × (Fin n -> Fin n -> Real))
    (j : Fin n) (i : Fin n) (hij : i.val < j.val) :
    (flCGSStep fp A QR j).2 i j =
      fl_dotProduct fp m (fun r => QR.1 r i) (fun r => A r j) := by
  have hne : ¬ (i = j) := by
    intro h; rw [h] at hij; exact Nat.lt_irrefl j.val hij
  simp only [flCGSStep, if_true]
  rw [if_neg hne]
  exact flCGSRoff_offDiag fp A QR.1 QR.2 j i hij

/-- The diagonal `R` entry in column `j` produced by `flCGSStep` is the rounded
Euclidean norm of the computed residual (Higham Alg. 19.11, page 373). -/
theorem flCGSStep_R_diag {m n : Nat} (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (QR : (Fin m -> Fin n -> Real) × (Fin n -> Fin n -> Real)) (j : Fin n) :
    (flCGSStep fp A QR j).2 j j =
      fl_norm2 fp m (flCGSResidual fp A QR.1 (flCGSRoff fp A QR.1 QR.2 j) j) := by
  simp only [flCGSStep, if_true]

/-- The column-`j` entries of the `Q` factor produced by `flCGSStep` are the
componentwise rounded quotients `fl(s_ij / r_jj)` (Higham Alg. 19.11,
page 373). -/
theorem flCGSStep_Q_col {m n : Nat} (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (QR : (Fin m -> Fin n -> Real) × (Fin n -> Fin n -> Real))
    (j : Fin n) (i : Fin m) :
    (flCGSStep fp A QR j).1 i j =
      fp.fl_div
        (flCGSResidualEntry fp A QR.1 (flCGSRoff fp A QR.1 QR.2 j) i j)
        (fl_norm2 fp m (flCGSResidual fp A QR.1 (flCGSRoff fp A QR.1 QR.2 j) j)) := by
  simp only [flCGSStep, if_true]

/-- One `flCGSAux` step advances stage `t` to `t+1` by applying `flCGSStep` at
column `t` (when `t < n`). -/
theorem flCGSAux_succ {m n : Nat} (fp : FPModel) (A : Fin m -> Fin n -> Real)
    {t : Nat} (ht : t < n) :
    flCGSAux fp A (t + 1) = flCGSStep fp A (flCGSAux fp A t) ⟨t, ht⟩ := by
  simp [flCGSAux, ht]

/-- Master stability lemma for the `R` factor: a column `k` with `k.val < t` is
frozen from stage `t` onward. -/
theorem flCGSAux_R_stable {m n : Nat} (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (t : Nat) (i k : Fin n) (hk : k.val < t) :
    ∀ s : Nat, t ≤ s →
      (flCGSAux fp A s).2 i k = (flCGSAux fp A t).2 i k := by
  intro s hts
  induction s with
  | zero =>
      have : t = 0 := Nat.le_zero.mp hts
      omega
  | succ s ih =>
      rcases Nat.lt_or_ge t (s + 1) with hlt | hge
      · -- t ≤ s, so use ih and the step at column s (≠ k since k.val < t ≤ s)
        have hts' : t ≤ s := Nat.lt_succ_iff.mp hlt
        by_cases hsn : s < n
        · rw [flCGSAux_succ fp A hsn]
          have hne : (⟨s, hsn⟩ : Fin n) ≠ k := by
            intro h
            have : s = k.val := congrArg Fin.val h.symm ▸ rfl
            omega
          rw [flCGSStep_R_of_ne fp A (flCGSAux fp A s) ⟨s, hsn⟩ i k
            (fun h => hne h.symm)]
          exact ih hts'
        · -- s ≥ n: stage is stationary
          have : flCGSAux fp A (s + 1) = flCGSAux fp A s := by
            simp [flCGSAux, hsn]
          rw [this]
          exact ih hts'
      · -- t = s + 1
        have : t = s + 1 := Nat.le_antisymm hts hge
        rw [this]

/-- Master stability lemma for the `Q` factor: a column `k` with `k.val < t` is
frozen from stage `t` onward. -/
theorem flCGSAux_Q_stable {m n : Nat} (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (t : Nat) (i : Fin m) (k : Fin n) (hk : k.val < t) :
    ∀ s : Nat, t ≤ s →
      (flCGSAux fp A s).1 i k = (flCGSAux fp A t).1 i k := by
  intro s hts
  induction s with
  | zero =>
      have : t = 0 := Nat.le_zero.mp hts
      omega
  | succ s ih =>
      rcases Nat.lt_or_ge t (s + 1) with hlt | hge
      · have hts' : t ≤ s := Nat.lt_succ_iff.mp hlt
        by_cases hsn : s < n
        · rw [flCGSAux_succ fp A hsn]
          have hne : (⟨s, hsn⟩ : Fin n) ≠ k := by
            intro h
            have : s = k.val := congrArg Fin.val h.symm ▸ rfl
            omega
          rw [flCGSStep_Q_of_ne fp A (flCGSAux fp A s) ⟨s, hsn⟩ i k
            (fun h => hne h.symm)]
          exact ih hts'
        · have : flCGSAux fp A (s + 1) = flCGSAux fp A s := by
            simp [flCGSAux, hsn]
          rw [this]
          exact ih hts'
      · have : t = s + 1 := Nat.le_antisymm hts hge
        rw [this]

/-!
## Connecting the recursion to the computed factors

Column `j` of the computed factors equals what stage `j+1` produced (the
step at column `j`), because later stages freeze column `j`.  The step's *input*
`Q` has columns `< j` equal to the final computed columns, again by stability.
-/

/-- The step-`j` input `Q` (stage `j.val`) agrees with the final computed `Q`
on every column `< j`. -/
theorem flCGSAux_input_Q_eq_final {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) (i : Fin m) (k j : Fin n)
    (hkj : k.val < j.val) :
    (flCGSAux fp A j.val).1 i k = fl_classicalGramSchmidtQ fp A i k := by
  have hstab :=
    flCGSAux_Q_stable fp A (k.val + 1) i k (Nat.lt_succ_self k.val)
  have hjn : j.val ≤ n := Nat.le_of_lt j.isLt
  rw [fl_classicalGramSchmidtQ]
  rw [hstab n (le_trans (Nat.succ_le_of_lt hkj) (le_trans (Nat.le_of_lt j.isLt) (le_refl n)))]
  rw [hstab j.val (Nat.succ_le_of_lt hkj)]

/-- Column `j` of the computed `R` factor equals the step-`j` output.  -/
theorem fl_classicalGramSchmidtR_col {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) (i j : Fin n) :
    fl_classicalGramSchmidtR fp A i j =
      (flCGSStep fp A (flCGSAux fp A j.val) j).2 i j := by
  rw [fl_classicalGramSchmidtR]
  have hstep : flCGSAux fp A (j.val + 1) =
      flCGSStep fp A (flCGSAux fp A j.val) ⟨j.val, j.isLt⟩ := flCGSAux_succ fp A j.isLt
  have hj' : (⟨j.val, j.isLt⟩ : Fin n) = j := rfl
  rw [hj'] at hstep
  have hstab :=
    flCGSAux_R_stable fp A (j.val + 1) i j (Nat.lt_succ_self j.val) n
      (Nat.succ_le_of_lt j.isLt)
  rw [hstab, hstep]

/-- Column `j` of the computed `Q` factor equals the step-`j` output. -/
theorem fl_classicalGramSchmidtQ_col {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) (i : Fin m) (j : Fin n) :
    fl_classicalGramSchmidtQ fp A i j =
      (flCGSStep fp A (flCGSAux fp A j.val) j).1 i j := by
  rw [fl_classicalGramSchmidtQ]
  have hstep : flCGSAux fp A (j.val + 1) =
      flCGSStep fp A (flCGSAux fp A j.val) ⟨j.val, j.isLt⟩ := flCGSAux_succ fp A j.isLt
  have hj' : (⟨j.val, j.isLt⟩ : Fin n) = j := rfl
  rw [hj'] at hstep
  have hstab :=
    flCGSAux_Q_stable fp A (j.val + 1) i j (Nat.lt_succ_self j.val) n
      (Nat.succ_le_of_lt j.isLt)
  rw [hstab, hstep]

/-!
## Final-factor relations of Algorithm 19.11

The following lemmas describe the *computed* factors `Q-hat`, `R-hat` directly,
each an exact identity that the honest rounded-state contract records with its
rounding error.  Write `Qhat = fl_classicalGramSchmidtQ fp A`,
`Rhat = fl_classicalGramSchmidtR fp A`.
-/

/-- **Off-diagonal identity** (Higham Alg. 19.11, page 373): the computed
strict-upper `R-hat` entry is the rounded inner product of the computed `q-hat_i`
column with the input column `a_j`. -/
theorem fl_classicalGramSchmidtR_offDiag {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) (i j : Fin n) (hij : i.val < j.val) :
    fl_classicalGramSchmidtR fp A i j =
      fl_dotProduct fp m
        (fun r => fl_classicalGramSchmidtQ fp A r i) (fun r => A r j) := by
  rw [fl_classicalGramSchmidtR_col, flCGSStep_R_offDiag fp A _ j i hij]
  congr 1
  funext r
  exact flCGSAux_input_Q_eq_final fp A r i j hij

/-- The step-`j` off-diagonal helper `Roff` agrees with the final computed `R`
factor on the strict-upper column-`j` entries. -/
theorem flCGSRoff_eq_final {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) (i j : Fin n) (hij : i.val < j.val) :
    flCGSRoff fp A (flCGSAux fp A j.val).1 (flCGSAux fp A j.val).2 j i j =
      fl_classicalGramSchmidtR fp A i j := by
  rw [flCGSRoff_offDiag fp A _ _ j i hij, fl_classicalGramSchmidtR_offDiag fp A i j hij]
  congr 1
  funext r
  exact (flCGSAux_input_Q_eq_final fp A r i j hij)

/-- The step-`j` residual entry equals the residual entry evaluated on the final
computed factors `Q-hat`, `R-hat`.  Both the coefficient row (off-diagonal `R`)
and the data row (columns `< j` of `Q`) coincide with their final values. -/
theorem flCGSStep_residualEntry_eq_final {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) (i : Fin m) (j : Fin n) :
    flCGSResidualEntry fp A (flCGSAux fp A j.val).1
        (flCGSRoff fp A (flCGSAux fp A j.val).1 (flCGSAux fp A j.val).2 j) i j =
      flCGSResidualEntry fp A (fl_classicalGramSchmidtQ fp A)
        (fl_classicalGramSchmidtR fp A) i j := by
  unfold flCGSResidualEntry
  congr 1
  · -- coefficient rows agree
    funext t
    have ht : t.val < j.val + 1 := t.isLt
    simp only [flCGSCoeff]
    by_cases h0 : t.val = 0
    · rw [dif_pos h0, dif_pos h0]
    · rw [dif_neg h0, dif_neg h0]
      have hlt : t.val - 1 < j.val := by omega
      congr 1
      exact flCGSRoff_eq_final fp A ⟨t.val - 1, Nat.lt_trans hlt j.isLt⟩ j hlt
  · -- data rows agree
    funext t
    have ht : t.val < j.val + 1 := t.isLt
    simp only [flCGSRow]
    by_cases h0 : t.val = 0
    · rw [dif_pos h0, dif_pos h0]
    · rw [dif_neg h0, dif_neg h0]
      have hlt : t.val - 1 < j.val := by omega
      exact flCGSAux_input_Q_eq_final fp A i ⟨t.val - 1, Nat.lt_trans hlt j.isLt⟩ j hlt

/-- The step-`j` residual column equals the residual column on the final computed
factors. -/
theorem flCGSStep_residual_eq_final {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) (j : Fin n) :
    flCGSResidual fp A (flCGSAux fp A j.val).1
        (flCGSRoff fp A (flCGSAux fp A j.val).1 (flCGSAux fp A j.val).2 j) j =
      flCGSResidual fp A (fl_classicalGramSchmidtQ fp A)
        (fl_classicalGramSchmidtR fp A) j := by
  funext i
  exact flCGSStep_residualEntry_eq_final fp A i j

/-- **Diagonal identity** (Higham Alg. 19.11, page 373): the computed diagonal
`R-hat` entry `r_jj` is the rounded Euclidean norm of the computed residual
column `s_j`, evaluated on the final factors. -/
theorem fl_classicalGramSchmidtR_diag {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) (j : Fin n) :
    fl_classicalGramSchmidtR fp A j j =
      fl_norm2 fp m
        (flCGSResidual fp A (fl_classicalGramSchmidtQ fp A)
          (fl_classicalGramSchmidtR fp A) j) := by
  rw [fl_classicalGramSchmidtR_col, flCGSStep_R_diag,
    flCGSStep_residual_eq_final]

/-- **Normalization identity** (Higham Alg. 19.11, page 373): the computed
`q-hat_ij` is the rounded quotient of the computed residual entry `s_ij` by the
diagonal `r_jj`, all evaluated on the final factors. -/
theorem fl_classicalGramSchmidtQ_normalized {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) (i : Fin m) (j : Fin n) :
    fl_classicalGramSchmidtQ fp A i j =
      fp.fl_div
        (flCGSResidualEntry fp A (fl_classicalGramSchmidtQ fp A)
          (fl_classicalGramSchmidtR fp A) i j)
        (fl_classicalGramSchmidtR fp A j j) := by
  rw [fl_classicalGramSchmidtQ_col, flCGSStep_Q_col,
    flCGSStep_residualEntry_eq_final, flCGSStep_residual_eq_final]
  rw [fl_classicalGramSchmidtR_diag]

/-- Below-diagonal `R` entries are the placeholder zeros at every stage: one CGS
step only writes on-diagonal and strict-upper column-`j` entries. -/
theorem flCGSAux_R_lower_zero {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) (t : Nat) (i j : Fin n) (hji : j.val < i.val) :
    (flCGSAux fp A t).2 i j = 0 := by
  induction t with
  | zero => simp [flCGSAux]
  | succ t ih =>
      by_cases htn : t < n
      · rw [flCGSAux_succ fp A htn]
        by_cases hjk : j = (⟨t, htn⟩ : Fin n)
        · -- column j is the active column; below-diagonal entry copies incoming R
          subst hjk
          simp only [flCGSStep, if_true]
          have hij : ¬ (i = (⟨t, htn⟩ : Fin n)) := by
            intro h; rw [h] at hji; exact Nat.lt_irrefl (⟨t, htn⟩ : Fin n).val hji
          rw [if_neg hij]
          have hnlt : ¬ (i.val < (⟨t, htn⟩ : Fin n).val) := Nat.not_lt_of_gt hji
          simp only [flCGSRoff, if_true]
          rw [if_neg hnlt]
          exact ih
        · rw [flCGSStep_R_of_ne fp A (flCGSAux fp A t) ⟨t, htn⟩ i j hjk]
          exact ih
      · have : flCGSAux fp A (t + 1) = flCGSAux fp A t := by simp [flCGSAux, htn]
        rw [this]; exact ih

/-- **Upper-trapezoidal shape** of the computed `R-hat` factor (Higham
Alg. 19.11, page 373).  This is an exact structural identity, carrying no
rounding error. -/
theorem fl_classicalGramSchmidtR_upperTrapezoidal {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) :
    IsUpperTrapezoidal n n (fl_classicalGramSchmidtR fp A) := by
  intro i j hji
  exact flCGSAux_R_lower_zero fp A n i j hji

/-!
## The rounded classical Gram-Schmidt state

`ClassicalGramSchmidtRoundedState` is the honest floating-point analogue of the
exact `ClassicalGramSchmidtState` (`GramSchmidt.lean`).  Each exact defining
equation of Algorithm 19.11 is replaced by the same equation *up to an explicit
bounded rounding perturbation*:

* `upper`        — exact upper-trapezoidal shape (no rounding);
* `projection`   — off-diagonal `R̂_ij` equals the exact inner product
                   `gsDot (q̂_i) (a_j)` up to a `gamma fp m`-class error
                   (`fl_dotProduct` backward error, §3.1 eq. (3.3), page 63);
* `diagonal`     — `R̂_jj` equals the exact residual norm
                   `gsColumnNorm2 (ŝ_j)` up to a `gamma fp (m+1)`-class relative
                   error (`fl_norm2`, Lemma 18.1 style, page 63/360);
* `normalized`   — `q̂_ij` equals the exact normalized entry
                   `gsNormalize (ŝ_j) (R̂_jj) i` up to a single rounding factor
                   `1 + δ`, `|δ| ≤ u` (rounded division, standard model (2.4),
                   page 40);
* `residual`     — the computed residual `ŝ_j` equals the exact classical
                   Gram-Schmidt residual `a_j - sum_{k<j} R̂_kj q̂_k`
                   (`classicalGramSchmidtResidual`) up to a `gamma fp (j+1)`-class
                   columnwise backward error, the honest CGS analogue of the MGS
                   backward-error result.

The residual column `ŝ_j` is the algorithm's *computed* residual
`flCGSResidual fp A Q̂ R̂ j`; the diagonal and normalization channels are stated
against this same `ŝ_j`, so the surface is internally consistent.

`hpivot` is the honest nonzero-*computed*-residual-norm hypothesis: the CGS
analogue of the MGS nonzero-pivot assumption `gsColumnNorm2 (stage) ≠ 0`.  It is
required only to unfold the rounded-division relative-error model on the diagonal.
-/

/-- Honest floating-point analogue of `ClassicalGramSchmidtState` for the rounded
classical Gram-Schmidt kernel of Higham Algorithm 19.11 (page 373).  See the
module note above for the meaning of each channel and the constant conventions
(`gamma`-class indices, not the printed integer `c` of page 357). -/
structure ClassicalGramSchmidtRoundedState {m n : Nat}
    (fp : FPModel) (A Q : Fin m -> Fin n -> Real) (R : Fin n -> Fin n -> Real)
    (s : Fin n -> Fin m -> Real) : Prop where
  /-- Exact upper-trapezoidal shape of the computed `R`. -/
  upper : IsUpperTrapezoidal n n R
  /-- Off-diagonal backward error: `R̂_ij = gsDot(q̂_i, a_j) + e`, `|e| ≤ γ_m·Σ|·|`. -/
  projection :
    forall i j : Fin n, i.val < j.val ->
      |R i j - gsDot (gsColumn Q i) (gsColumn A j)| ≤
        gamma fp m *
          (∑ r : Fin m, |gsColumn Q i r| * |gsColumn A j r|)
  /-- Diagonal relative error: `R̂_jj = gsColumnNorm2(ŝ_j)·(1+θ)`, `|θ| ≤ γ_{m+1}`. -/
  diagonal :
    forall j : Fin n,
      Exists fun theta : Real =>
        |theta| ≤ gamma fp (m + 1) /\
          R j j = gsColumnNorm2 (s j) * (1 + theta)
  /-- Normalization rounding: `q̂_ij = gsNormalize(ŝ_j, R̂_jj) i·(1+δ)`, `|δ| ≤ u`. -/
  normalized :
    forall (i : Fin m) (j : Fin n),
      Exists fun delta : Real =>
        |delta| ≤ fp.u /\
          gsColumn Q j i = gsNormalize (s j) (R j j) i * (1 + delta)
  /-- Residual columnwise backward error against `classicalGramSchmidtResidual`. -/
  residual :
    forall (i : Fin m) (j : Fin n),
      |s j i - classicalGramSchmidtResidual A Q R j i| ≤
        gamma fp (j.val + 1) *
          (|A i j| +
            ∑ t : Fin j.val,
              |R ⟨t.val, Nat.lt_trans t.isLt j.isLt⟩ j| *
                |Q i ⟨t.val, Nat.lt_trans t.isLt j.isLt⟩|)

/-!
## Backward-error atoms for the inner product and the norm
-/

/-- **Inner-product backward error** for the rounded dot product, in the shape
needed by the `projection` channel (Higham §3.1, equation (3.3), page 63):
`fl(x^T y)` differs from the exact `gsDot x y` by at most `gamma fp m` times the
sum of term magnitudes. -/
theorem fl_dotProduct_sub_gsDot_abs_le {m : Nat} (fp : FPModel)
    (x y : Fin m -> Real) (hm : gammaValid fp m) :
    |fl_dotProduct fp m x y - gsDot x y| ≤
      gamma fp m * (∑ r : Fin m, |x r| * |y r|) := by
  obtain ⟨eta, heta, hexp⟩ := dotProduct_backward_error fp m x y hm
  have hgsdot : gsDot x y = ∑ r : Fin m, x r * y r := rfl
  rw [hexp, hgsdot]
  have hdiff :
      (∑ r : Fin m, x r * y r * (1 + eta r)) - ∑ r : Fin m, x r * y r =
        ∑ r : Fin m, x r * y r * eta r := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [hdiff]
  calc
    |∑ r : Fin m, x r * y r * eta r|
        ≤ ∑ r : Fin m, |x r * y r * eta r| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r : Fin m, |x r| * |y r| * gamma fp m := by
          apply Finset.sum_le_sum
          intro r _
          rw [abs_mul, abs_mul]
          exact mul_le_mul_of_nonneg_left (heta r)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = gamma fp m * ∑ r : Fin m, |x r| * |y r| := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r _
          ring

/-- Bridge: `Real.sqrt (∑ x_i * x_i) = gsColumnNorm2 x`, i.e. the sum-of-products
form used by `fl_norm2_relative_error` is the Euclidean column norm. -/
theorem sqrt_sum_mul_self_eq_gsColumnNorm2 {m : Nat} (x : Fin m -> Real) :
    Real.sqrt (∑ i : Fin m, x i * x i) = gsColumnNorm2 x := by
  rw [gsColumnNorm2, vecNorm2, vecNorm2Sq]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_two]

/-- **Norm relative error** for the rounded 2-norm, in the shape needed by the
`diagonal` channel (Higham Lemma 18.1 style, page 63/360):
`fl_norm2 fp m x = gsColumnNorm2 x * (1 + theta)` with `|theta| ≤ gamma fp (m+1)`. -/
theorem fl_norm2_eq_gsColumnNorm2_mul {m : Nat} (fp : FPModel)
    (x : Fin m -> Real) (hm : gammaValid fp (2 * (m + 1))) :
    Exists fun theta : Real =>
      |theta| ≤ gamma fp (m + 1) /\
        fl_norm2 fp m x = gsColumnNorm2 x * (1 + theta) := by
  obtain ⟨theta, htheta, hnorm⟩ := fl_norm2_relative_error fp m x hm
  refine ⟨theta, htheta, ?_⟩
  rw [hnorm, sqrt_sum_mul_self_eq_gsColumnNorm2]

/-!
## Main theorem: the rounded kernel meets the honest contract
-/

/-- **Rounded classical Gram-Schmidt backward/forward error** (Higham
Algorithm 19.11, page 373).

Under the standard `gamma`-validity side conditions and the honest nonzero
*computed*-residual-norm hypothesis `hpivot` (the CGS analogue of the MGS
nonzero-pivot assumption), the rounded kernel `fl_classicalGramSchmidt` satisfies
the honest floating-point analogue `ClassicalGramSchmidtRoundedState` of the
exact `ClassicalGramSchmidtState`.  The computed residual columns are
`flCGSResidual fp A Q̂ R̂`.

Constant convention: every bound uses an explicit `gamma fp (index)`; the indices
(`m`, `m+1`, `j+1`) are the ones the proof actually delivers, and are a
`gamma-tilde`-class surface in the sense of Higham page 357 (the printed integer
`c` is left unspecified there and is not claimed here). -/
theorem fl_classicalGramSchmidt_roundedState {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real)
    (hm : gammaValid fp (2 * (m + 1))) (hn : gammaValid fp n)
    (hpivot : forall j : Fin n, fl_classicalGramSchmidtR fp A j j ≠ 0) :
    ClassicalGramSchmidtRoundedState fp A
      (fl_classicalGramSchmidtQ fp A) (fl_classicalGramSchmidtR fp A)
      (flCGSResidual fp A (fl_classicalGramSchmidtQ fp A)
        (fl_classicalGramSchmidtR fp A)) where
  upper := fl_classicalGramSchmidtR_upperTrapezoidal fp A
  projection := by
    intro i j hij
    have hmm : gammaValid fp m :=
      gammaValid_mono fp (by omega) hm
    rw [fl_classicalGramSchmidtR_offDiag fp A i j hij]
    have hbe :=
      fl_dotProduct_sub_gsDot_abs_le fp
        (fun r => fl_classicalGramSchmidtQ fp A r i) (fun r => A r j) hmm
    -- `gsDot`/`gsColumn` unfold to the same summand shapes.
    simpa [gsDot, gsColumn] using hbe
  diagonal := by
    intro j
    rw [fl_classicalGramSchmidtR_diag fp A j]
    exact fl_norm2_eq_gsColumnNorm2_mul fp
      (flCGSResidual fp A (fl_classicalGramSchmidtQ fp A)
        (fl_classicalGramSchmidtR fp A) j) hm
  normalized := by
    intro i j
    have hpiv : fl_classicalGramSchmidtR fp A j j ≠ 0 := hpivot j
    obtain ⟨delta, hdelta, hdiv⟩ :=
      fp.model_div
        (flCGSResidualEntry fp A (fl_classicalGramSchmidtQ fp A)
          (fl_classicalGramSchmidtR fp A) i j)
        (fl_classicalGramSchmidtR fp A j j) hpiv
    refine ⟨delta, hdelta, ?_⟩
    -- `gsColumn Q j i = Q i j = q̂_ij`, and `s j i = residual entry`.
    have hq : gsColumn (fl_classicalGramSchmidtQ fp A) j i =
        fl_classicalGramSchmidtQ fp A i j := rfl
    rw [hq, fl_classicalGramSchmidtQ_normalized fp A i j, hdiv]
    rfl
  residual := by
    intro i j
    have hj1 : gammaValid fp (j.val + 1) :=
      gammaValid_mono fp (Nat.succ_le_of_lt j.isLt) hn
    have hbe :=
      flCGSResidual_backward_error fp A (fl_classicalGramSchmidtQ fp A)
        (fl_classicalGramSchmidtR fp A) i j hj1
    -- `flCGSResidual ... j i = flCGSResidualEntry ... i j` definitionally.
    simpa [flCGSResidual] using hbe

end

end NumStability
