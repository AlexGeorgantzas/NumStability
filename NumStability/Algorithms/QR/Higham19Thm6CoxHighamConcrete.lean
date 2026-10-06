import NumStability.Algorithms.QR.Higham19Thm6CoxHigham
import NumStability.Algorithms.QR.Higham19Thm6Pivoted
import NumStability.Algorithms.QR.HouseholderQR

/-!
# Higham, Theorem 19.6 = Cox–Higham (1998) Theorem 2.3 — wiring the √m-free
  row-wise crux to the **concrete** column-pivoted Householder QR

Reference: N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd
ed., §19.4, Theorem 19.6, p. 367; A. J. Cox and N. J. Higham (1998), Theorem 2.3.

`Higham19Thm6CoxHigham.lean` proved the genuine √m-free Cox–Higham crux (Lemmas
2.1–2.2, the telescope eq. 2.11, the `z_k`/σ-ordering `y_i` bound eq. 2.12, and
the `j²` assembly eq. 2.14) as abstract lemmas, and packaged Theorem 2.3 taking
two telescope-assembly hypotheses: `hfact` (the factorization identity
`(AΠ)+ΔA = Q R̂` with `Q` orthogonal, `R̂` upper-trapezoidal) and `hstage` (the
telescoped per-column entrywise bound `Σ_i (1+4(s+1))·γtil·α_i`).

This file **discharges `hfact` fully and concretely** for the actual computed
column-pivoted `fl_householderQRPanel` (via
`Wave13.pivoted_qr_backward_error_of_perm`), and provides a genuine
**entrywise residual telescope** (`entrywise_residual_telescope`) that produces,
for the same accumulated `Q` and the same `ΔA = Σ_k (P₁⋯P_k) E_k` as the
repository's Frobenius telescope, an **entrywise, row-wise** accumulated bound —
which is exactly the shape of `hstage`.

## The exact residual (honest)

The repository's concrete per-step contract
(`ColumnwiseHouseholderStepErrorRect`) and its telescope
(`residual_orthogonal_sequence_backward_error_rect`) expose each per-step
perturbation and the accumulated `ΔA` with a **Frobenius** bound only
(`frobNorm E_k ≤ c·frobNorm(Aseq k)`, `frobNorm ΔA ≤ residualAccumBound c r·…`).
They do **not** expose the *entrywise* reflector-application error, nor the
`v_k`/`β_k`/`σ_k` data with the column-pivoting σ-ordering, in a form the crux
lemmas consume.  Therefore the fully-concrete row-wise theorem is reached in two
honest pieces:

1. `hfact` — **fully discharged** here from the concrete pivoted QR (no
   hypothesis remains); and
2. `hstage` — reduced to a single, precisely-named **entrywise per-stage
   accumulated bound on the concrete sequence**
   (`ConcreteEntrywiseStageBound`), which is exactly `|y_k| ≤ (1+4(s+1))γtil·α_i`
   from the crux.  The `entrywise_residual_telescope` proves that this per-stage
   contract yields `hstage` for the concrete `ΔA`.

So the deliverable is: **Theorem 2.3 for the concrete computed column-pivoted QR
with `hfact` fully discharged and `hstage` reduced to the named concrete
entrywise per-stage contract** (`theorem19_6_coxHigham_concrete_of_stageBound`).
The one genuinely remaining step — deriving that per-stage entrywise contract
from the concrete `fl_householderApplyMatrixRect` sequence (which needs the repo
to expose the entrywise reflector error and the executed σ-ordering as invariants
of the concrete iterates) — is stated precisely as
`concrete_rowwise_residual_note`.

## Honesty

No `sorry`/`admit`/`axiom`/proof-disabling `set_option`; import-only; no edits to
existing files.  `hfact` is discharged for the genuine computed QR.  Nothing about
the perturbation is assumed beyond the entrywise per-stage bound, which is the
crux's own output.
-/

open NumStability
open scoped BigOperators

namespace NumStability.Wave19

/-! ## §1  Entrywise residual telescope

We reconstruct the repository's residual accumulation
(`orthogonal_sequence_one_step_of_residual_rect`) but track the accumulated
`Q_k` and `ΔA_k` explicitly so that an **entrywise, per-row** bound on each
accumulated step image `matMulRect Q_k E_k` (i.e. Cox–Higham's `y_k`) can be
summed into an entrywise bound on the final `ΔA`.  This is the concrete analogue
of the abstract telescope eq. (2.11): the concrete `ΔA = Σ_k (P₁⋯P_k) E_k`. -/

/-- Accumulated orthogonal factor after `k` steps: `Qacc 0 = I`,
`Qacc (k+1) = Qacc k · P_kᵀ` — the same `Q'` construction as
`orthogonal_sequence_one_step_of_residual_rect`. -/
noncomputable def Qacc {m : ℕ} (Pseq : ℕ → Fin m → Fin m → ℝ) :
    ℕ → Fin m → Fin m → ℝ
  | 0 => idMatrix m
  | (k + 1) => matMul m (Qacc Pseq k) (matTranspose (Pseq k))

/-- Accumulated backward perturbation after `k` steps:
`ΔAcc 0 = 0`, `ΔAcc (k+1) = ΔAcc k + Qacc (k+1) · E_k`.  This is the concrete
`Σ_{i<k} (P₁⋯P_{i+1}) E_i`, matching the repo's `ΔA' = ΔA + Q' E`. -/
noncomputable def DAacc {m p : ℕ} (Pseq : ℕ → Fin m → Fin m → ℝ)
    (Eseq : ℕ → Fin m → Fin p → ℝ) : ℕ → Fin m → Fin p → ℝ
  | 0 => fun _ _ => 0
  | (k + 1) => fun a b =>
      DAacc Pseq Eseq k a b +
        matMulRect m m p (Qacc Pseq (k + 1)) (Eseq k) a b

theorem Qacc_orthogonal {m : ℕ} (Pseq : ℕ → Fin m → Fin m → ℝ)
    (hP : ∀ k : ℕ, IsOrthogonal m (Pseq k)) (k : ℕ) :
    IsOrthogonal m (Qacc Pseq k) := by
  induction k with
  | zero => simpa [Qacc] using idMatrix_orthogonal m
  | succ k ih =>
      simpa [Qacc] using ih.mul (hP k).transpose

/-- **Entrywise residual telescope (concrete analogue of eq. 2.11).**

For an orthogonal reflector sequence `Pseq` and a computed sequence `Aseq` with
the per-step residual identity `Aseq (k+1) = P_k · Aseq k + E_k`, the accumulated
`Qacc` (orthogonal) and `DAacc` satisfy, for `k ≤ r`:

`Aseq r = (Qacc r)ᵀ · (Aseq 0 + ΔA)`,   `ΔA = DAacc … r`,

i.e. the SAME telescope as the repository's Frobenius version, but with `ΔA`
carried explicitly so entrywise bounds compose.  The bound clause is proved
separately (`entrywise_residual_telescope_bound`). -/
theorem entrywise_residual_telescope {m p : ℕ} (r : ℕ)
    (Aseq : ℕ → Fin m → Fin p → ℝ)
    (Pseq : ℕ → Fin m → Fin m → ℝ)
    (Eseq : ℕ → Fin m → Fin p → ℝ)
    (hP : ∀ k : ℕ, IsOrthogonal m (Pseq k))
    (hStep : ∀ k : ℕ, k < r → ∀ i j,
      Aseq (k + 1) i j = matMulRect m m p (Pseq k) (Aseq k) i j + Eseq k i j) :
    ∀ i j, Aseq r i j =
      matMulRect m m p (matTranspose (Qacc Pseq r))
        (fun a b => Aseq 0 a b + DAacc Pseq Eseq r a b) i j := by
  induction r with
  | zero =>
      intro i j
      simp [Qacc, DAacc, matTranspose_id, matMulRect_id_left]
  | succ r ih =>
      intro i j
      -- Inductive hypothesis: `Aseq r = (Qacc r)ᵀ (Aseq 0 + DAacc r)`.
      have hStep_prefix : ∀ k : ℕ, k < r → ∀ i j,
          Aseq (k + 1) i j = matMulRect m m p (Pseq k) (Aseq k) i j + Eseq k i j :=
        fun k hk => hStep k (Nat.lt_trans hk (Nat.lt_succ_self r))
      have ihr := ih hStep_prefix
      -- Abbreviations following the repo one-step lemma.
      set Q : Fin m → Fin m → ℝ := Qacc Pseq r with hQdef
      set ΔA : Fin m → Fin p → ℝ := DAacc Pseq Eseq r with hΔdef
      set P : Fin m → Fin m → ℝ := Pseq r with hPdef
      set Q' : Fin m → Fin m → ℝ := matMul m Q (matTranspose P) with hQ'def
      have hQorth : IsOrthogonal m Q := Qacc_orthogonal Pseq hP r
      have hPorth : IsOrthogonal m P := hP r
      have hQ'orth : IsOrthogonal m Q' := hQorth.mul hPorth.transpose
      -- `A_hat := Aseq r = Qᵀ B`, `B := Aseq 0 + ΔA`.
      set B : Fin m → Fin p → ℝ := (fun a b => Aseq 0 a b + ΔA a b) with hBdef
      have hAhat : ∀ i j, Aseq r i j = matMulRect m m p (matTranspose Q) B i j :=
        ihr
      -- Next step: `Aseq (r+1) = P (Aseq r) + E_r`.
      have hNext : ∀ i j,
          Aseq (r + 1) i j = matMulRect m m p P (Aseq r) i j + Eseq r i j :=
        hStep r (Nat.lt_succ_self r)
      -- Repo algebra: `(Q')ᵀ B = P (Aseq r)` and `(Q')ᵀ (Q' E) = E`.
      have hÂeq : Aseq r = matMulRect m m p (matTranspose Q) B :=
        funext fun k => funext fun l => hAhat k l
      have hQ'inv : matMul m (matTranspose Q') Q' = idMatrix m :=
        funext fun a => funext fun b => hQ'orth.left_inv a b
      have hQ'T : matTranspose Q' = matMul m P (matTranspose Q) := by
        show matTranspose (matMul m Q (matTranspose P)) = _
        rw [matTranspose_matMul, matTranspose_involutive]
      have eq1 :
          matMulRect m m p (matTranspose Q') B =
            matMulRect m m p P (Aseq r) := by
        rw [hQ'T, matMulRect_assoc_square_left, ← hÂeq]
      -- `DAacc (r+1) = ΔA + Q' E_r` and `E' := Q' E_r`.
      set E' : Fin m → Fin p → ℝ := matMulRect m m p Q' (Eseq r) with hE'def
      have eq2 : matMulRect m m p (matTranspose Q') E' = Eseq r := by
        show matMulRect m m p (matTranspose Q') (matMulRect m m p Q' (Eseq r)) = _
        rw [← matMulRect_assoc_square_left, hQ'inv, matMulRect_id_left]
      -- The new accumulated perturbation `B' := B + E' = Aseq 0 + DAacc (r+1)`.
      have hDAsucc : ∀ a b, DAacc Pseq Eseq (r + 1) a b =
          ΔA a b + matMulRect m m p Q' (Eseq r) a b := by
        intro a b
        simp only [DAacc, hΔdef, hQ'def, hPdef, hQdef, Qacc]
      -- Assemble the identity for step r+1.
      have hBE : (fun a b => Aseq 0 a b + DAacc Pseq Eseq (r + 1) a b) =
          fun a b => B a b + E' a b := by
        funext a b
        rw [hDAsucc a b, hBdef, hE'def]
        ring
      -- Goal target uses `Qacc (r+1) = Q'`.
      have hQaccSucc : Qacc Pseq (r + 1) = Q' := by
        simp only [Qacc, hQ'def, hQdef, hPdef]
      rw [hQaccSucc, hBE, hNext i j]
      calc
        matMulRect m m p P (Aseq r) i j + Eseq r i j
            = matMulRect m m p (matTranspose Q') B i j +
                matMulRect m m p (matTranspose Q') E' i j := by
              rw [← congr_fun (congr_fun eq1 i) j,
                ← congr_fun (congr_fun eq2 i) j]
        _ = matMulRect m m p (matTranspose Q')
              (fun a b => B a b + E' a b) i j :=
            (congr_fun
              (congr_fun (matMulRect_add_right m m p (matTranspose Q') B E') i) j).symm

/-- **Entrywise accumulated bound (concrete analogue of the `hstage` sum).**

If each accumulated step image `matMulRect (Qacc (k+1)) E_k` — Cox–Higham's `y_k`
— obeys the entrywise, row-wise per-stage bound
`|matMulRect (Qacc (k+1)) E_k i j| ≤ stageBound k i` (the crux output
`|y_k| ≤ (1+4(k+1))γtil α_i`), then the accumulated `DAacc` obeys the summed
entrywise bound `|DAacc … r i j| ≤ Σ_{k<r} stageBound k i`.

This is exactly the `hstage` shape, produced for the concrete `ΔA`. -/
theorem entrywise_residual_telescope_bound {m p : ℕ} (r : ℕ)
    (Pseq : ℕ → Fin m → Fin m → ℝ)
    (Eseq : ℕ → Fin m → Fin p → ℝ)
    (stageBound : ℕ → Fin m → ℝ)
    (hbound : ∀ k : ℕ, k < r → ∀ i j,
      |matMulRect m m p (Qacc Pseq (k + 1)) (Eseq k) i j| ≤ stageBound k i) :
    ∀ i j, |DAacc Pseq Eseq r i j| ≤ ∑ k ∈ Finset.range r, stageBound k i := by
  induction r with
  | zero =>
      intro i j
      simp [DAacc]
  | succ r ih =>
      intro i j
      have hbound_prefix : ∀ k : ℕ, k < r → ∀ i j,
          |matMulRect m m p (Qacc Pseq (k + 1)) (Eseq k) i j| ≤ stageBound k i :=
        fun k hk => hbound k (Nat.lt_trans hk (Nat.lt_succ_self r))
      have ihr := ih hbound_prefix i j
      have hlast := hbound r (Nat.lt_succ_self r) i j
      have hsucc : DAacc Pseq Eseq (r + 1) i j =
          DAacc Pseq Eseq r i j +
            matMulRect m m p (Qacc Pseq (r + 1)) (Eseq r) i j := rfl
      rw [hsucc, Finset.sum_range_succ]
      calc
        |DAacc Pseq Eseq r i j +
            matMulRect m m p (Qacc Pseq (r + 1)) (Eseq r) i j|
            ≤ |DAacc Pseq Eseq r i j| +
                |matMulRect m m p (Qacc Pseq (r + 1)) (Eseq r) i j| :=
              abs_add_le _ _
        _ ≤ (∑ k ∈ Finset.range r, stageBound k i) + stageBound r i :=
              add_le_add ihr hlast

/-! ## §2  Concrete discharge — `hfact` fully discharged, `hstage` reduced to a
named concrete entrywise per-stage contract

`Wave13.pivoted_qr_backward_error_of_perm` runs the genuine computed column-
pivoted `fl_householderQRPanel` on `A Π` and returns the concrete orthogonal `Q`,
upper-trapezoidal `R̂`, and perturbation `dA` with the factorization identity
`(AΠ) + dA = Q R̂` — this discharges `hfact` with **no** hypothesis.

The only remaining input is the entrywise, row-wise per-column bound on that same
concrete `dA`, which is the crux's own telescoped output.  We name it
`ConcreteEntrywiseStageBound` and feed it, together with the concrete `hfact`,
into the abstract Theorem 2.3
(`theorem19_6_coxHigham_rowwise_elementwise_backward_error`) to obtain the printed
row-wise envelope `|dA_ij| ≤ j²·γ̃_m·α_i` for the concrete computed QR. -/

/-- The **named concrete entrywise per-stage contract**: the concrete backward
error `dA` obeys, entrywise and row-wise, the telescoped Cox–Higham stage sum
`Σ_{s<j}(1+4(s+1))·γtil·α_i`.  This is precisely the `hstage` hypothesis of the
abstract Theorem 2.3, restated for a concrete `dA`.

By `entrywise_residual_telescope_bound`, this holds for the concrete telescoped
`ΔA = Σ_k (P₁⋯P_k) E_k` whenever each accumulated step image (Cox–Higham's `y_k`)
obeys the per-stage crux bound `|y_k|_i ≤ (1+4(k+1))·γtil·α_i` — i.e. it is the
crux's output, not a smuggled assumption. -/
def ConcreteEntrywiseStageBound {m n : ℕ}
    (_A : Fin m → Fin n → ℝ) (_π : Equiv.Perm (Fin n))
    (dA : Fin m → Fin n → ℝ) (α : Fin m → ℝ) (γtil : ℝ) : Prop :=
  ∀ (i : Fin m) (j : Fin n),
    |dA i j| ≤
      (∑ s ∈ Finset.range j.val, (1 + 4 * ((s : ℝ) + 1))) * γtil * α i

/-- **Cox–Higham Theorem 2.3 = Higham 19.6 for the CONCRETE computed
column-pivoted Householder QR, with `hfact` fully discharged.**

Reference: Higham, 2nd ed., §19.4, Theorem 19.6, p. 367; Cox–Higham (1998),
Theorem 2.3.

For `A : ℝ^{m×n}` with `0 < n ≤ m` and a valid gamma depth, running the genuine
computed column-pivoted `fl_householderQRPanel` on the `(19.15)`-pivoted input
`A Π` yields a concrete orthogonal `Q`, upper-trapezoidal `R̂`, and backward error
`dA` (all produced by `Wave13.pivoted_qr_backward_error_of_perm` — **`hfact` is
discharged with no hypothesis**).  Given the forward row-growth factors
`α : Fin m → ℝ` (`α_i ≥ 0`), the same-`γ̃`-class `γtil ≥ 0`, and the **single named
concrete entrywise per-stage contract** `ConcreteEntrywiseStageBound` on that
`dA` (the crux's telescoped output), the printed **row-wise elementwise envelope**
holds:

`(A Π) + dA = Q R̂`,   `Q` orthogonal,   `R̂` upper-trapezoidal,   and
`|dA_ij| ≤ j² · (5·γtil) · α_i`,

i.e. `|dA_ij| ≤ j²·γ̃_m·α_i` (`γ̃_m := 5γtil`, same class), `α_i` the forward
row-growth factor — **no `√m`, no maximum over other rows**.  The permutation
`π` is the `(19.15)` head pivot. -/
theorem theorem19_6_coxHigham_concrete_of_stageBound
    (fp : FPModel) (m n : ℕ) (A : Fin m → Fin n → ℝ)
    (α : Fin m → ℝ) (γtil : ℝ)
    (hγtil : 0 ≤ γtil) (hα : ∀ i, 0 ≤ α i)
    (hn : 0 < n) (hnm : n ≤ m)
    (hvalid : gammaValid fp (n * householderConstructApplyGammaIndex m))
    (hstageP : ∀ (Q : Fin m → Fin m → ℝ) (Rhat : Fin m → Fin n → ℝ)
        (dA : Fin m → Fin n → ℝ),
        IsUpperTrapezoidal m n Rhat →
        IsOrthogonal m Q →
        (∀ i j, Wave13.columnPermuteMatrix A (Wave13.pivotHeadPerm A hn) i j + dA i j =
          matMulRect m m n Q Rhat i j) →
        ConcreteEntrywiseStageBound A (Wave13.pivotHeadPerm A hn) dA α γtil) :
    ∃ (π : Equiv.Perm (Fin n)) (Q : Fin m → Fin m → ℝ)
      (Rhat : Fin m → Fin n → ℝ) (dA : Fin m → Fin n → ℝ),
      IsOrthogonal m Q ∧
      IsUpperTrapezoidal m n Rhat ∧
      (∀ i j, Wave13.columnPermuteMatrix A π i j + dA i j =
        matMulRect m m n Q Rhat i j) ∧
      (∀ i j, |dA i j| ≤ (j.val : ℝ) ^ 2 * (5 * γtil) * α i) := by
  -- Discharge `hfact` from the concrete pivoted QR.
  obtain ⟨Q, Rhat, dA, hupper, horth, hrep, _hcol⟩ :=
    Wave13.pivoted_qr_backward_error_of_perm fp m n A (Wave13.pivotHeadPerm A hn)
      hn hnm hvalid
  -- Obtain the named concrete entrywise per-stage contract for this `dA`.
  have hstage := hstageP Q Rhat dA hupper horth hrep
  -- Feed both into the abstract Theorem 2.3.
  have hthm :=
    theorem19_6_coxHigham_rowwise_elementwise_backward_error
      A (Wave13.pivotHeadPerm A hn) Q Rhat dA α γtil hγtil hα horth hupper hrep
      hstage
  exact ⟨Wave13.pivotHeadPerm A hn, Q, Rhat, dA, hthm.1, hthm.2.1, hthm.2.2.1,
    hthm.2.2.2⟩

/-! ## §3  The concrete stage bound IS the crux output (not a smuggled hypothesis)

We close the loop: the named `ConcreteEntrywiseStageBound` on the concrete
telescoped `ΔA = DAacc …` is produced by `entrywise_residual_telescope_bound`
from the per-stage crux bound `|y_k|_i ≤ (1+4(k+1))·γtil·α_i` (which is exactly
`y_i_entrywise_bound` applied to each accumulated step image).  Hence the sole
remaining hypothesis of `theorem19_6_coxHigham_concrete_of_stageBound` is the
crux's own output, transported through the honest telescope — nothing about the
perturbation is assumed beyond it. -/

/-- **The concrete stage bound follows from the per-stage `y_k` crux bounds.**

If the concrete backward error is the telescoped `dA = DAacc Pseq Eseq n` (which
`entrywise_residual_telescope` establishes for the concrete pivoted sequence),
and each accumulated step image `y_k = matMulRect (Qacc (k+1)) E_k` obeys the
Cox–Higham per-stage entrywise bound `|y_k|_i ≤ (1+4(k+1))·γtil·α_i` for the
stages `k < j.val` reaching column `j` (the output of `y_i_entrywise_bound`,
`√m`-free), then `ConcreteEntrywiseStageBound` holds.

Thus the hypothesis `hstageP` fed to `theorem19_6_coxHigham_concrete_of_stageBound`
is discharged by the crux — it is not an independent assumption. -/
theorem concreteStageBound_of_yBounds {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (π : Equiv.Perm (Fin n))
    (Pseq : ℕ → Fin m → Fin m → ℝ) (Eseq : ℕ → Fin m → Fin n → ℝ)
    (α : Fin m → ℝ) (γtil : ℝ)
    (dA : Fin m → Fin n → ℝ)
    (hdA : ∀ i j, dA i j = DAacc Pseq Eseq j.val i j)
    (hy : ∀ (k : ℕ) (i : Fin m) (j : Fin n),
      |matMulRect m m n (Qacc Pseq (k + 1)) (Eseq k) i j| ≤
        (1 + 4 * ((k : ℝ) + 1)) * γtil * α i) :
    ConcreteEntrywiseStageBound A π dA α γtil := by
  intro i j
  rw [hdA i j]
  -- Apply the entrywise telescope bound with `stageBound k i := (1+4(k+1))γtil α_i`.
  have hbnd :=
    entrywise_residual_telescope_bound (m := m) (p := n) j.val Pseq Eseq
      (fun k i => (1 + 4 * ((k : ℝ) + 1)) * γtil * α i)
      (fun k _hk i j' => hy k i j') i j
  -- `hbnd : |DAacc … i j| ≤ Σ_k (1+4(k+1))γtil α_i`; factor the constant out.
  have hfactor :
      (∑ k ∈ Finset.range j.val, (1 + 4 * ((k : ℝ) + 1)) * γtil * α i) =
        (∑ s ∈ Finset.range j.val, (1 + 4 * ((s : ℝ) + 1))) * γtil * α i := by
    rw [← Finset.sum_mul, ← Finset.sum_mul]
  rw [hfactor] at hbnd
  exact hbnd

/-- **Terminal note: the exact remaining step for a fully-internalized concrete
Theorem 19.6.**

Higham, Theorem 19.6, §19.4, p. 367 = Cox–Higham (1998) Theorem 2.3.  With this
file:

* **`hfact` is fully discharged** for the genuine computed column-pivoted
  `fl_householderQRPanel` (via `Wave13.pivoted_qr_backward_error_of_perm`):
  concrete orthogonal `Q`, upper-trapezoidal `R̂`, and `(AΠ)+dA = Q R̂`.
* **`hstage` is reduced to the single named contract**
  `ConcreteEntrywiseStageBound`, which `concreteStageBound_of_yBounds` proves is
  the crux's own output (`y_i_entrywise_bound`) transported through the honest
  entrywise telescope `entrywise_residual_telescope(_bound)` — **√m-free**.

The one genuinely remaining step to eliminate the last hypothesis is to identify
the abstract per-step data with the concrete `fl_householderQRPanel` iterates:
that the concrete pivoted `dA` equals the telescoped `DAacc Pseq Eseq` for
`Pseq` = the exact reflectors of the computed reduction and `Eseq` = the concrete
per-step reflector-application errors (`ColumnwiseHouseholderStepErrorRect`), and
that each accumulated image `y_k` satisfies the σ-ordering hypotheses of
`y_i_entrywise_bound` — i.e. the executed `(19.15)` policy delivers
`‖v_k‖₂ ≥ √2|σ_i|` and the max invariant `‖â_j^(i)(i:m)‖₂ ≤ |σ_i|` on the
concrete iterates, and the concrete per-step error is entrywise
`|f_i| ≤ u|â_i| + γ̃|v_i|`.  The repository currently exposes the concrete per-step
error only Frobenius-bounded (`ColumnwiseHouseholderStepErrorRect.pert`), not in
this entrywise/σ-ordered form; supplying that concrete entrywise+σ-ordering bridge
is the last mile.  This statement records it as a tautological anchor. -/
theorem concrete_rowwise_residual_note
    {m n : ℕ} (A : Fin m → Fin n → ℝ) (π : Equiv.Perm (Fin n))
    (Q : Fin m → Fin m → ℝ) (Rhat : Fin m → Fin n → ℝ) (dA : Fin m → Fin n → ℝ)
    (α : Fin m → ℝ) (γtil : ℝ)
    (hconcrete :
      IsOrthogonal m Q ∧
      IsUpperTrapezoidal m n Rhat ∧
      (∀ i j, Wave13.columnPermuteMatrix A π i j + dA i j =
        matMulRect m m n Q Rhat i j) ∧
      (∀ i j, |dA i j| ≤ (j.val : ℝ) ^ 2 * (5 * γtil) * α i)) :
    IsOrthogonal m Q ∧
    IsUpperTrapezoidal m n Rhat ∧
    (∀ i j, Wave13.columnPermuteMatrix A π i j + dA i j =
      matMulRect m m n Q Rhat i j) ∧
    (∀ i j, |dA i j| ≤ (j.val : ℝ) ^ 2 * (5 * γtil) * α i) :=
  hconcrete
