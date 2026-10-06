/-
Algorithms/Cholesky/AasenDirectTridiagGEPPSolveCh11Closure.lean

Assembly support for the source-faithful tridiagonal-GEPP middle solve in
Higham's Theorem 11.8.  The rounded adjacent-pivot executor is deliberately
kept behind a small budget interface: it must provide its computed middle
solution `y`, a source perturbation `DeltaT`, and a nonnegative entrywise
majorant `BT`.  Everything after that operational theorem -- the outer Aasen
solves, the collapsed source equation, and the `gamma_(15*n+25)` scalar fold --
is discharged here.

The report's local constants (`gamma_2`, `gamma_1`, and `gamma_3`) still guide
the operational proof, but this assembly does not turn their local `gamma_6`
combination into an unjustified dimension-independent infinity-norm claim.
Instead, the norm fold accepts a proved middle radius `gamma_k`; precisely
`k <= 8*n+25` remains available inside the printed final radius.
-/
import NumStability.Algorithms.Cholesky.AasenDirect118Ch11Closure

open scoped BigOperators

namespace NumStability.Ch11Closure.AasenDirectGEPP

open NumStability
open NumStability.Ch11Closure
open NumStability.Ch11Closure.AasenDirect
open NumStability.Ch11Closure.AasenNorm
open NumStability.Ch11Closure.Mixed
open NumStability.Ch11Closure.HFactor

/-! ### The direct middle-solve interface -/

/-- A direct source backward-error certificate for an operational middle
tridiagonal solve.  `BT` is kept separate from `DeltaT`: an interleaved GEPP
proof can assemble a sparse nonnegative local budget without first proving an
entrywise formula for the accumulated perturbation itself. -/
def AasenDirectMiddleBudget (fp : FPModel) (n : ℕ)
    (T : Fin n → Fin n → ℝ) (z y : Fin n → ℝ)
    (DeltaT BT : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j : Fin n, 0 ≤ BT i j) ∧
  (∀ i j : Fin n, |DeltaT i j| ≤ BT i j) ∧
  (∀ i : Fin n,
    ∑ j : Fin n, (T i j + DeltaT i j) * y j = z i)

/-- Build the direct middle certificate from any nonnegative componentwise
envelope.  This is the convenient endpoint for a trace induction that first
constructs `DeltaT` and then bounds it by a sparse local budget. -/
theorem aasenDirectMiddleBudget_of_envelope (fp : FPModel) (n : ℕ)
    (T : Fin n → Fin n → ℝ) (z y : Fin n → ℝ)
    (DeltaT W : Fin n → Fin n → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hW : ∀ i j : Fin n, 0 ≤ W i j)
    (hDeltaT : ∀ i j : Fin n, |DeltaT i j| ≤ c * W i j)
    (hTy : ∀ i : Fin n,
      ∑ j : Fin n, (T i j + DeltaT i j) * y j = z i) :
    AasenDirectMiddleBudget fp n T z y DeltaT (fun i j => c * W i j) := by
  exact ⟨fun i j => mul_nonneg hc (hW i j), hDeltaT, hTy⟩

/-- The outer rounded Aasen solves compose with any operational middle solver
that supplies `AasenDirectMiddleBudget`.  In particular, this theorem does not
mention triangular factors of `T`, equation (9.20), or an accumulated GEPP
lower factor. -/
theorem higham11_15_fl_aasen_solve_chain_source_backward_error_of_direct_middle_budget
    (fp : FPModel) (n : ℕ)
    (A Pmat L T : Fin n → Fin n → ℝ) (b y : Fin n → ℝ)
    (DeltaT BT : Fin n → Fin n → ℝ)
    (hLdiag : ∀ i : Fin n, L i i ≠ 0)
    (hLlower : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hmiddle : AasenDirectMiddleBudget fp n T
      (fl_forwardSub fp n L (fun i => ∑ j : Fin n, Pmat i j * b j))
      y DeltaT BT) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z := fl_forwardSub fp n L rhs
    let U : Fin n → Fin n → ℝ := fun i j => L j i
    let w := fl_backSub fp n U y
    let bound := higham11_15_aasenChainDeltaABound n (gamma fp n) BT L T U
    ∃ DeltaS : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaS i j| ≤ bound i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaS i j) * w j = rhs i) := by
  intro rhs z U w bound
  rcases hmiddle with ⟨hBT, hDeltaT, hTy⟩
  obtain ⟨DeltaL, DeltaU, hDeltaL, hDeltaU, hLz, hUw⟩ :=
    higham11_15_fl_aasen_outer_triangular_solves_backward_error
      fp n Pmat L b y hLdiag hLlower hn
  have hchain : ∀ i j : Fin n,
      |higham11_15_aasenChainDeltaA n L T U DeltaL DeltaT DeltaU i j| ≤
        bound i j := by
    exact higham11_15_aasenChainDeltaA_abs_bound_gamma
      n L T U DeltaL DeltaT DeltaU BT (gamma fp n)
      (gamma_nonneg fp hn) hBT hDeltaL hDeltaT hDeltaU
  exact higham11_15_aasen_chain_source_backward_error_of_components
    n A L T U DeltaL DeltaT DeltaU rhs z y w bound
    (by
      intro i j
      simpa [U] using hprod i j)
    hLz hTy hUw hchain

/-! ### Scalar absorption for a proved middle radius -/

/-- Multiplication by the two outer triangular-solve perturbations costs at
most `2*n` additional gamma slots. -/
theorem higham11_8_one_plus_two_gamma_plus_sq_mul_gamma_k_le_gamma_2nk
    (fp : FPModel) (n k : ℕ)
    (hval : gammaValid fp (2 * n + k)) :
    (1 + 2 * gamma fp n + (gamma fp n) ^ 2) * gamma fp k ≤
      gamma fp (2 * n + k) := by
  have h2n : gammaValid fp (2 * n) := gammaValid_mono fp (by omega) hval
  have hk : gammaValid fp k := gammaValid_mono fp (by omega) hval
  have houter :
      2 * gamma fp n + (gamma fp n) ^ 2 ≤ gamma fp (2 * n) :=
    higham11_8_two_gamma_plus_sq_le_gamma_2n fp n h2n
  have hcoeff :
      1 + 2 * gamma fp n + (gamma fp n) ^ 2 ≤ 1 + gamma fp (2 * n) := by
    linarith
  have hmul :
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) * gamma fp k ≤
        (1 + gamma fp (2 * n)) * gamma fp k :=
    mul_le_mul_of_nonneg_right hcoeff (gamma_nonneg fp hk)
  have hsum :
      gamma fp k + gamma fp (2 * n) + gamma fp k * gamma fp (2 * n) ≤
        gamma fp (k + 2 * n) :=
    gamma_sum_le fp k (2 * n) (by simpa [Nat.add_comm] using hval)
  calc
    (1 + 2 * gamma fp n + (gamma fp n) ^ 2) * gamma fp k
        ≤ (1 + gamma fp (2 * n)) * gamma fp k := hmul
    _ = gamma fp k + gamma fp k * gamma fp (2 * n) := by ring
    _ ≤ gamma fp k + gamma fp (2 * n) + gamma fp k * gamma fp (2 * n) := by
        linarith [gamma_nonneg fp h2n]
    _ ≤ gamma fp (k + 2 * n) := hsum
    _ = gamma fp (2 * n + k) := by
        congr 1
        omega

/-- Complete coefficient fold for the factor residual, the two outer solves,
and a middle perturbation budget bounded by `gamma_k`.  The exact remaining
allowance is `k <= 8*n+25`. -/
theorem higham11_8_direct_middle_gamma_k_bracket_le_gamma_15n25
    (fp : FPModel) (n k : ℕ) (hn : 2 ≤ n) (hk : k ≤ 8 * n + 25)
    (hval : gammaValid fp (15 * n + 25)) :
    gamma fp (3 * n) +
        (2 * gamma fp n + (gamma fp n) ^ 2) +
        (1 + 2 * gamma fp n + (gamma fp n) ^ 2) * gamma fp k ≤
      gamma fp (15 * n + 25) := by
  have h2n : gammaValid fp (2 * n) := gammaValid_mono fp (by omega) hval
  have h5n : gammaValid fp (5 * n) := gammaValid_mono fp (by omega) hval
  have h2nk : gammaValid fp (2 * n + k) :=
    gammaValid_mono fp (by omega) hval
  have h7nk : gammaValid fp (7 * n + k) :=
    gammaValid_mono fp (by omega) hval
  have houter :
      2 * gamma fp n + (gamma fp n) ^ 2 ≤ gamma fp (2 * n) :=
    higham11_8_two_gamma_plus_sq_le_gamma_2n fp n h2n
  have hmiddle :
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) * gamma fp k ≤
        gamma fp (2 * n + k) :=
    higham11_8_one_plus_two_gamma_plus_sq_mul_gamma_k_le_gamma_2nk
      fp n k h2nk
  have hfirst : gamma fp (3 * n) + gamma fp (2 * n) ≤ gamma fp (5 * n) := by
    simpa [show 3 * n + 2 * n = 5 * n by omega] using
      higham11_gamma_add_le fp (3 * n) (2 * n) (by
        simpa [show 3 * n + 2 * n = 5 * n by omega] using h5n)
  have hsecond :
      gamma fp (5 * n) + gamma fp (2 * n + k) ≤ gamma fp (7 * n + k) := by
    simpa [show 5 * n + (2 * n + k) = 7 * n + k by omega] using
      higham11_gamma_add_le fp (5 * n) (2 * n + k) (by
        simpa [show 5 * n + (2 * n + k) = 7 * n + k by omega] using h7nk)
  have hmono : gamma fp (7 * n + k) ≤ gamma fp (15 * n + 25) :=
    gamma_mono fp (by omega) hval
  linarith

/-- The maximal convenient specialization of
`higham11_8_direct_middle_gamma_k_bracket_le_gamma_15n25`. -/
theorem higham11_8_direct_middle_gamma_8n25_bracket_le_gamma_15n25
    (fp : FPModel) (n : ℕ) (hn : 2 ≤ n)
    (hval : gammaValid fp (15 * n + 25)) :
    gamma fp (3 * n) +
        (2 * gamma fp n + (gamma fp n) ^ 2) +
        (1 + 2 * gamma fp n + (gamma fp n) ^ 2) * gamma fp (8 * n + 25) ≤
      gamma fp (15 * n + 25) := by
  exact higham11_8_direct_middle_gamma_k_bracket_le_gamma_15n25
    fp n (8 * n + 25) hn (by omega) hval

/-! ### Optional trace-product norm bridge -/

/-- A nonnegative local envelope scaled by `gamma_ell`, whose norm is at most
`m ||T||_inf`, is absorbed by `gamma_(m*ell)`. -/
theorem higham11_8_scaled_envelope_infNorm_le_gamma_nsmul
    (fp : FPModel) {n m ell : ℕ} (hm : 1 ≤ m) (hn : 0 < n)
    (W T : Fin n → Fin n → ℝ)
    (hW : ∀ i j : Fin n, 0 ≤ W i j)
    (hWnorm : infNorm W ≤ (m : ℝ) * infNorm T)
    (hval : gammaValid fp (m * ell)) :
    infNorm (fun i j => gamma fp ell * W i j) ≤
      gamma fp (m * ell) * infNorm T := by
  have hell : gammaValid fp ell := gammaValid_mono fp (by
    have : ell ≤ m * ell := by nlinarith
    exact this) hval
  have hscale :
      infNorm (fun i j => gamma fp ell * W i j) ≤ gamma fp ell * infNorm W :=
    infNorm_const_mul_le (gamma fp ell) (gamma_nonneg fp hell) W hW
  have hgamma_mul : (m : ℝ) * gamma fp ell ≤ gamma fp (m * ell) :=
    gamma_nsmul_le fp m ell hm hval
  calc
    infNorm (fun i j => gamma fp ell * W i j)
        ≤ gamma fp ell * infNorm W := hscale
    _ ≤ gamma fp ell * ((m : ℝ) * infNorm T) :=
      mul_le_mul_of_nonneg_left hWnorm (gamma_nonneg fp hell)
    _ = ((m : ℝ) * gamma fp ell) * infNorm T := by ring
    _ ≤ gamma fp (m * ell) * infNorm T :=
      mul_le_mul_of_nonneg_right hgamma_mul (infNorm_nonneg T)

/-- Componentwise domination by the scaled envelope transfers the preceding
bound to an arbitrary nonnegative middle budget `BT`. -/
theorem higham11_8_middle_budget_infNorm_le_gamma_nsmul_of_envelope
    (fp : FPModel) {n m ell : ℕ} (hm : 1 ≤ m) (hn : 0 < n)
    (BT W T : Fin n → Fin n → ℝ)
    (hBT : ∀ i j : Fin n, 0 ≤ BT i j)
    (hW : ∀ i j : Fin n, 0 ≤ W i j)
    (hdom : ∀ i j : Fin n, BT i j ≤ gamma fp ell * W i j)
    (hWnorm : infNorm W ≤ (m : ℝ) * infNorm T)
    (hval : gammaValid fp (m * ell)) :
    infNorm BT ≤ gamma fp (m * ell) * infNorm T := by
  have hell : gammaValid fp ell := gammaValid_mono fp (by
    have : ell ≤ m * ell := by nlinarith
    exact this) hval
  let S : Fin n → Fin n → ℝ := fun i j => gamma fp ell * W i j
  have hS : ∀ i j : Fin n, 0 ≤ S i j := fun i j =>
    mul_nonneg (gamma_nonneg fp hell) (hW i j)
  have hBTabs : ∀ i j : Fin n, |BT i j| ≤ S i j := by
    intro i j
    rw [abs_of_nonneg (hBT i j)]
    exact hdom i j
  have hle : infNorm BT ≤ infNorm S :=
    higham11_3_infNorm_le_of_componentwise_bound_nonneg n BT S hS hBTabs
  exact hle.trans (by
    simpa [S] using higham11_8_scaled_envelope_infNorm_le_gamma_nsmul
      fp hm hn W T hW hWnorm hval)

/-- The trace-level target suggested by the local Higham analysis.  If the
local `gamma_6` envelope has row norm at most `(n+2)||T||_inf`, its middle
budget fits in `gamma_(6n+12)`, hence in the terminal allowance `8n+25`. -/
theorem higham11_8_local_gamma_six_envelope_infNorm_le_gamma_6n12
    (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (BT W T : Fin n → Fin n → ℝ)
    (hBT : ∀ i j : Fin n, 0 ≤ BT i j)
    (hW : ∀ i j : Fin n, 0 ≤ W i j)
    (hdom : ∀ i j : Fin n, BT i j ≤ gamma fp 6 * W i j)
    (hWnorm : infNorm W ≤ ((n + 2 : ℕ) : ℝ) * infNorm T)
    (hval : gammaValid fp (6 * n + 12)) :
    infNorm BT ≤ gamma fp (6 * n + 12) * infNorm T := by
  have h := higham11_8_middle_budget_infNorm_le_gamma_nsmul_of_envelope
    fp (m := n + 2) (ell := 6) (by omega) hn BT W T hBT hW hdom hWnorm (by
      simpa [show (n + 2) * 6 = 6 * n + 12 by omega] using hval)
  simpa [show (n + 2) * 6 = 6 * n + 12 by omega] using h

/-! ### Terminal Theorem-11.8 assembly -/

/-- **Theorem 11.8, direct operational-middle assembly.**

This is the terminal Chapter-11 wrapper required by a rounded adjacent-pivot
tridiagonal solver.  Its middle hypothesis is exactly the operational
certificate `AasenDirectMiddleBudget`, plus the norm radius proved for that
certificate.  There are no middle triangular factors, equation-(9.20) model,
or accumulated-lower-factor norm hypotheses.

Any operational theorem with `||BT||_inf <= gamma_k ||That||_inf` and
`k <= 8*n+25` therefore closes the printed `gamma_(15*n+25)` conclusion. -/
theorem higham11_8_aasen_backward_error_direct_of_operational_middle_budget
    (fp : FPModel) (n : ℕ) (hn : 2 ≤ n)
    (A Pmat : Fin n → Fin n → ℝ) (b y : Fin n → ℝ)
    (DeltaT BT : Fin n → Fin n → ℝ) (k : ℕ)
    (hsymm : ∀ i j : Fin n, A i j = A j i)
    (hp : FlAasenPivots fp n A)
    (hLhat_cap : ∀ i j : Fin n, |(flAasen fp n A).Lhat i j| ≤ 1)
    (hmiddle : AasenDirectMiddleBudget fp n (flAasen fp n A).That
      (fl_forwardSub fp n (flAasen fp n A).Lhat
        (fun i => ∑ j : Fin n, Pmat i j * b j))
      y DeltaT BT)
    (hBTnorm : infNorm BT ≤ gamma fp k * infNorm (flAasen fp n A).That)
    (hk : k ≤ 8 * n + 25)
    (hval : gammaValid fp (15 * n + 25)) :
    let Lh := (flAasen fp n A).Lhat
    let Th := (flAasen fp n A).That
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z := fl_forwardSub fp n Lh rhs
    let Uouter : Fin n → Fin n → ℝ := fun i j => Lh j i
    let w := fl_backSub fp n Uouter y
    let Bfactor : Fin n → Fin n → ℝ := fun i j =>
      gamma fp (3 * n) *
        ∑ p : Fin n, ∑ q : Fin n, |Lh i p| * |Th p q| * |Lh j q|
    let Bsolve : Fin n → Fin n → ℝ :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT Lh Th Uouter
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ Bfactor i j + Bsolve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w j = rhs i) ∧
      infNorm DeltaA ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * gamma fp (15 * n + 25) * infNorm Th := by
  intro Lh Th rhs z Uouter w Bfactor Bsolve
  have hn_pos : 0 < n := by omega
  have hnval : gammaValid fp n := gammaValid_mono fp (by omega) hval
  have h2n : gammaValid fp (2 * n) := gammaValid_mono fp (by omega) hval
  have h3n : gammaValid fp (3 * n) := gammaValid_mono fp (by omega) hval
  have hkn : gammaValid fp k := gammaValid_mono fp (by omega) hval
  have hgamma_n : 0 ≤ gamma fp n := gamma_nonneg fp hnval
  have hgamma_k : 0 ≤ gamma fp k := gamma_nonneg fp hkn
  rcases hmiddle with ⟨hBT, hDeltaT, hTy⟩
  have hLdiag_one : ∀ i : Fin n, Lh i i = 1 := flAasen_L_unit_diag fp n A
  have hLupper : ∀ i j : Fin n, i.val < j.val → Lh i j = 0 :=
    flAasen_L_upper_zero fp n A
  have hLfirst : ∀ i j : Fin n, j.val = 0 → i.val ≠ 0 → Lh i j = 0 :=
    flAasen_L_first_col fp n A
  have hLdiag_ne : ∀ i : Fin n, Lh i i ≠ 0 := fun i => by
    rw [hLdiag_one i]
    exact one_ne_zero
  let Afact : Fin n → Fin n → ℝ :=
    fun i j => ∑ p : Fin n, ∑ q : Fin n, Lh i p * Th p q * Lh j q
  have hmiddle' : AasenDirectMiddleBudget fp n Th z y DeltaT BT := by
    exact ⟨hBT, hDeltaT, hTy⟩
  obtain ⟨DeltaS, hDeltaS, hsource⟩ :=
    higham11_15_fl_aasen_solve_chain_source_backward_error_of_direct_middle_budget
      fp n Afact Pmat Lh Th b y DeltaT BT hLdiag_ne hLupper hnval
      (by intro i j; rfl) hmiddle'
  have hfactor : ∀ i j : Fin n, |Afact i j - A i j| ≤ Bfactor i j :=
    fun i j => fl_aasen_factorization_residual fp n A hp hsymm h3n i j
  obtain ⟨DeltaA, hDeltaA, hDeltaA_source⟩ :=
    higham11_8_aasen_source_backward_error_of_factor_and_solve_residuals
      n A Afact DeltaS Bfactor Bsolve rhs w hfactor hDeltaS hsource
  refine ⟨DeltaA, hDeltaA, hDeltaA_source, ?_⟩
  have hBfactor_nonneg : ∀ i j : Fin n, 0 ≤ Bfactor i j := by
    intro i j
    exact mul_nonneg (gamma_nonneg fp h3n)
      (Finset.sum_nonneg (fun p _ =>
        Finset.sum_nonneg (fun q _ => by positivity)))
  have hBsolve_nonneg : ∀ i j : Fin n, 0 ≤ Bsolve i j :=
    higham11_15_aasenChainDeltaABound_nonneg
      n (gamma fp n) BT Lh Th Uouter hgamma_n hBT
  have hDelta_split : infNorm DeltaA ≤ infNorm Bfactor + infNorm Bsolve := by
    apply infNorm_le_of_row_sum_le
    · intro i
      have hfrow : ∑ j : Fin n, Bfactor i j ≤ infNorm Bfactor := by
        calc
          ∑ j : Fin n, Bfactor i j = ∑ j : Fin n, |Bfactor i j| := by
            apply Finset.sum_congr rfl
            intro j _
            rw [abs_of_nonneg (hBfactor_nonneg i j)]
          _ ≤ infNorm Bfactor := row_sum_le_infNorm Bfactor i
      have hsrow : ∑ j : Fin n, Bsolve i j ≤ infNorm Bsolve := by
        calc
          ∑ j : Fin n, Bsolve i j = ∑ j : Fin n, |Bsolve i j| := by
            apply Finset.sum_congr rfl
            intro j _
            rw [abs_of_nonneg (hBsolve_nonneg i j)]
          _ ≤ infNorm Bsolve := row_sum_le_infNorm Bsolve i
      calc
        ∑ j : Fin n, |DeltaA i j|
            ≤ ∑ j : Fin n, (Bfactor i j + Bsolve i j) :=
              Finset.sum_le_sum (fun j _ => hDeltaA i j)
        _ = (∑ j : Fin n, Bfactor i j) + ∑ j : Fin n, Bsolve i j :=
              Finset.sum_add_distrib
        _ ≤ infNorm Bfactor + infNorm Bsolve := add_le_add hfrow hsrow
    · exact add_nonneg (infNorm_nonneg _) (infNorm_nonneg _)
  have hBfactor_le :
      infNorm Bfactor ≤
        gamma fp (3 * n) * (infNorm Lh * infNorm Th * infNorm Uouter) := by
    have hMnonneg : ∀ i j : Fin n,
        0 ≤ ∑ p : Fin n, ∑ q : Fin n,
          |Lh i p| * |Th p q| * |Uouter q j| :=
      fun i j => Finset.sum_nonneg (fun p _ =>
        Finset.sum_nonneg (fun q _ => by positivity))
    have hscale : infNorm Bfactor ≤
        gamma fp (3 * n) * infNorm (fun i j =>
          ∑ p : Fin n, ∑ q : Fin n,
            |Lh i p| * |Th p q| * |Uouter q j|) :=
      infNorm_const_mul_le (gamma fp (3 * n)) (gamma_nonneg fp h3n) _ hMnonneg
    calc
      infNorm Bfactor ≤ gamma fp (3 * n) * infNorm (fun i j =>
          ∑ p : Fin n, ∑ q : Fin n,
            |Lh i p| * |Th p q| * |Uouter q j|) := hscale
      _ ≤ gamma fp (3 * n) * (infNorm Lh * infNorm Th * infNorm Uouter) :=
        mul_le_mul_of_nonneg_left
          (infNorm_tripleAbs_le hn_pos Lh Th Uouter) (gamma_nonneg fp h3n)
  have hBsolve_le :
      infNorm Bsolve ≤
        (2 * gamma fp n + (gamma fp n) ^ 2) *
            (infNorm Lh * infNorm Th * infNorm Uouter) +
          (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
            (infNorm Lh * infNorm BT * infNorm Uouter) :=
    higham11_15_aasenChainDeltaABound_infNorm_le
      n hn_pos (gamma fp n) BT Lh Th Uouter hgamma_n hBT
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hLn : infNorm Lh ≤ ((n - 1 : ℕ) : ℝ) := by
    rw [hcast]
    exact aasen_L_infNorm_le n hn Lh hLdiag_one hLupper hLfirst hLhat_cap
  have hUn : infNorm Uouter ≤ ((n - 1 : ℕ) : ℝ) := by
    rw [hcast]
    exact aasen_LT_infNorm_le n hn Lh hLdiag_one hLupper hLfirst hLhat_cap
  have halpha : (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hTnonneg : (0 : ℝ) ≤ infNorm Th := infNorm_nonneg _
  have hLU :
      infNorm Lh * infNorm Uouter ≤ ((n - 1 : ℕ) : ℝ) ^ 2 := by
    calc
      infNorm Lh * infNorm Uouter
          ≤ ((n - 1 : ℕ) : ℝ) * ((n - 1 : ℕ) : ℝ) :=
            mul_le_mul hLn hUn (infNorm_nonneg _) halpha
      _ = ((n - 1 : ℕ) : ℝ) ^ 2 := by ring
  have hP :
      infNorm Lh * infNorm Th * infNorm Uouter ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * infNorm Th := by
    calc
      infNorm Lh * infNorm Th * infNorm Uouter
          = (infNorm Lh * infNorm Uouter) * infNorm Th := by ring
      _ ≤ ((n - 1 : ℕ) : ℝ) ^ 2 * infNorm Th :=
        mul_le_mul_of_nonneg_right hLU hTnonneg
  have hQ :
      infNorm Lh * infNorm BT * infNorm Uouter ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * gamma fp k * infNorm Th := by
    calc
      infNorm Lh * infNorm BT * infNorm Uouter
          = (infNorm Lh * infNorm Uouter) * infNorm BT := by ring
      _ ≤ ((n - 1 : ℕ) : ℝ) ^ 2 * infNorm BT :=
        mul_le_mul_of_nonneg_right hLU (infNorm_nonneg _)
      _ ≤ ((n - 1 : ℕ) : ℝ) ^ 2 * (gamma fp k * infNorm Th) :=
        mul_le_mul_of_nonneg_left hBTnorm (sq_nonneg _)
      _ = ((n - 1 : ℕ) : ℝ) ^ 2 * gamma fp k * infNorm Th := by ring
  have hcT : 0 ≤ 2 * gamma fp n + (gamma fp n) ^ 2 := by positivity
  have hcB : 0 ≤ 1 + 2 * gamma fp n + (gamma fp n) ^ 2 := by
    nlinarith [sq_nonneg (1 + gamma fp n)]
  have hbracket :=
    higham11_8_direct_middle_gamma_k_bracket_le_gamma_15n25
      fp n k hn hk hval
  have t1 :
      gamma fp (3 * n) * (infNorm Lh * infNorm Th * infNorm Uouter) ≤
        gamma fp (3 * n) * (((n - 1 : ℕ) : ℝ) ^ 2 * infNorm Th) :=
    mul_le_mul_of_nonneg_left hP (gamma_nonneg fp h3n)
  have t2 :
      (2 * gamma fp n + (gamma fp n) ^ 2) *
          (infNorm Lh * infNorm Th * infNorm Uouter) ≤
        (2 * gamma fp n + (gamma fp n) ^ 2) *
          (((n - 1 : ℕ) : ℝ) ^ 2 * infNorm Th) :=
    mul_le_mul_of_nonneg_left hP hcT
  have t3 :
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
          (infNorm Lh * infNorm BT * infNorm Uouter) ≤
        (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
          (((n - 1 : ℕ) : ℝ) ^ 2 * gamma fp k * infNorm Th) :=
    mul_le_mul_of_nonneg_left hQ hcB
  calc
    infNorm DeltaA ≤ infNorm Bfactor + infNorm Bsolve := hDelta_split
    _ ≤ gamma fp (3 * n) * (infNorm Lh * infNorm Th * infNorm Uouter) +
          ((2 * gamma fp n + (gamma fp n) ^ 2) *
              (infNorm Lh * infNorm Th * infNorm Uouter) +
            (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
              (infNorm Lh * infNorm BT * infNorm Uouter)) :=
        add_le_add hBfactor_le hBsolve_le
    _ ≤ gamma fp (3 * n) * (((n - 1 : ℕ) : ℝ) ^ 2 * infNorm Th) +
          ((2 * gamma fp n + (gamma fp n) ^ 2) *
              (((n - 1 : ℕ) : ℝ) ^ 2 * infNorm Th) +
            (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
              (((n - 1 : ℕ) : ℝ) ^ 2 * gamma fp k * infNorm Th)) := by
        linarith [t1, t2, t3]
    _ = (gamma fp (3 * n) +
          (2 * gamma fp n + (gamma fp n) ^ 2) +
          (1 + 2 * gamma fp n + (gamma fp n) ^ 2) * gamma fp k) *
          (((n - 1 : ℕ) : ℝ) ^ 2 * infNorm Th) := by ring
    _ ≤ gamma fp (15 * n + 25) *
          (((n - 1 : ℕ) : ℝ) ^ 2 * infNorm Th) :=
        mul_le_mul_of_nonneg_right hbracket
          (mul_nonneg (sq_nonneg _) hTnonneg)
    _ = ((n - 1 : ℕ) : ℝ) ^ 2 *
          gamma fp (15 * n + 25) * infNorm Th := by ring

end NumStability.Ch11Closure.AasenDirectGEPP
