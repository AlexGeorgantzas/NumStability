import NumStability.Algorithms.LeastSquares.LSE
import NumStability.Algorithms.LeastSquares.Higham20Theorem20_3

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

namespace Theorem20_10

/-!
# Higham, Chapter 20, Theorem 20.10

This module gives a compact end-to-end surface for the rounded Householder GQR
path developed in `LSE.lean`.  In particular, the same named returned vector is
used in both parts of the theorem.  The construction computes Householder
panels for `Bᵀ` and the reversed trailing `A Q₂` block, computes the transformed
right-hand side, and performs the two rounded triangular solves.

The coefficients below are the explicit conservative gamma envelopes proved
for that concrete path.  They play the role of Higham's dimension-dependent
`γ̃_mn` and `γ̃_np` constants without claiming sharper constants than the local
implementation lemmas establish.
-/

/-- The proof-level returned vector of the concrete rounded Householder GQR
path.  Its specification identifies it with the rounded transformed-tail
triangular solve for the constructed GQR record. -/
noncomputable def computedX {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold
          hB hStack) :
    Fin (p + q) → ℝ :=
  theorem20_10_constructed_householder_returned_xhat
    fp A B b d hp hq hB hStack hu

/-- The concrete rounded Householder GQR path supplies the Part (a)
perturbation certificate for its named returned vector.

This is the missing consolidation step between the already proved concrete
factor/RHS construction, rank preservation, rounded triangular solves, and the
generic Part (a) certificate.  No perturbed rank, nonzero triangular diagonal,
or computed-vector identification is assumed: all three are discharged from
the source ranks and the single public unit-roundoff threshold. -/
theorem computedX_partA_certificate
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold
          hB hStack) :
    Nonempty
      (Theorem20_10PartAPerturbationCertificate A B b d
        (computedX fp A B b d hp hq hB hStack hu)
        (theorem20_10_householder_composed_partA_gammaA fp r p q)
        (theorem20_10_householder_composed_partA_gammaB fp r p q)) := by
  let xhat : Fin (p + q) → ℝ :=
    theorem20_10_constructed_householder_returned_xhat
      fp A B b d hp hq hB hStack hu
  let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
    fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
  let beta : Fin q → ℝ :=
    theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
  rcases
      theorem20_10_constructed_householder_returned_xhat_rank_preserved_triangular_solve_and_exact_perturbed_minimizer_of_source_ranks_unit_roundoff_smallnessThreshold_composed_conservative_gamma
        fp A B b d hp hq hB hStack hu with
    ⟨DeltaA0, DeltaB0, Deltab0, _hDeltaBrep, hDeltaA0, hDeltaB0,
      hDeltab0, hpert, _hQeq, _hSeq, htail, hxhat, hrank,
      _htri, _hpartB⟩
  have hdiag :
      (∀ i : Fin p, hpert.S i i ≠ 0) ∧
        (∀ i : Fin q, hpert.L22 i i ≠ 0) :=
    (hpert.fullRowRank_stackedFullColumnRank_iff_s_l22_diag_ne_zero).1 hrank
  rcases
      theorem20_10_householder_component_unit_roundoff_conditions_of_lt_smallnessThreshold
        fp hB hStack hp hq hu with
    ⟨hsmallA, hsmallB, _hhalf, _hunit⟩
  have hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)) := by
    unfold gammaValid
    exact lt_of_le_of_lt hsmallA (by norm_num)
  have hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)) := by
    unfold gammaValid
    exact lt_of_le_of_lt hsmallB (by norm_num)
  have hKA_ge_two : 2 ≤ householderConstructApplyGammaIndex (r + q) := by
    dsimp [householderConstructApplyGammaIndex]
    omega
  have hKB_ge_two : 2 ≤ householderConstructApplyGammaIndex (p + q) := by
    dsimp [householderConstructApplyGammaIndex]
    omega
  have hvalid2S : gammaValid fp (2 * p) := by
    apply gammaValid_mono fp _ hvalidB
    calc
      2 * p = p * 2 := by omega
      _ ≤ p * householderConstructApplyGammaIndex (p + q) :=
        Nat.mul_le_mul_left p hKB_ge_two
  have hvalid2L22 : gammaValid fp (2 * q) := by
    apply gammaValid_mono fp _ hvalidA
    calc
      2 * q ≤ 2 * (p + q) := Nat.mul_le_mul_left 2 (by omega)
      _ = (p + q) * 2 := by omega
      _ ≤ (p + q) * householderConstructApplyGammaIndex (r + q) :=
        Nat.mul_le_mul_left (p + q) hKA_ge_two
  have hvalidp : gammaValid fp p :=
    gammaValid_mono fp (by omega) hvalid2S
  have hvalidq : gammaValid fp q :=
    gammaValid_mono fp (by omega) hvalid2L22
  have hgammap_nonneg : 0 ≤ gamma fp p := gamma_nonneg fp hvalidp
  have hgammaq_nonneg : 0 ≤ gamma fp q := gamma_nonneg fp hvalidq
  rcases
      theorem20_10_partA_certificate_of_constructed_perturbed_source_blocks_of_double_gammaValid_source_bounds_transformed_tail
        fp hpert beta (fun i => b i + Deltab0 i) d
        (gamma fp q) (gamma fp p) (0 : Fin (r + q) → ℝ)
        hgammap_nonneg le_rfl le_rfl hdiag.1 hdiag.2 hvalid2S hvalid2L22 with
    ⟨_DeltaS, _DeltaL22, _hDeltaS, _hDeltaL22,
      _hDeltaSfrob, _hDeltaL22frob, hcert⟩
  have hzero :
      vecNorm2 (0 : Fin (r + q) → ℝ) ≤
        gamma fp q * vecNorm2 (fun i => b i + Deltab0 i) := by
    change vecNorm2 (fun _ : Fin (r + q) => 0) ≤
      gamma fp q * vecNorm2 (fun i => b i + Deltab0 i)
    rw [vecNorm2_zero]
    exact mul_nonneg hgammaq_nonneg (vecNorm2_nonneg _)
  have htail0 : ∀ j : Fin q,
      matMulVec (r + q) (matTranspose hpert.U)
          (fun k => (b k + Deltab0 k) + (0 : Fin (r + q) → ℝ) k)
          (Fin.natAdd r j) = beta j := by
    intro j
    simpa using htail j
  have hcert2 := hcert hzero htail0
  have hxhat' :
      xhat = theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d := by
    simpa [xhat, Qb, beta] using hxhat
  rw [← hxhat'] at hcert2
  have hgammaB0_nonneg :
      0 ≤ theorem20_10_householder_gammaB fp r p q := by
    simpa [theorem20_10_householder_gammaB] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalidB
  have hgammaB_solution :
      gamma fp p ≤ theorem20_10_householder_composed_partA_gammaB fp r p q := by
    dsimp [theorem20_10_householder_composed_partA_gammaB]
    nlinarith
  have hcomposed :
      Nonempty
        (Theorem20_10PartAPerturbationCertificate A B b d xhat
          (theorem20_10_householder_composed_partA_gammaA fp r p q)
          (theorem20_10_householder_composed_partA_gammaB fp r p q)) :=
    theorem20_10_nonempty_partA_certificate_compose_source_perturbations
      A B b d xhat DeltaA0 DeltaB0 Deltab0
      hgammaq_nonneg hgammap_nonneg hDeltaA0 hDeltaB0 hDeltab0
      (by
        dsimp [theorem20_10_householder_composed_partA_gammaA]
        exact le_max_left _ _)
      (by
        dsimp [theorem20_10_householder_composed_partA_gammaA]
        exact le_max_right _ _)
      (by
        dsimp [theorem20_10_householder_composed_partA_gammaB]
        exact le_rfl)
      hgammaB_solution hcert2
  simpa [computedX, xhat] using hcomposed

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), for the same named
computed Householder GQR vector used by Part (b).

The conclusion is the printed mixed-stability form: the returned vector is an
`O(γ̃_np)` relative perturbation of the exact solution of an LSE problem whose
`A`, `B`, and `b` data have the displayed `O(γ̃_mn)`/`O(γ̃_np)` normwise
perturbations, while `d` is unchanged. -/
theorem computedX_partA_mixed_stability
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold
          hB hStack) :
    let xhat := computedX fp A B b d hp hq hB hStack hu
    let gammaA := theorem20_10_householder_composed_partA_gammaA fp r p q
    let gammaB := theorem20_10_householder_composed_partA_gammaB fp r p q
    ∃ (DeltaA : Fin (r + q) → Fin (p + q) → ℝ)
      (DeltaB : Fin p → Fin (p + q) → ℝ)
      (Deltab : Fin (r + q) → ℝ)
      (DeltaX : Fin (p + q) → ℝ)
      (x : Fin (p + q) → ℝ),
      (∀ j, xhat j = x j + DeltaX j) ∧
      vecNorm2 DeltaX ≤ gammaB * vecNorm2 x ∧
      frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
      vecNorm2 Deltab ≤ gammaA * vecNorm2 b ∧
      frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
      IsLSEMinimizer
        (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i)
        (fun i j => B i j + DeltaB i j) d x := by
  dsimp
  rcases computedX_partA_certificate fp A B b d hp hq hB hStack hu with
    ⟨cert⟩
  have hcore :=
    theorem20_10_partA_mixed_stability_of_perturbation_certificate
      A B b d (computedX fp A B b d hp hq hB hStack hu) cert
  dsimp at hcore
  rcases hcore with
    ⟨DeltaA, DeltaB, Deltab, DeltaX, x,
      hAeq, hBeq, hbeq, hxhat, hDeltaX, hDeltaA,
      hDeltab, hDeltaB, hx, _hmethod⟩
  subst DeltaA
  subst DeltaB
  subst Deltab
  exact
    ⟨cert.DeltaA, cert.DeltaB, cert.Deltab, DeltaX, x, hxhat, hDeltaX,
      hDeltaA, hDeltab, hDeltaB, hx⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b), for the same named
computed Householder GQR vector used by Part (a).

The vector is the exact solution of a perturbed LSE problem, including a
constraint-right-hand-side perturbation.  All four perturbations carry the
explicit normwise budgets in the source theorem. -/
theorem computedX_partB_backward_error
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold
          hB hStack) :
    let xhat := computedX fp A B b d hp hq hB hStack hu
    let gammaA := theorem20_10_householder_composed_partA_gammaA fp r p q
    let gammaB := theorem20_10_householder_composed_partA_gammaB fp r p q
    ∃ (DeltaA : Fin (r + q) → Fin (p + q) → ℝ)
      (DeltaB : Fin p → Fin (p + q) → ℝ)
      (Deltab : Fin (r + q) → ℝ)
      (Deltad : Fin p → ℝ),
      frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
      frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
      vecNorm2 Deltab ≤
        gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
      vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
      IsLSEMinimizer
        (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i)
        (fun i j => B i j + DeltaB i j)
        (fun i => d i + Deltad i) xhat := by
  dsimp
  rcases
      theorem20_10_constructed_householder_returned_xhat_exact_perturbed_minimizer_of_source_ranks_unit_roundoff_smallnessThreshold_composed_conservative_gamma
        fp A B b d hp hq hB hStack hu with
    ⟨DeltaA, DeltaB, Deltab, Deltad, hDeltad,
      hDeltaA, hDeltaB, hDeltab, hDeltadBound, hxhat, _hunique⟩
  exact
    ⟨DeltaA, DeltaB, Deltab, Deltad,
      hDeltaA, hDeltaB, hDeltab, hDeltadBound, hxhat⟩

/-! ## Empty-constraint boundary (`p = 0`) -/

private theorem orthogonal_matMulVec_injective {n : ℕ}
    {U : Fin n → Fin n → ℝ} (hU : IsOrthogonal n U) :
    Function.Injective (matMulVec n U) := by
  intro x y hxy
  ext i
  calc
    x i = matMulVec n (idMatrix n) x i :=
      (congrFun (matMulVec_id n x) i).symm
    _ = matMulVec n (matMul n (matTranspose U) U) x i := by
          congr 2
          ext a b
          exact (hU.left_inv a b).symm
    _ = matMulVec n (matTranspose U) (matMulVec n U x) i :=
          matMulVec_matMul n (matTranspose U) U x i
    _ = matMulVec n (matTranspose U) (matMulVec n U y) i := by
          rw [hxy]
    _ = matMulVec n (matMul n (matTranspose U) U) y i :=
          (matMulVec_matMul n (matTranspose U) U y i).symm
    _ = matMulVec n (idMatrix n) y i := by
          congr 2
          ext a b
          exact hU.left_inv a b
    _ = y i := congrFun (matMulVec_id n y) i

/-- The genuine computed `p = 0` branch of the GQR method is the ordinary
Householder-QR least-squares algorithm: transform `A` and `b` with the same
rounded panel and solve its computed top triangular block with `fl_backSub`.

This is a literal implementation path, not a selected exact minimizer. -/
noncomputable def computedX_emptyConstraints {r q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin q → ℝ) (b : Fin (r + q) → ℝ) :
    Fin q → ℝ :=
  Theorem20_3.computedX fp A b (Nat.le_add_left q r)

/-- A positive unit-roundoff threshold for the empty-constraint branch.  Its
first cap validates every gamma index used by the concrete QR least-squares
path.  Its second cap keeps the QR panel perturbation below the source stacked
full-column-rank margin. -/
noncomputable def emptyConstraintUnitRoundoffSmallnessThreshold
    {r q : ℕ} {A : Fin (r + q) → Fin q → ℝ}
    {B : Fin 0 → Fin q → ℝ}
    (hStack : LSEStackedFullColumnRank A B) : ℝ :=
  let N := Theorem20_3.gammaIndex (r + q) q
  min
    (((1 : ℝ) / 2) / (N : ℝ))
    (hStack.vecNorm2LowerMargin /
      ((2 : ℝ) * (N : ℝ) * (1 + frobNormRect A)))

/-- Positivity of the empty-constraint unit-roundoff threshold under the
source dimension condition `q > 0`. -/
theorem emptyConstraintUnitRoundoffSmallnessThreshold_pos
    {r q : ℕ} {A : Fin (r + q) → Fin q → ℝ}
    {B : Fin 0 → Fin q → ℝ}
    (hq : 0 < q) (hStack : LSEStackedFullColumnRank A B) :
    0 < emptyConstraintUnitRoundoffSmallnessThreshold hStack := by
  let N := Theorem20_3.gammaIndex (r + q) q
  have hqN : q ≤ N := by
    simp [N, Theorem20_3.gammaIndex]
  have hNnat : 0 < N := lt_of_lt_of_le hq hqN
  have hN : (0 : ℝ) < N := by exact_mod_cast hNnat
  have hnorm : 0 ≤ frobNormRect A := frobNormRect_nonneg A
  have hden : 0 < (2 : ℝ) * (N : ℝ) * (1 + frobNormRect A) := by
    positivity
  dsimp [emptyConstraintUnitRoundoffSmallnessThreshold]
  exact lt_min (div_pos (by norm_num) hN)
    (div_pos hStack.vecNorm2LowerMargin_pos hden)

/-- The boundary threshold supplies both global gamma validity and the strict
QR-panel perturbation budget needed to preserve source full column rank. -/
theorem emptyConstraint_unit_roundoff_conditions_of_lt_smallnessThreshold
    {r q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin q → ℝ}
    {B : Fin 0 → Fin q → ℝ}
    (hq : 0 < q) (hStack : LSEStackedFullColumnRank A B)
    (hu : fp.u < emptyConstraintUnitRoundoffSmallnessThreshold hStack) :
    gammaValid fp (Theorem20_3.gammaIndex (r + q) q) ∧
      gamma fp (q * householderConstructApplyGammaIndex (r + q)) *
          frobNormRect A < hStack.vecNorm2LowerMargin := by
  let N := Theorem20_3.gammaIndex (r + q) q
  let K := householderConstructApplyGammaIndex (r + q)
  have hqN : q ≤ N := by
    simp [N, Theorem20_3.gammaIndex]
  have hidxN : q * K ≤ N := by
    dsimp [N, K, Theorem20_3.gammaIndex]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hNnat : 0 < N := lt_of_lt_of_le hq hqN
  have hN : (0 : ℝ) < N := by exact_mod_cast hNnat
  have hnorm : 0 ≤ frobNormRect A := frobNormRect_nonneg A
  have honeNorm : 0 < 1 + frobNormRect A := by linarith
  have hden : 0 < (2 : ℝ) * (N : ℝ) * (1 + frobNormRect A) := by
    positivity
  have huHalf : fp.u < ((1 : ℝ) / 2) / (N : ℝ) :=
    lt_of_lt_of_le hu (by
      dsimp [emptyConstraintUnitRoundoffSmallnessThreshold]
      exact min_le_left _ _)
  have huRank :
      fp.u < hStack.vecNorm2LowerMargin /
        ((2 : ℝ) * (N : ℝ) * (1 + frobNormRect A)) :=
    lt_of_lt_of_le hu (by
      dsimp [emptyConstraintUnitRoundoffSmallnessThreshold]
      exact min_le_right _ _)
  have hNu_lt : (N : ℝ) * fp.u < 1 / 2 := by
    have := (lt_div_iff₀ hN).mp huHalf
    nlinarith
  have hhalf : (N : ℝ) * fp.u ≤ 1 / 2 := le_of_lt hNu_lt
  have hvalidN : gammaValid fp N := by
    unfold gammaValid
    linarith
  have hgammaN : gamma fp N ≤ 2 * ((N : ℝ) * fp.u) :=
    gamma_le_two_mul_n_u_of_nu_le_half fp N hhalf
  have hgammaIdx : gamma fp (q * K) ≤ gamma fp N :=
    gamma_mono fp hidxN hvalidN
  have hRankProduct :
      fp.u * ((2 : ℝ) * (N : ℝ) * (1 + frobNormRect A)) <
        hStack.vecNorm2LowerMargin :=
    (lt_div_iff₀ hden).mp huRank
  constructor
  · simpa [N] using hvalidN
  · calc
      gamma fp (q * householderConstructApplyGammaIndex (r + q)) *
            frobNormRect A
          ≤ gamma fp N * frobNormRect A := by
              exact mul_le_mul_of_nonneg_right
                (by simpa [K] using hgammaIdx) hnorm
      _ ≤ (2 * ((N : ℝ) * fp.u)) * frobNormRect A := by
              exact mul_le_mul_of_nonneg_right hgammaN hnorm
      _ ≤ fp.u * ((2 : ℝ) * (N : ℝ) * (1 + frobNormRect A)) := by
              nlinarith [fp.u_nonneg, hN, hnorm]
      _ < hStack.vecNorm2LowerMargin := hRankProduct

/-- Source full column rank and the boundary unit-roundoff threshold imply
nonbreakdown of the actual computed top triangular QR block.  Thus the
ordinary least-squares solver's public diagonal guard is derived rather than
added to the empty-constraint Theorem 20.10 surface. -/
theorem computedR_emptyConstraints_diag_ne_zero
    {r q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin q → ℝ)
    (B : Fin 0 → Fin q → ℝ)
    (hq : 0 < q) (hStack : LSEStackedFullColumnRank A B)
    (hu : fp.u < emptyConstraintUnitRoundoffSmallnessThreshold hStack) :
    ∀ i : Fin q,
      Theorem20_3.computedR fp A (Nat.le_add_left q r) i i ≠ 0 := by
  let m := r + q
  let hqm : q ≤ m := Nat.le_add_left q r
  let Q : Fin m → Fin m → ℝ := fl_householderQRPanel_Q fp m q A
  let Rhat : Fin m → Fin q → ℝ := fl_householderQRPanel_R fp m q A
  let R : Fin q → Fin q → ℝ := Theorem20_3.computedR fp A hqm
  rcases
      emptyConstraint_unit_roundoff_conditions_of_lt_smallnessThreshold
        fp hq hStack hu with
    ⟨hvalid, hpanelSmall⟩
  have hvalidQR :
      gammaValid fp (q * householderConstructApplyGammaIndex m) := by
    apply gammaValid_mono fp _ hvalid
    dsimp [m, Theorem20_3.gammaIndex]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hsteps : 0 < Nat.min m q := by
    simpa [Nat.min_eq_right hqm] using hq
  have hpanel :=
    fl_householderQRPanel_R_columnwise_backward_error_gammaHigham_of_global_gammaValid
      fp m q A hsteps (by simpa [Nat.min_eq_right hqm] using hvalidQR)
  rcases hpanel.result with ⟨DeltaA, hrep, hDeltaAraw, _hDeltaAcols⟩
  have hDeltaA :
      frobNormRect DeltaA ≤
        gamma fp (q * householderConstructApplyGammaIndex m) *
          frobNormRect A := by
    simpa [Nat.min_eq_right hqm, frobNormRect_eq_frobNormFn] using
      hDeltaAraw
  have hDeltaASmall :
      frobNormRect DeltaA < hStack.vecNorm2LowerMargin := by
    exact lt_of_le_of_lt hDeltaA (by simpa [m] using hpanelSmall)
  let DeltaB : Fin 0 → Fin q → ℝ := fun i => Fin.elim0 i
  have hDeltaB : frobNormRect DeltaB ≤ 0 := by
    simp [DeltaB, frobNormRect, frobNormSqRect]
  have hStackOp :
      rectOpNorm2Le (lseStackedMatrix DeltaA DeltaB)
        (frobNormRect DeltaA + 0) :=
    rectOpNorm2Le_lseStackedMatrix_of_frobNormRect_bounds
      (le_refl (frobNormRect DeltaA)) hDeltaB
  have hStackPert :
      LSEStackedFullColumnRank
        (fun i j => A i j + DeltaA i j)
        (fun i j => B i j + DeltaB i j) :=
    LSEStackedFullColumnRank.of_lower_bound_and_rectOpNorm2Le_lt
      hStack.vecNorm2LowerMargin_lower_bound hStackOp (by
        simpa using hDeltaASmall)
  have hAinj :
      Function.Injective
        (rectMatMulVec (fun i j => A i j + DeltaA i j)) :=
    (lseStackedFullColumnRank_empty_constraints_iff
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j)).1 hStackPert
  have hRinj : Function.Injective (rectMatMulVec R) := by
    intro x y hxy
    apply hAinj
    have hfull : rectMatMulVec Rhat x = rectMatMulVec Rhat y := by
      ext i
      by_cases hi : i.val < q
      · let iq : Fin q := ⟨i.val, hi⟩
        have hiq := congrFun hxy iq
        simpa [R, Rhat, Theorem20_3.computedR, iq, hqm] using hiq
      · have hqi : q ≤ i.val := Nat.le_of_not_gt hi
        unfold rectMatMulVec
        apply Finset.sum_congr rfl
        intro j _hj
        have hzero : Rhat i j = 0 := by
          exact hpanel.upper i j (lt_of_lt_of_le j.isLt hqi)
        simp [hzero]
    have hmatrix :
        Rhat = matMulRectLeft (matTranspose Q)
          (fun i j => A i j + DeltaA i j) := by
      ext i j
      simpa [Rhat, Q, matMulRectLeft, matMulRect] using hrep i j
    rw [hmatrix] at hfull
    rw [rectMatMulVec_matMulRectLeft,
      rectMatMulVec_matMulRectLeft] at hfull
    exact orthogonal_matMulVec_injective hpanel.orth.transpose hfull
  have hupper : ∀ i j : Fin q, j.val < i.val → R i j = 0 := by
    intro i j hji
    exact hpanel.upper
      ⟨i.val, lt_of_lt_of_le i.isLt hqm⟩ j hji
  have hdet : Matrix.det (R : Matrix (Fin q) (Fin q) ℝ) ≠ 0 :=
    rectMatMulVec_det_ne_zero_of_injective hRinj
  have hdiag : ∀ i : Fin q, R i i ≠ 0 :=
    diag_ne_zero_of_upper_triangular_det_ne_zero q R hupper hdet
  simpa [R, hqm, m] using hdiag

/-- Core backward-error package for the literal empty-constraint computed
branch.  It is Theorem 20.3's Householder-QR/`fl_backSub` result, strengthened
from columnwise to Frobenius matrix control and transported across the exact
equivalence between ordinary and zero-row-constrained least squares. -/
theorem computedX_emptyConstraints_backward_error
    {r q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin q → ℝ)
    (B : Fin 0 → Fin q → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin 0 → ℝ)
    (hq : 0 < q) (hStack : LSEStackedFullColumnRank A B)
    (hu : fp.u < emptyConstraintUnitRoundoffSmallnessThreshold hStack) :
    let gammaA := Theorem20_3.gamma_tilde_mn fp (r + q) q
    ∃ (DeltaA : Fin (r + q) → Fin q → ℝ)
      (Deltab : Fin (r + q) → ℝ),
      frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
      vecNorm2 Deltab ≤ gammaA * vecNorm2 b ∧
      IsLSEMinimizer
        (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) B d
        (computedX_emptyConstraints fp A b) := by
  dsimp
  let hqm : q ≤ r + q := Nat.le_add_left q r
  have hvalid : gammaValid fp (Theorem20_3.gammaIndex (r + q) q) :=
    (emptyConstraint_unit_roundoff_conditions_of_lt_smallnessThreshold
      fp hq hStack hu).1
  have hdiag : ∀ i : Fin q, Theorem20_3.computedR fp A hqm i i ≠ 0 := by
    simpa [hqm] using
      computedR_emptyConstraints_diag_ne_zero fp A B hq hStack hu
  rcases
      Theorem20_3.householder_qr_fl_backSub_backward_error
        fp A b hq hqm hvalid hdiag with
    ⟨DeltaA, Deltab, hDeltaAcols, hDeltab, hmin⟩
  have hvalidQR :
      gammaValid fp
        (q * householderConstructApplyGammaIndex (r + q)) := by
    apply gammaValid_mono fp _ hvalid
    dsimp [Theorem20_3.gammaIndex]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hvalidq : gammaValid fp q := by
    apply gammaValid_mono fp _ hvalid
    simp [Theorem20_3.gammaIndex]
  have heta : 0 ≤ H19.Theorem19_4.gamma_tilde fp (r + q) q := by
    simpa [H19.Theorem19_4.gamma_tilde,
      Nat.min_eq_right hqm] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalidQR
  have hgammaq : 0 ≤ gamma fp q := gamma_nonneg fp hvalidq
  have hmatrixCoeff : 0 ≤ Theorem20_3.matrixCoeff fp (r + q) q := by
    dsimp [Theorem20_3.matrixCoeff]
    positivity
  have hgammaA : 0 ≤ Theorem20_3.gamma_tilde_mn fp (r + q) q :=
    le_trans hmatrixCoeff (le_max_left _ _)
  have hDeltaA :
      frobNormRect DeltaA ≤
        Theorem20_3.gamma_tilde_mn fp (r + q) q * frobNormRect A :=
    frobNormRect_le_of_col_vecNorm2_le DeltaA A hgammaA hDeltaAcols
  refine ⟨DeltaA, Deltab, hDeltaA, hDeltab, ?_⟩
  apply (isLSEMinimizer_empty_constraints_iff
    (fun i j => A i j + DeltaA i j)
    (fun i => b i + Deltab i) B d
    (computedX_emptyConstraints fp A b)).2
  simpa [computedX_emptyConstraints, hqm] using hmin

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), at the source-permitted
boundary `p = 0`, `q > 0`.

The returned vector is the literal Householder-QR least-squares vector.  It is
already an exact minimizer for perturbed `A` and `b`, so the source theorem's
solution perturbation and empty constraint perturbation can both be zero. -/
theorem computedX_emptyConstraints_partA_mixed_stability
    {r q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin q → ℝ)
    (B : Fin 0 → Fin q → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin 0 → ℝ)
    (hq : 0 < q) (hStack : LSEStackedFullColumnRank A B)
    (hu : fp.u < emptyConstraintUnitRoundoffSmallnessThreshold hStack) :
    let xhat := computedX_emptyConstraints fp A b
    let gammaA := Theorem20_3.gamma_tilde_mn fp (r + q) q
    let gammaB : ℝ := 0
    ∃ (DeltaA : Fin (r + q) → Fin q → ℝ)
      (DeltaB : Fin 0 → Fin q → ℝ)
      (Deltab : Fin (r + q) → ℝ)
      (DeltaX : Fin q → ℝ)
      (x : Fin q → ℝ),
      (∀ j, xhat j = x j + DeltaX j) ∧
      vecNorm2 DeltaX ≤ gammaB * vecNorm2 x ∧
      frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
      vecNorm2 Deltab ≤ gammaA * vecNorm2 b ∧
      frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
      IsLSEMinimizer
        (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i)
        (fun i j => B i j + DeltaB i j) d x := by
  dsimp
  rcases computedX_emptyConstraints_backward_error
      fp A B b d hq hStack hu with
    ⟨DeltaA, Deltab, hDeltaA, hDeltab, hmin⟩
  let DeltaB : Fin 0 → Fin q → ℝ := fun i => Fin.elim0 i
  let DeltaX : Fin q → ℝ := fun _ => 0
  refine
    ⟨DeltaA, DeltaB, Deltab, DeltaX,
      computedX_emptyConstraints fp A b, ?_, ?_, hDeltaA, hDeltab, ?_, ?_⟩
  · intro j
    simp [DeltaX]
  · simp [DeltaX, vecNorm2_zero]
  · simp [DeltaB, frobNormRect, frobNormSqRect]
  · apply (isLSEMinimizer_empty_constraints_iff
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j) d
      (computedX_emptyConstraints fp A b)).2
    exact (isLSEMinimizer_empty_constraints_iff
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i) B d
      (computedX_emptyConstraints fp A b)).1 hmin

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b), at the source-permitted
boundary `p = 0`, `q > 0`.

The same literal Householder-QR least-squares vector is an exact solution of a
perturbed empty-constraint LSE problem.  The absent constraint matrix and
right-hand side have identically zero perturbations and coefficient. -/
theorem computedX_emptyConstraints_partB_backward_error
    {r q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin q → ℝ)
    (B : Fin 0 → Fin q → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin 0 → ℝ)
    (hq : 0 < q) (hStack : LSEStackedFullColumnRank A B)
    (hu : fp.u < emptyConstraintUnitRoundoffSmallnessThreshold hStack) :
    let xhat := computedX_emptyConstraints fp A b
    let gammaA := Theorem20_3.gamma_tilde_mn fp (r + q) q
    let gammaB : ℝ := 0
    ∃ (DeltaA : Fin (r + q) → Fin q → ℝ)
      (DeltaB : Fin 0 → Fin q → ℝ)
      (Deltab : Fin (r + q) → ℝ)
      (Deltad : Fin 0 → ℝ),
      frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
      frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
      vecNorm2 Deltab ≤
        gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
      vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
      IsLSEMinimizer
        (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i)
        (fun i j => B i j + DeltaB i j)
        (fun i => d i + Deltad i) xhat := by
  dsimp
  rcases computedX_emptyConstraints_backward_error
      fp A B b d hq hStack hu with
    ⟨DeltaA, Deltab, hDeltaA, hDeltab, hmin⟩
  let DeltaB : Fin 0 → Fin q → ℝ := fun i => Fin.elim0 i
  let Deltad : Fin 0 → ℝ := fun i => Fin.elim0 i
  refine ⟨DeltaA, DeltaB, Deltab, Deltad, hDeltaA, ?_, ?_, ?_, ?_⟩
  · simp [DeltaB, frobNormRect, frobNormSqRect]
  · simpa using hDeltab
  · have hDeltadZero : Deltad = (0 : Fin 0 → ℝ) := by
      funext i
      exact Fin.elim0 i
    rw [hDeltadZero]
    have hzeroNorm : vecNorm2 (0 : Fin 0 → ℝ) = 0 := by
      change vecNorm2 (fun _ : Fin 0 => 0) = 0
      exact vecNorm2_zero
    rw [hzeroNorm]
    norm_num
  · apply (isLSEMinimizer_empty_constraints_iff
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i)
      (computedX_emptyConstraints fp A b)).2
    exact (isLSEMinimizer_empty_constraints_iff
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i) B d
      (computedX_emptyConstraints fp A b)).1 hmin

/-! ## Full-constraint boundary (`q = 0`) -/

/-- The computed lower-triangular constraint block obtained from the literal
rounded Householder QR panel of `Bᵀ` when `B` is square. -/
noncomputable def computedS_fullConstraints {p : ℕ} (fp : FPModel)
    (B : Fin p → Fin p → ℝ) : Fin p → Fin p → ℝ :=
  matTranspose (fl_householderQRPanel_R fp p p (finiteTranspose B))

/-- The genuine computed `q = 0` branch: triangularize `Bᵀ`, solve the
computed lower-triangular constraint system with `fl_forwardSub`, and map the
coordinates back with the computed Householder orthogonal factor. -/
noncomputable def computedX_fullConstraints {p : ℕ} (fp : FPModel)
    (B : Fin p → Fin p → ℝ) (d : Fin p → ℝ) : Fin p → ℝ :=
  let Q := fl_householderQRPanel_Q fp p p (finiteTranspose B)
  let S := computedS_fullConstraints fp B
  matMulVec p Q (fl_forwardSub fp p S d)

/-- A single gamma horizon for the square constraint panel and its rounded
forward solve. -/
def fullConstraintGammaIndex (p : ℕ) : ℕ :=
  max p (p * householderConstructApplyGammaIndex p)

/-- The source rank radius used by the `q = 0` branch.  Retaining both source
margins mirrors the two assumptions in (20.24), even though square full row
rank alone already implies stacked full column rank. -/
noncomputable def fullConstraintSourceRankRadius
    {r p : ℕ} {A : Fin r → Fin p → ℝ} {B : Fin p → Fin p → ℝ}
    (hB : LSEFullRowRank B) (hStack : LSEStackedFullColumnRank A B) : ℝ :=
  min hB.transposeVecNorm2LowerMargin hStack.vecNorm2LowerMargin

/-- Positive unit-roundoff threshold for the square constraint-only branch.
The first cap validates the panel and solve gamma indices; the second keeps
the composed constraint perturbation below both source rank margins. -/
noncomputable def fullConstraintUnitRoundoffSmallnessThreshold
    {r p : ℕ} {A : Fin r → Fin p → ℝ} {B : Fin p → Fin p → ℝ}
    (hB : LSEFullRowRank B) (hStack : LSEStackedFullColumnRank A B) : ℝ :=
  let N := fullConstraintGammaIndex p
  min
    (((1 : ℝ) / 2) / (N : ℝ))
    (fullConstraintSourceRankRadius hB hStack /
      ((6 : ℝ) * (N : ℝ) * (1 + frobNormRect B)))

/-- Positivity of the full-constraint threshold for `p > 0`. -/
theorem fullConstraintUnitRoundoffSmallnessThreshold_pos
    {r p : ℕ} {A : Fin r → Fin p → ℝ} {B : Fin p → Fin p → ℝ}
    (hp : 0 < p) (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B) :
    0 < fullConstraintUnitRoundoffSmallnessThreshold hB hStack := by
  let N := fullConstraintGammaIndex p
  have hpN : p ≤ N := by simp [N, fullConstraintGammaIndex]
  have hNnat : 0 < N := lt_of_lt_of_le hp hpN
  have hN : (0 : ℝ) < N := by exact_mod_cast hNnat
  have hradius : 0 < fullConstraintSourceRankRadius hB hStack := by
    dsimp [fullConstraintSourceRankRadius]
    exact lt_min hB.transposeVecNorm2LowerMargin_pos
      hStack.vecNorm2LowerMargin_pos
  have hden : 0 < (6 : ℝ) * (N : ℝ) * (1 + frobNormRect B) := by
    have hnorm := frobNormRect_nonneg B
    positivity
  dsimp [fullConstraintUnitRoundoffSmallnessThreshold]
  exact lt_min (div_pos (by norm_num) hN) (div_pos hradius hden)

/-- The full-constraint threshold validates the literal panel/solve path and
bounds the composed matrix perturbation strictly below both source margins. -/
theorem fullConstraint_unit_roundoff_conditions_of_lt_smallnessThreshold
    {r p : ℕ} (fp : FPModel)
    {A : Fin r → Fin p → ℝ} {B : Fin p → Fin p → ℝ}
    (hp : 0 < p) (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu : fp.u < fullConstraintUnitRoundoffSmallnessThreshold hB hStack) :
    gammaValid fp (p * householderConstructApplyGammaIndex p) ∧
      gammaValid fp p ∧
      theorem20_10_householder_composed_partA_gammaB fp r p 0 *
          frobNormRect B < fullConstraintSourceRankRadius hB hStack := by
  let N := fullConstraintGammaIndex p
  let idx := p * householderConstructApplyGammaIndex p
  have hpN : p ≤ N := by simp [N, fullConstraintGammaIndex]
  have hidxN : idx ≤ N := by simp [N, idx, fullConstraintGammaIndex]
  have hNnat : 0 < N := lt_of_lt_of_le hp hpN
  have hN : (0 : ℝ) < N := by exact_mod_cast hNnat
  have hnorm : 0 ≤ frobNormRect B := frobNormRect_nonneg B
  have hden : 0 < (6 : ℝ) * (N : ℝ) * (1 + frobNormRect B) := by
    positivity
  have huHalf : fp.u < ((1 : ℝ) / 2) / (N : ℝ) :=
    lt_of_lt_of_le hu (by
      dsimp [fullConstraintUnitRoundoffSmallnessThreshold]
      exact min_le_left _ _)
  have huRank :
      fp.u < fullConstraintSourceRankRadius hB hStack /
        ((6 : ℝ) * (N : ℝ) * (1 + frobNormRect B)) :=
    lt_of_lt_of_le hu (by
      dsimp [fullConstraintUnitRoundoffSmallnessThreshold]
      exact min_le_right _ _)
  have hNu_lt : (N : ℝ) * fp.u < 1 / 2 := by
    have := (lt_div_iff₀ hN).mp huHalf
    nlinarith
  have hhalfN : (N : ℝ) * fp.u ≤ 1 / 2 := le_of_lt hNu_lt
  have hvalidN : gammaValid fp N := by
    unfold gammaValid
    linarith
  have hvalidIdx : gammaValid fp idx := gammaValid_mono fp hidxN hvalidN
  have hvalidp : gammaValid fp p := gammaValid_mono fp hpN hvalidN
  have hhalfIdx : (idx : ℝ) * fp.u ≤ 1 / 2 := by
    have hcast : (idx : ℝ) ≤ N := by exact_mod_cast hidxN
    exact le_trans (mul_le_mul_of_nonneg_right hcast fp.u_nonneg) hhalfN
  have hhalfp : (p : ℝ) * fp.u ≤ 1 / 2 := by
    have hcast : (p : ℝ) ≤ N := by exact_mod_cast hpN
    exact le_trans (mul_le_mul_of_nonneg_right hcast fp.u_nonneg) hhalfN
  have hgammaPanel :
      theorem20_10_householder_gammaB fp r p 0 ≤
        2 * ((N : ℝ) * fp.u) := by
    calc
      theorem20_10_householder_gammaB fp r p 0
          ≤ 2 * ((idx : ℝ) * fp.u) := by
              simpa [idx, mul_assoc] using
                theorem20_10_householder_gammaB_le_linear_unit_roundoff_of_small
                  (r := r) (p := p) (q := 0) fp hhalfIdx
      _ ≤ 2 * ((N : ℝ) * fp.u) := by
              have hcast : (idx : ℝ) ≤ N := by exact_mod_cast hidxN
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hcast fp.u_nonneg) (by norm_num)
  have hgammap : gamma fp p ≤ 2 * ((N : ℝ) * fp.u) := by
    calc
      gamma fp p ≤ 2 * ((p : ℝ) * fp.u) :=
        gamma_le_two_mul_n_u_of_nu_le_half fp p hhalfp
      _ ≤ 2 * ((N : ℝ) * fp.u) := by
        have hcast : (p : ℝ) ≤ N := by exact_mod_cast hpN
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hcast fp.u_nonneg) (by norm_num)
  have hpanelNonneg :
      0 ≤ theorem20_10_householder_gammaB fp r p 0 := by
    simpa [theorem20_10_householder_gammaB] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalidIdx
  have hgammapNonneg : 0 ≤ gamma fp p := gamma_nonneg fp hvalidp
  have ht : 0 ≤ 2 * ((N : ℝ) * fp.u) := by
    exact mul_nonneg (by norm_num) (mul_nonneg (le_of_lt hN) fp.u_nonneg)
  have ht_one : 2 * ((N : ℝ) * fp.u) ≤ 1 := by nlinarith
  have hcomposed :
      theorem20_10_householder_composed_partA_gammaB fp r p 0 ≤
        6 * (N : ℝ) * fp.u := by
    dsimp [theorem20_10_householder_composed_partA_gammaB]
    nlinarith
  have hRankProduct :
      fp.u * ((6 : ℝ) * (N : ℝ) * (1 + frobNormRect B)) <
        fullConstraintSourceRankRadius hB hStack :=
    (lt_div_iff₀ hden).mp huRank
  refine ⟨by simpa [idx] using hvalidIdx, hvalidp, ?_⟩
  calc
    theorem20_10_householder_composed_partA_gammaB fp r p 0 *
          frobNormRect B
        ≤ (6 * (N : ℝ) * fp.u) * frobNormRect B :=
          mul_le_mul_of_nonneg_right hcomposed hnorm
    _ ≤ fp.u * ((6 : ℝ) * (N : ℝ) * (1 + frobNormRect B)) := by
          nlinarith [fp.u_nonneg, hN, hnorm]
    _ < fullConstraintSourceRankRadius hB hStack := hRankProduct

/-- The literal square constraint-only computation is the exact solution of
an LSE problem whose constraint matrix has the composed Householder-panel and
forward-substitution perturbation.  Nonbreakdown is derived from source full
row rank and the unit-roundoff threshold, rather than assumed for the rounded
triangular diagonal. -/
theorem computedX_fullConstraints_backward_error
    {r p : ℕ} (fp : FPModel)
    (A : Fin r → Fin p → ℝ) (B : Fin p → Fin p → ℝ)
    (b : Fin r → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu : fp.u < fullConstraintUnitRoundoffSmallnessThreshold hB hStack) :
    let gammaB := theorem20_10_householder_composed_partA_gammaB fp r p 0
    ∃ DeltaB : Fin p → Fin p → ℝ,
      frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
      LSEFullRowRank (fun i j => B i j + DeltaB i j) ∧
      LSEStackedFullColumnRank A (fun i j => B i j + DeltaB i j) ∧
      IsLSEMinimizer A b (fun i j => B i j + DeltaB i j) d
        (computedX_fullConstraints fp B d) := by
  dsimp
  let Q : Fin p → Fin p → ℝ :=
    fl_householderQRPanel_Q fp p p (finiteTranspose B)
  let S : Fin p → Fin p → ℝ := computedS_fullConstraints fp B
  let yhat : Fin p → ℝ := fl_forwardSub fp p S d
  let gamma0 := theorem20_10_householder_gammaB fp r p 0
  let gammaB := theorem20_10_householder_composed_partA_gammaB fp r p 0
  rcases fullConstraint_unit_roundoff_conditions_of_lt_smallnessThreshold
      fp hp hB hStack hu with
    ⟨hvalidPanel, hvalidp, hgammaBsmall⟩
  rcases theorem20_10_householder_B_transpose_perturbed_constraint_block
      (r := r) (p := p) (q := 0) fp B hp hvalidPanel with
    ⟨DeltaB0, _hDeltaBrep, hQraw, hSraw, hBQraw, hDeltaB0⟩
  let B0 : Fin p → Fin p → ℝ := fun i j => B i j + DeltaB0 i j
  have hQ : IsOrthogonal p Q := by
    simpa [Q] using hQraw
  have hS : IsLowerTriangular S := by
    simpa [S, computedS_fullConstraints] using hSraw
  have hBQ : matMulRectRight B0 Q = S := by
    have hBQ' : matMulRectRight B0 Q = gqrBQBlock (q := 0) S := by
      simpa [B0, Q, S, computedS_fullConstraints, matMulRectRight]
        using hBQraw
    exact hBQ'.trans (gqrBQBlock_zero_eq S)
  have hgamma0_nonneg : 0 ≤ gamma0 := by
    simpa [gamma0, theorem20_10_householder_gammaB] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalidPanel
  have hgammap_nonneg : 0 ≤ gamma fp p := gamma_nonneg fp hvalidp
  have hgamma0_le : gamma0 ≤ gammaB := by
    dsimp [gammaB, gamma0,
      theorem20_10_householder_composed_partA_gammaB]
    nlinarith
  have hDeltaB0_bound :
      frobNormRect DeltaB0 ≤ gamma0 * frobNormRect B := by
    simpa [gamma0] using hDeltaB0
  have hDeltaB0_small :
      frobNormRect DeltaB0 < hB.transposeVecNorm2LowerMargin := by
    calc
      frobNormRect DeltaB0 ≤ gamma0 * frobNormRect B := hDeltaB0_bound
      _ ≤ gammaB * frobNormRect B :=
        mul_le_mul_of_nonneg_right hgamma0_le (frobNormRect_nonneg B)
      _ < fullConstraintSourceRankRadius hB hStack := by
        simpa [gammaB] using hgammaBsmall
      _ ≤ hB.transposeVecNorm2LowerMargin := by
        exact min_le_left _ _
  have hDeltaB0TransposeFrob :
      frobNormRect (fun j : Fin p => fun i : Fin p => DeltaB0 i j) =
        frobNormRect DeltaB0 := by
    simpa [finiteTranspose] using frobNormRect_finiteTranspose DeltaB0
  have hDeltaB0Op :
      rectOpNorm2Le (fun j : Fin p => fun i : Fin p => DeltaB0 i j)
        (frobNormRect DeltaB0) := by
    apply rectOpNorm2Le_of_frobNormRect_le
    rw [hDeltaB0TransposeFrob]
  have hB0 : LSEFullRowRank B0 := by
    exact LSEFullRowRank.of_transpose_lower_bound_and_rectOpNorm2Le_lt
      (B := B) (DeltaB := DeltaB0)
      hB.transposeVecNorm2LowerMargin_lower_bound hDeltaB0Op hDeltaB0_small
  have hSinj : Function.Injective (rectMatMulVec S) := by
    intro x y hxy
    apply orthogonal_matMulVec_injective hQ
    apply hB0.square_rectMatMulVec_injective
    calc
      rectMatMulVec B0 (matMulVec p Q x) =
          rectMatMulVec (matMulRectRight B0 Q) x := by
            simpa [matMulRectRight] using
              (rectMatMulVec_rectMatMul B0 Q x).symm
      _ = rectMatMulVec S x := by rw [hBQ]
      _ = rectMatMulVec S y := hxy
      _ = rectMatMulVec (matMulRectRight B0 Q) y := by rw [hBQ]
      _ = rectMatMulVec B0 (matMulVec p Q y) := by
            simpa [matMulRectRight] using
              rectMatMulVec_rectMatMul B0 Q y
  have hSdiag : ∀ i : Fin p, S i i ≠ 0 :=
    rectMatMulVec_diag_ne_zero_of_lowerTriangular_injective hS hSinj
  rcases forwardSub_backward_error fp p S d hSdiag hS hvalidp with
    ⟨DeltaS, hDeltaSentry, hSeq⟩
  have hDeltaSfrob :
      frobNormRect DeltaS ≤ gamma fp p * frobNormRect S := by
    simpa [frobNormRect_eq_frobNormFn] using
      (frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le
        DeltaS S hgammap_nonneg hDeltaSentry)
  let Spert : Fin p → Fin p → ℝ := fun i j => S i j + DeltaS i j
  let Bpert : Fin p → Fin p → ℝ :=
    gqrSourceBFromBlocks (q := 0) Q Spert
  let DeltaB1 : Fin p → Fin p → ℝ := fun i j =>
    gqrSourceBFromBlocks (q := 0) Q Spert i j -
      gqrSourceBFromBlocks (q := 0) Q S i j
  let DeltaB : Fin p → Fin p → ℝ :=
    fun i j => DeltaB0 i j + DeltaB1 i j
  have hSourceB0 : gqrSourceBFromBlocks (q := 0) Q S = B0 :=
    gqrSourceBFromBlocks_eq_of_bq_eq (p := p) (q := 0) B0 Q S hQ
      (by simpa [gqrBQBlock_zero_eq] using hBQ)
  have hSnorm : frobNormRect S = frobNormRect B0 := by
    calc
      frobNormRect S = frobNormRect (gqrSourceBFromBlocks (q := 0) Q S) :=
        (frobNormRect_gqrSourceBFromBlocks (p := p) (q := 0) Q S hQ).symm
      _ = frobNormRect B0 := by rw [hSourceB0]
  have hB0norm :
      frobNormRect B0 ≤ (1 + gamma0) * frobNormRect B := by
    calc
      frobNormRect B0 ≤ frobNormRect B + frobNormRect DeltaB0 := by
        simpa [B0] using frobNormRect_add_le B DeltaB0
      _ ≤ frobNormRect B + gamma0 * frobNormRect B :=
        add_le_add_right hDeltaB0_bound _
      _ = (1 + gamma0) * frobNormRect B := by ring
  have hDeltaB1norm : frobNormRect DeltaB1 = frobNormRect DeltaS := by
    simpa [DeltaB1, Spert] using
      (gqrSourceBFromBlocks_perturbation_frobNorm_eq
        (q := 0) Q S DeltaS hQ)
  have hDeltaB1bound :
      frobNormRect DeltaB1 ≤
        gamma fp p * (1 + gamma0) * frobNormRect B := by
    calc
      frobNormRect DeltaB1 = frobNormRect DeltaS := hDeltaB1norm
      _ ≤ gamma fp p * frobNormRect S := hDeltaSfrob
      _ = gamma fp p * frobNormRect B0 := by rw [hSnorm]
      _ ≤ gamma fp p * ((1 + gamma0) * frobNormRect B) :=
        mul_le_mul_of_nonneg_left hB0norm hgammap_nonneg
      _ = gamma fp p * (1 + gamma0) * frobNormRect B := by ring
  have hDeltaBbound :
      frobNormRect DeltaB ≤ gammaB * frobNormRect B := by
    calc
      frobNormRect DeltaB ≤
          frobNormRect DeltaB0 + frobNormRect DeltaB1 := by
        simpa [DeltaB] using frobNormRect_add_le DeltaB0 DeltaB1
      _ ≤ gamma0 * frobNormRect B +
          gamma fp p * (1 + gamma0) * frobNormRect B :=
        add_le_add hDeltaB0_bound hDeltaB1bound
      _ = gammaB * frobNormRect B := by
        dsimp [gammaB, gamma0,
          theorem20_10_householder_composed_partA_gammaB]
        ring
  have hBpertEq : (fun i j => B i j + DeltaB i j) = Bpert := by
    ext i j
    change B i j +
        (DeltaB0 i j +
          (gqrSourceBFromBlocks (q := 0) Q Spert i j -
            gqrSourceBFromBlocks (q := 0) Q S i j)) =
      gqrSourceBFromBlocks (q := 0) Q Spert i j
    have hbase := congrFun (congrFun hSourceB0 i) j
    change gqrSourceBFromBlocks (q := 0) Q S i j =
      B i j + DeltaB0 i j at hbase
    rw [hbase]
    ring
  have hDeltaB_small :
      frobNormRect DeltaB < hB.transposeVecNorm2LowerMargin := by
    calc
      frobNormRect DeltaB ≤ gammaB * frobNormRect B := hDeltaBbound
      _ < fullConstraintSourceRankRadius hB hStack := by
        simpa [gammaB] using hgammaBsmall
      _ ≤ hB.transposeVecNorm2LowerMargin := min_le_left _ _
  have hDeltaBTransposeFrob :
      frobNormRect (fun j : Fin p => fun i : Fin p => DeltaB i j) =
        frobNormRect DeltaB := by
    simpa [finiteTranspose] using frobNormRect_finiteTranspose DeltaB
  have hDeltaBOp :
      rectOpNorm2Le (fun j : Fin p => fun i : Fin p => DeltaB i j)
        (frobNormRect DeltaB) := by
    apply rectOpNorm2Le_of_frobNormRect_le
    rw [hDeltaBTransposeFrob]
  have hBfinal : LSEFullRowRank (fun i j => B i j + DeltaB i j) :=
    LSEFullRowRank.of_transpose_lower_bound_and_rectOpNorm2Le_lt
      (B := B) (DeltaB := DeltaB)
      hB.transposeVecNorm2LowerMargin_lower_bound hDeltaBOp hDeltaB_small
  have hBQpert : matMulRectRight Bpert Q = Spert := by
    change matMulRectRight (gqrSourceBFromBlocks (q := 0) Q Spert) Q = Spert
    calc
      matMulRectRight (gqrSourceBFromBlocks (q := 0) Q Spert) Q =
          gqrBQBlock (q := 0) Spert :=
        gqrSourceBFromBlocks_mul_Q (p := p) (q := 0) Q Spert hQ
      _ = Spert := gqrBQBlock_zero_eq Spert
  have hSeqFn : rectMatMulVec Spert yhat = d := by
    ext i
    simpa [Spert, yhat, rectMatMulVec] using hSeq i
  have hfeasiblePert : LSEFeasible Bpert d (matMulVec p Q yhat) := by
    intro i
    calc
      rectMatMulVec Bpert (matMulVec p Q yhat) i =
          rectMatMulVec (matMulRectRight Bpert Q) yhat i := by
            simpa [matMulRectRight] using
              congrFun (rectMatMulVec_rectMatMul Bpert Q yhat).symm i
      _ = rectMatMulVec Spert yhat i := by rw [hBQpert]
      _ = d i := congrFun hSeqFn i
  have hfeasible :
      LSEFeasible (fun i j => B i j + DeltaB i j) d
        (computedX_fullConstraints fp B d) := by
    rw [hBpertEq]
    simpa [computedX_fullConstraints, Q, S, yhat] using hfeasiblePert
  refine ⟨DeltaB, hDeltaBbound, hBfinal,
    hBfinal.square_lseStackedFullColumnRank A, ?_⟩
  exact hBfinal.isLSEMinimizer_of_square_feasible A b d
    (computedX_fullConstraints fp B d) hfeasible

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), at the
source-permitted boundary `q = 0`, `p > 0`.

The literal rounded constraint solve is already the exact solution for the
composed constraint-matrix perturbation.  Hence the solution, `A`, and `b`
perturbations may all be zero. -/
theorem computedX_fullConstraints_partA_mixed_stability
    {r p : ℕ} (fp : FPModel)
    (A : Fin r → Fin p → ℝ) (B : Fin p → Fin p → ℝ)
    (b : Fin r → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu : fp.u < fullConstraintUnitRoundoffSmallnessThreshold hB hStack) :
    let xhat := computedX_fullConstraints fp B d
    let gammaA : ℝ := 0
    let gammaB := theorem20_10_householder_composed_partA_gammaB fp r p 0
    ∃ (DeltaA : Fin r → Fin p → ℝ)
      (DeltaB : Fin p → Fin p → ℝ)
      (Deltab : Fin r → ℝ)
      (DeltaX : Fin p → ℝ)
      (x : Fin p → ℝ),
      (∀ j, xhat j = x j + DeltaX j) ∧
      vecNorm2 DeltaX ≤ gammaB * vecNorm2 x ∧
      frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
      vecNorm2 Deltab ≤ gammaA * vecNorm2 b ∧
      frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
      IsLSEMinimizer
        (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i)
        (fun i j => B i j + DeltaB i j) d x := by
  dsimp
  rcases computedX_fullConstraints_backward_error
      fp A B b d hp hB hStack hu with
    ⟨DeltaB, hDeltaB, _hBpert, _hStackPert, hmin⟩
  rcases fullConstraint_unit_roundoff_conditions_of_lt_smallnessThreshold
      fp hp hB hStack hu with ⟨hvalidPanel, hvalidp, _hsmall⟩
  have hgamma0 :
      0 ≤ theorem20_10_householder_gammaB fp r p 0 := by
    simpa [theorem20_10_householder_gammaB] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalidPanel
  have hgammaB :
      0 ≤ theorem20_10_householder_composed_partA_gammaB fp r p 0 := by
    dsimp [theorem20_10_householder_composed_partA_gammaB]
    nlinarith [gamma_nonneg fp hvalidp]
  let DeltaA : Fin r → Fin p → ℝ := fun _ _ => 0
  let Deltab : Fin r → ℝ := fun _ => 0
  let DeltaX : Fin p → ℝ := fun _ => 0
  refine ⟨DeltaA, DeltaB, Deltab, DeltaX,
    computedX_fullConstraints fp B d, ?_, ?_, ?_, ?_, hDeltaB, ?_⟩
  · intro j
    simp [DeltaX]
  · simp [DeltaX, vecNorm2_zero]
    exact mul_nonneg hgammaB (vecNorm2_nonneg _)
  · simp [DeltaA, frobNormRect, frobNormSqRect]
  · simp [Deltab, vecNorm2_zero]
  · simpa [DeltaA, Deltab] using hmin

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b), at the
source-permitted boundary `q = 0`, `p > 0`.

The same literal vector is an exact solution after perturbing only `B`; the
inactive least-squares data and the constraint right-hand side need no
perturbation. -/
theorem computedX_fullConstraints_partB_backward_error
    {r p : ℕ} (fp : FPModel)
    (A : Fin r → Fin p → ℝ) (B : Fin p → Fin p → ℝ)
    (b : Fin r → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu : fp.u < fullConstraintUnitRoundoffSmallnessThreshold hB hStack) :
    let xhat := computedX_fullConstraints fp B d
    let gammaA : ℝ := 0
    let gammaB := theorem20_10_householder_composed_partA_gammaB fp r p 0
    ∃ (DeltaA : Fin r → Fin p → ℝ)
      (DeltaB : Fin p → Fin p → ℝ)
      (Deltab : Fin r → ℝ)
      (Deltad : Fin p → ℝ),
      frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
      frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
      vecNorm2 Deltab ≤
        gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
      vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
      IsLSEMinimizer
        (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i)
        (fun i j => B i j + DeltaB i j)
        (fun i => d i + Deltad i) xhat := by
  dsimp
  rcases computedX_fullConstraints_backward_error
      fp A B b d hp hB hStack hu with
    ⟨DeltaB, hDeltaB, _hBpert, _hStackPert, hmin⟩
  rcases fullConstraint_unit_roundoff_conditions_of_lt_smallnessThreshold
      fp hp hB hStack hu with ⟨hvalidPanel, hvalidp, _hsmall⟩
  have hgamma0 :
      0 ≤ theorem20_10_householder_gammaB fp r p 0 := by
    simpa [theorem20_10_householder_gammaB] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalidPanel
  have hgammaB :
      0 ≤ theorem20_10_householder_composed_partA_gammaB fp r p 0 := by
    dsimp [theorem20_10_householder_composed_partA_gammaB]
    nlinarith [gamma_nonneg fp hvalidp]
  let DeltaA : Fin r → Fin p → ℝ := fun _ _ => 0
  let Deltab : Fin r → ℝ := fun _ => 0
  let Deltad : Fin p → ℝ := fun _ => 0
  refine ⟨DeltaA, DeltaB, Deltab, Deltad, ?_, hDeltaB, ?_, ?_, ?_⟩
  · simp [DeltaA, frobNormRect, frobNormSqRect]
  · simp [Deltab, vecNorm2_zero]
    exact mul_nonneg (mul_nonneg hgammaB (frobNormRect_nonneg A))
      (vecNorm2_nonneg _)
  · simp [Deltad, vecNorm2_zero]
    exact mul_nonneg (mul_nonneg hgammaB (frobNormRect_nonneg B))
      (vecNorm2_nonneg _)
  · simpa [DeltaA, Deltab, Deltad] using hmin

end Theorem20_10

end NumStability
