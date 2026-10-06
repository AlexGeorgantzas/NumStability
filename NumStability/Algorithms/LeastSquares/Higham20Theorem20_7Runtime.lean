import NumStability.Algorithms.LeastSquares.Higham20Theorem20_7Contract

namespace NumStability

open scoped BigOperators

namespace Theorem20_7

/-!
# A literal-trace runtime envelope for Theorem 20.7

This file closes the Split 3B numerical interface for the actual stored,
column-pivoted QR and paired right-hand-side traces without a row-policy or
component-budget premise.  Its scales are finite sums of norms of the local
per-stage residuals that the execution itself produces, together with a
finite sum of final top-`R` column norms for the triangular-solve correction.

The resulting envelope is deliberately conservative.  It is a forward,
execution-derived exact-Real runtime certificate for the literal trace; it
does **not** claim the printed Cox--Higham compression of these scales to the
source-facing `alpha_i` and `beta_i` growth factors.
-/

/-- Sum of the Euclidean norms of every matrix-residual column created at one
literal QR stage. -/
noncomputable def pivotedStoredQRRuntimeMatrixStageScale
    (fp : FPModel) {m n : Nat} (hmn : n <= m)
    (A : Fin m -> Fin n -> Real) (k : Nat) : Real :=
  ∑ c : Fin n,
    vecNorm2 (fun r : Fin m => pivotedStoredQREseq fp hmn A k r c)

/-- Matrix-side runtime scale.  This is a finite sum of local stage residual
norms and does not inspect the accumulated perturbation. -/
noncomputable def pivotedStoredQRRuntimeMatrixScale
    (fp : FPModel) {m n : Nat} (hmn : n <= m)
    (A : Fin m -> Fin n -> Real) : Real :=
  ∑ k ∈ Finset.range n,
    pivotedStoredQRRuntimeMatrixStageScale fp hmn A k

/-- RHS-side runtime scale, again formed only from the individual residual of
each executed common-reflector update. -/
noncomputable def pivotedStoredQRRuntimeRhsScale
    (fp : FPModel) {m n : Nat} (hmn : n <= m)
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real) : Real :=
  ∑ k ∈ Finset.range n,
    vecNorm2 (pivotedStoredQRRhsEseq fp hmn A b k)

/-- Forward scale for transporting a componentwise triangular perturbation.
It is the sum of the Euclidean norms of the embedded columns of the literal
final top block `R`. -/
noncomputable def pivotedStoredQRRuntimeTopRScale
    (fp : FPModel) {m n : Nat} (hmn : n <= m)
    (A : Fin m -> Fin n -> Real) : Real :=
  ∑ c : Fin n,
    vecNorm2 (fun r : Fin m =>
      rectTopBlock (m := m) (pivotedStoredQRTopR fp hmn A) r c)

/-- Common matrix scale used by the numerical contract.  It covers both the
literal QR residual and the pulled-back triangular correction. -/
noncomputable def pivotedStoredQRRuntimeAlpha
    (fp : FPModel) {m n : Nat} (hmn : n <= m)
    (A : Fin m -> Fin n -> Real) : Fin m -> Real :=
  fun _ =>
    pivotedStoredQRRuntimeMatrixScale fp hmn A +
      pivotedStoredQRRuntimeTopRScale fp hmn A

/-- Common RHS scale used by the numerical contract. -/
noncomputable def pivotedStoredQRRuntimeBeta
    (fp : FPModel) {m n : Nat} (hmn : n <= m)
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real) : Fin m -> Real :=
  fun _ => pivotedStoredQRRuntimeRhsScale fp hmn A b

theorem pivotedStoredQRRuntimeMatrixStageScale_nonneg
    (fp : FPModel) {m n : Nat} (hmn : n <= m)
    (A : Fin m -> Fin n -> Real) (k : Nat) :
    0 <= pivotedStoredQRRuntimeMatrixStageScale fp hmn A k := by
  apply Finset.sum_nonneg
  intro c _hc
  exact vecNorm2_nonneg _

theorem pivotedStoredQRRuntimeMatrixScale_nonneg
    (fp : FPModel) {m n : Nat} (hmn : n <= m)
    (A : Fin m -> Fin n -> Real) :
    0 <= pivotedStoredQRRuntimeMatrixScale fp hmn A := by
  apply Finset.sum_nonneg
  intro k _hk
  exact pivotedStoredQRRuntimeMatrixStageScale_nonneg fp hmn A k

theorem pivotedStoredQRRuntimeRhsScale_nonneg
    (fp : FPModel) {m n : Nat} (hmn : n <= m)
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real) :
    0 <= pivotedStoredQRRuntimeRhsScale fp hmn A b := by
  apply Finset.sum_nonneg
  intro k _hk
  exact vecNorm2_nonneg _

theorem pivotedStoredQRRuntimeTopRScale_nonneg
    (fp : FPModel) {m n : Nat} (hmn : n <= m)
    (A : Fin m -> Fin n -> Real) :
    0 <= pivotedStoredQRRuntimeTopRScale fp hmn A := by
  apply Finset.sum_nonneg
  intro c _hc
  exact vecNorm2_nonneg _

theorem pivotedStoredQRRuntimeAlpha_nonneg
    (fp : FPModel) {m n : Nat} (hmn : n <= m)
    (A : Fin m -> Fin n -> Real) (i : Fin m) :
    0 <= pivotedStoredQRRuntimeAlpha fp hmn A i := by
  exact add_nonneg
    (pivotedStoredQRRuntimeMatrixScale_nonneg fp hmn A)
    (pivotedStoredQRRuntimeTopRScale_nonneg fp hmn A)

theorem pivotedStoredQRRuntimeBeta_nonneg
    (fp : FPModel) {m n : Nat} (hmn : n <= m)
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real) (i : Fin m) :
    0 <= pivotedStoredQRRuntimeBeta fp hmn A b i :=
  pivotedStoredQRRuntimeRhsScale_nonneg fp hmn A b

/-- Orthogonality turns a local residual-column norm into a bound on every
coordinate of its transported stage image. -/
theorem pivotedStoredQR_runtime_stageImage_entrywise_le
    (fp : FPModel) {m n : Nat} (hmn : n <= m)
    (A : Fin m -> Fin n -> Real) (k : Nat) (i : Fin m) (j : Fin n) :
    |matMulRect m m n
        (Wave19.Qacc (pivotedStoredQRPseq fp hmn A) (k + 1))
        (pivotedStoredQREseq fp hmn A k) i j| <=
      pivotedStoredQRRuntimeMatrixStageScale fp hmn A k := by
  have hQ : IsOrthogonal m
      (Wave19.Qacc (pivotedStoredQRPseq fp hmn A) (k + 1)) :=
    Wave19.Qacc_orthogonal _
      (fun q => pivotedStoredQRPseq_orthogonal fp hmn A q) (k + 1)
  have hcoord := hQ.abs_matMulVec_le_vecNorm2
    (fun r : Fin m => pivotedStoredQREseq fp hmn A k r j) i
  have hcol :
      vecNorm2 (fun r : Fin m => pivotedStoredQREseq fp hmn A k r j) <=
        pivotedStoredQRRuntimeMatrixStageScale fp hmn A k := by
    simpa [pivotedStoredQRRuntimeMatrixStageScale] using
      (Finset.single_le_sum
      (fun c _hc => vecNorm2_nonneg
        (fun r : Fin m => pivotedStoredQREseq fp hmn A k r c))
      (Finset.mem_univ j))
  have hcoord' :
      |matMulRect m m n
          (Wave19.Qacc (pivotedStoredQRPseq fp hmn A) (k + 1))
          (pivotedStoredQREseq fp hmn A k) i j| <=
        vecNorm2 (fun r : Fin m => pivotedStoredQREseq fp hmn A k r j) := by
    simpa [matMulRect, matMulVec] using hcoord
  exact hcoord'.trans hcol

/-- The literal matrix perturbation accumulator is bounded by the finite sum
of local matrix residual norms. -/
theorem pivotedStoredQR_pivotDAacc_runtime_bound
    (fp : FPModel) {m n : Nat} (hmn : n <= m)
    (A : Fin m -> Fin n -> Real) (i : Fin m) (j : Fin n) :
    |pivotDAacc (pivotedStoredQRPseq fp hmn A)
        (pivotedStoredQRSwapSeq fp hmn A)
        (pivotedStoredQREseq fp hmn A) n i j| <=
      pivotedStoredQRRuntimeMatrixScale fp hmn A := by
  have hacc := pivotDAacc_final_entrywise_bound
    (pivotedStoredQRPseq fp hmn A)
    (pivotedStoredQRSwapSeq fp hmn A)
    (pivotedStoredQREseq fp hmn A)
    (fun k (_r : Fin m) =>
      pivotedStoredQRRuntimeMatrixStageScale fp hmn A k)
    (fun k c hc => pivotedStoredQRSwapSeq_fix_prefix fp hmn A k c hc)
    (fun k c hc => pivotedStoredQRSwapSeq_maps_active fp hmn A k c hc)
    (fun k r c hc =>
      pivotedStoredQR_QaccE_completed_column_zero fp hmn A k r c hc)
    (fun k r c =>
      pivotedStoredQR_runtime_stageImage_entrywise_le fp hmn A k r c)
    i j
  have hsubset : Finset.range (j.val + 1) ⊆ Finset.range n :=
    Finset.range_mono (Nat.succ_le_iff.mpr j.isLt)
  have hsum :
      (∑ k ∈ Finset.range (j.val + 1),
        pivotedStoredQRRuntimeMatrixStageScale fp hmn A k) <=
      pivotedStoredQRRuntimeMatrixScale fp hmn A := by
    simpa [pivotedStoredQRRuntimeMatrixScale] using
      (Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun k _hkn _hkp =>
          pivotedStoredQRRuntimeMatrixStageScale_nonneg fp hmn A k))
  exact hacc.trans hsum

/-- The one-column telescope gives an analogous local-residual runtime bound
for the paired right-hand side. -/
theorem pivotedStoredQRRhsDelta_runtime_bound
    (fp : FPModel) {m n : Nat} (hmn : n <= m)
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real) (i : Fin m) :
    |pivotedStoredQRRhsDelta fp hmn A b i| <=
      pivotedStoredQRRuntimeRhsScale fp hmn A b := by
  have hacc := Wave19.entrywise_residual_telescope_bound n
    (pivotedStoredQRPseq fp hmn A)
    (pivotedStoredQRRhsEMatrixSeq fp hmn A b)
    (fun k (_r : Fin m) =>
      vecNorm2 (pivotedStoredQRRhsEseq fp hmn A b k))
    (fun k _hk r (_c : Fin 1) => by
      have hQ : IsOrthogonal m
          (Wave19.Qacc (pivotedStoredQRPseq fp hmn A) (k + 1)) :=
        Wave19.Qacc_orthogonal _
          (fun q => pivotedStoredQRPseq_orthogonal fp hmn A q) (k + 1)
      have hcoord := hQ.abs_matMulVec_le_vecNorm2
        (pivotedStoredQRRhsEseq fp hmn A b k) r
      simpa [pivotedStoredQRRhsEMatrixSeq, matMulRect, matMulVec] using hcoord)
    i (0 : Fin 1)
  simpa [pivotedStoredQRRhsDelta, pivotedStoredQRRuntimeRhsScale] using hacc

/-- Each embedded final-`R` column norm is below the finite top-`R` runtime
scale. -/
theorem pivotedStoredQR_topR_column_le_runtimeTopRScale
    (fp : FPModel) {m n : Nat} (hmn : n <= m)
    (A : Fin m -> Fin n -> Real) (j : Fin n) :
    vecNorm2 (fun r : Fin m =>
        rectTopBlock (m := m) (pivotedStoredQRTopR fp hmn A) r j) <=
      pivotedStoredQRRuntimeTopRScale fp hmn A := by
  simpa [pivotedStoredQRRuntimeTopRScale] using
    (Finset.single_le_sum
    (fun c _hc => vecNorm2_nonneg (fun r : Fin m =>
      rectTopBlock (m := m) (pivotedStoredQRTopR fp hmn A) r c))
    (Finset.mem_univ j))

/-- Any triangular perturbation allowed by floating-point back substitution
is transported componentwise within `gamma_n` times the forward top-`R`
runtime scale. -/
theorem pivotedStoredQR_QdR_runtime_bound
    (fp : FPModel) {m n : Nat} (hmn : n <= m)
    (A : Fin m -> Fin n -> Real) (hgamma : gammaValid fp n)
    (dR : Fin n -> Fin n -> Real)
    (hdR : forall i j,
      |dR i j| <= gamma fp n * |pivotedStoredQRTopR fp hmn A i j|)
    (i : Fin m) (j : Fin n) :
    |matMulRect m m n
        (Wave19.Qacc (pivotedStoredQRPseq fp hmn A) n)
        (rectTopBlock (m := m) dR) i j| <=
      gamma fp n * pivotedStoredQRRuntimeTopRScale fp hmn A := by
  have hQ : IsOrthogonal m
      (Wave19.Qacc (pivotedStoredQRPseq fp hmn A) n) :=
    Wave19.Qacc_orthogonal _
      (fun q => pivotedStoredQRPseq_orthogonal fp hmn A q) n
  have hcoord := hQ.abs_matMulVec_le_vecNorm2
    (fun r : Fin m => rectTopBlock (m := m) dR r j) i
  have hpert := rectTopBlock_col_vecNorm2_perturb_bound_of_gamma
    (m := m) (n := n) fp (pivotedStoredQRTopR fp hmn A) dR
      hgamma hdR j
  have hcol := pivotedStoredQR_topR_column_le_runtimeTopRScale
    fp hmn A j
  have hgamma0 : 0 <= gamma fp n := gamma_nonneg fp hgamma
  calc
    |matMulRect m m n
        (Wave19.Qacc (pivotedStoredQRPseq fp hmn A) n)
        (rectTopBlock (m := m) dR) i j| <=
        vecNorm2 (fun r : Fin m => rectTopBlock (m := m) dR r j) := by
          simpa [matMulRect, matMulVec] using hcoord
    _ <= gamma fp n *
        vecNorm2 (fun r : Fin m =>
          rectTopBlock (m := m) (pivotedStoredQRTopR fp hmn A) r j) := hpert
    _ <= gamma fp n * pivotedStoredQRRuntimeTopRScale fp hmn A :=
      mul_le_mul_of_nonneg_left hcol hgamma0

theorem one_le_natCast_sq_of_pos {n : Nat} (hn : 0 < n) :
    (1 : Real) <= (n : Real) ^ 2 := by
  have hn1 : (1 : Real) <= (n : Real) := by exact_mod_cast hn
  nlinarith

/-- Fully instantiated Split 3B contract for the literal execution.

No field is imported as a row-policy, component budget, accumulated-error
premise, or desired backward conclusion.  All three bounds are derived from
the local runtime scales above. -/
noncomputable def pivotedStoredQR_split3B_numericalContract_runtime
    (fp : FPModel) {m n : Nat} (hn : 0 < n) (hmn : n <= m)
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (hgamma : gammaValid fp n) :
    PivotedStoredQRSplit3BNumericalContract fp hmn A b
      (pivotedStoredQRRuntimeAlpha fp hmn A)
      (pivotedStoredQRRuntimeBeta fp hmn A b)
      1 1 (gamma fp n) := by
  have hnSq : (1 : Real) <= (n : Real) ^ 2 :=
    one_le_natCast_sq_of_pos hn
  have hgamma0 : 0 <= gamma fp n := gamma_nonneg fp hgamma
  refine
    { alpha_nonneg := pivotedStoredQRRuntimeAlpha_nonneg fp hmn A
      betaScale_nonneg := pivotedStoredQRRuntimeBeta_nonneg fp hmn A b
      qrCoeff_nonneg := by norm_num
      rhsCoeff_nonneg := by norm_num
      backSubCoeff_nonneg := hgamma0
      qr_accumulated_pivot_row := ?_
      rhs_accumulated_source_row := ?_
      backSub_transport_source_row := ?_ }
  · intro i j
    have hacc := pivotedStoredQR_pivotDAacc_runtime_bound fp hmn A i j
    have hmatrix :
        pivotedStoredQRRuntimeMatrixScale fp hmn A <=
          pivotedStoredQRRuntimeAlpha fp hmn A i := by
      exact le_add_of_nonneg_right
        (pivotedStoredQRRuntimeTopRScale_nonneg fp hmn A)
    have hj0 : (0 : Real) <= (j.val : Real) := Nat.cast_nonneg _
    have hjfactor : (1 : Real) <= ((j.val : Real) + 1) ^ 2 := by
      nlinarith
    have halpha := pivotedStoredQRRuntimeAlpha_nonneg fp hmn A i
    calc
      |pivotDAacc (pivotedStoredQRPseq fp hmn A)
          (pivotedStoredQRSwapSeq fp hmn A)
          (pivotedStoredQREseq fp hmn A) n i j| <=
          pivotedStoredQRRuntimeMatrixScale fp hmn A := hacc
      _ <= pivotedStoredQRRuntimeAlpha fp hmn A i := hmatrix
      _ = 1 * pivotedStoredQRRuntimeAlpha fp hmn A i := by ring
      _ <= ((j.val : Real) + 1) ^ 2 *
          pivotedStoredQRRuntimeAlpha fp hmn A i :=
        mul_le_mul_of_nonneg_right hjfactor halpha
      _ = ((j.val : Real) + 1) ^ 2 * 1 *
          pivotedStoredQRRuntimeAlpha fp hmn A i := by ring
  · intro i
    have hacc := pivotedStoredQRRhsDelta_runtime_bound fp hmn A b i
    have hbeta := pivotedStoredQRRuntimeBeta_nonneg fp hmn A b i
    calc
      |pivotedStoredQRRhsDelta fp hmn A b i| <=
          pivotedStoredQRRuntimeBeta fp hmn A b i := hacc
      _ = 1 * pivotedStoredQRRuntimeBeta fp hmn A b i := by ring
      _ <= (n : Real) ^ 2 *
          pivotedStoredQRRuntimeBeta fp hmn A b i :=
        mul_le_mul_of_nonneg_right hnSq hbeta
      _ = (n : Real) ^ 2 * 1 *
          pivotedStoredQRRuntimeBeta fp hmn A b i := by ring
  · intro dR hdR i j
    let pi := pivotPermAcc (pivotedStoredQRSwapSeq fp hmn A) n
    have htransport := pivotedStoredQR_QdR_runtime_bound fp hmn A hgamma
      dR hdR i (pi.symm j)
    have htop :
        pivotedStoredQRRuntimeTopRScale fp hmn A <=
          pivotedStoredQRRuntimeAlpha fp hmn A i := by
      exact le_add_of_nonneg_left
        (pivotedStoredQRRuntimeMatrixScale_nonneg fp hmn A)
    have hga : 0 <= gamma fp n *
        pivotedStoredQRRuntimeAlpha fp hmn A i :=
      mul_nonneg hgamma0
        (pivotedStoredQRRuntimeAlpha_nonneg fp hmn A i)
    calc
      |matMulRect m m n
          (Wave19.Qacc (pivotedStoredQRPseq fp hmn A) n)
          (rectTopBlock (m := m) dR) i (pi.symm j)| <=
          gamma fp n * pivotedStoredQRRuntimeTopRScale fp hmn A := by
            simpa [pi] using htransport
      _ <= gamma fp n * pivotedStoredQRRuntimeAlpha fp hmn A i :=
        mul_le_mul_of_nonneg_left htop hgamma0
      _ = 1 * (gamma fp n * pivotedStoredQRRuntimeAlpha fp hmn A i) := by ring
      _ <= (n : Real) ^ 2 *
          (gamma fp n * pivotedStoredQRRuntimeAlpha fp hmn A i) :=
        mul_le_mul_of_nonneg_right hnSq hga
      _ = (n : Real) ^ 2 * gamma fp n *
          pivotedStoredQRRuntimeAlpha fp hmn A i := by ring

/-- Direct exact-minimizer endpoint for the literal pivoted stored-QR, paired
RHS, and back-substitution execution under the conservative runtime envelope.
The theorem has no numerical-contract, row-policy, component-budget, or final
perturbation hypothesis. -/
theorem fl_pivotedStoredQR_returnedX_exactMinimizer_of_runtime
    (fp : FPModel) {m n : Nat} (hn : 0 < n) (hmn : n <= m)
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (hdiag : forall i : Fin n, pivotedStoredQRTopR fp hmn A i i ≠ 0)
    (hgamma : gammaValid fp n) :
    exists dR : Fin n -> Fin n -> Real,
      (forall i j,
        |dR i j| <= gamma fp n * |pivotedStoredQRTopR fp hmn A i j|) /\
      IsLeastSquaresMinimizer
        (fun i j => A i j +
          pivotedStoredQRBackSubSourceDelta fp hmn A dR i j)
        (fun i => b i + pivotedStoredQRRhsDelta fp hmn A b i)
        (pivotedStoredQRReturnedX fp hmn A b) /\
      (forall i j,
        |pivotedStoredQRBackSubSourceDelta fp hmn A dR i j| <=
          (n : Real) ^ 2 * (1 + gamma fp n) *
            pivotedStoredQRRuntimeAlpha fp hmn A i) /\
      forall i,
        |pivotedStoredQRRhsDelta fp hmn A b i| <=
          (n : Real) ^ 2 * pivotedStoredQRRuntimeBeta fp hmn A b i := by
  have h := fl_pivotedStoredQR_returnedX_exactMinimizer_of_split3B
    fp hmn A b
      (pivotedStoredQRRuntimeAlpha fp hmn A)
      (pivotedStoredQRRuntimeBeta fp hmn A b)
      1 1 (gamma fp n)
      (pivotedStoredQR_split3B_numericalContract_runtime
        fp hn hmn A b hgamma)
      hdiag hgamma
  simpa using h

end Theorem20_7

end NumStability
