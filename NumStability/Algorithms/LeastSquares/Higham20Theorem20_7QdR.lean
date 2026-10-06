import NumStability.Algorithms.LeastSquares.Higham20Theorem20_7

namespace NumStability

open scoped BigOperators

namespace Theorem20_7

/-!
# Theorem 20.7: the pulled-back triangular correction

This file isolates the `Q [dR;0]` term created by rounded back substitution.
The useful telescope is the orientation used in Cox--Higham (3.7): each
Householder multiplier is formed against the original correction column and
the corresponding raw vector is then transported through the preceding
reflectors.  This avoids the generally false estimate comparing the norm of
the whole triangular correction column with every later pivot scale.
-/

/-- Rank-one vector subtracted by one raw Householder reflector. -/
noncomputable def rawHouseholderDirectTerm {m : ℕ}
    (v : ℕ → Fin m → ℝ) (β : ℕ → ℝ) (f : Fin m → ℝ)
    (k : ℕ) : Fin m → ℝ :=
  fun r => β k * (∑ s : Fin m, v k s * f s) * v k r

/-- Ordered matrix products are linear in their vector argument. -/
theorem applyProd_sub {m : ℕ} (P : ℕ → Fin m → Fin m → ℝ)
    (a len : ℕ) (f g : Fin m → ℝ) :
    Wave19.applyProd P a len (fun r => f r - g r) =
      fun r => Wave19.applyProd P a len f r -
        Wave19.applyProd P a len g r := by
  induction len generalizing a f g with
  | zero => simp [Wave19.applyProd]
  | succ len ih =>
      simp only [Wave19.applyProd]
      rw [ih]
      funext i
      simp only [matMulVec, mul_sub, Finset.sum_sub_distrib]

/-- Ordered matrix products commute with scalar multiplication. -/
theorem applyProd_smul {m : ℕ} (P : ℕ → Fin m → Fin m → ℝ)
    (a len : ℕ) (c : ℝ) (f : Fin m → ℝ) :
    Wave19.applyProd P a len (fun r => c * f r) =
      fun r => c * Wave19.applyProd P a len f r := by
  induction len generalizing a f with
  | zero => simp [Wave19.applyProd]
  | succ len ih =>
      simp only [Wave19.applyProd]
      rw [ih]
      funext i
      simp only [matMulVec, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring

/-- Transporting a direct Householder term transports only its raw vector;
the scalar multiplier remains outside the prefix product. -/
theorem applyProd_rawHouseholderDirectTerm {m : ℕ}
    (v : ℕ → Fin m → ℝ) (β : ℕ → ℝ) (f : Fin m → ℝ)
    (k : ℕ) (r : Fin m) :
    Wave19.applyProd (fun q => householder m (v q) (β q)) 0 k
        (rawHouseholderDirectTerm v β f k) r =
      (β k * (∑ s : Fin m, v k s * f s)) *
        Wave19.applyProd (fun q => householder m (v q) (β q)) 0 k (v k) r := by
  have h := applyProd_smul
    (fun q => householder m (v q) (β q)) 0 k
    (β k * (∑ s : Fin m, v k s * f s)) (v k)
  simpa [rawHouseholderDirectTerm] using congrFun h r

/-- Cox--Higham (3.7), in the prefix-transport orientation.

`applyProd P 0 len f` equals `f` minus the sum of the direct rank-one
Householder corrections, with the correction created at stage `k` transported
through stages `0,...,k-1`. -/
theorem applyProd_rawHouseholder_direct_expansion {m : ℕ}
    (v : ℕ → Fin m → ℝ) (β : ℕ → ℝ) (f : Fin m → ℝ)
    (len : ℕ) (r : Fin m) :
    Wave19.applyProd (fun k => householder m (v k) (β k)) 0 len f r =
      f r - ∑ k ∈ Finset.range len,
        Wave19.applyProd (fun q => householder m (v q) (β q)) 0 k
          (rawHouseholderDirectTerm v β f k) r := by
  induction len with
  | zero => simp [Wave19.applyProd]
  | succ len ih =>
      rw [applyProd_snoc]
      let P : ℕ → Fin m → Fin m → ℝ :=
        fun k => householder m (v k) (β k)
      let t := rawHouseholderDirectTerm v β f len
      have hPf : matMulVec m (P len) f = fun r => f r - t r := by
        funext i
        simp only [P, householder_matMulVec_eq]
        simp [t, rawHouseholderDirectTerm]
        ring
      simp only [Nat.zero_add]
      change Wave19.applyProd P 0 len (matMulVec m (P len) f) r = _
      rw [hPf, applyProd_sub]
      rw [show (fun k => householder m (v k) (β k)) = P by rfl] at ih
      change Wave19.applyProd P 0 len f r - Wave19.applyProd P 0 len t r =
        f r - ∑ k ∈ Finset.range (len + 1),
          Wave19.applyProd P 0 k (rawHouseholderDirectTerm v β f k) r
      rw [ih]
      simp only [Finset.sum_range_succ]
      simp [P, t]
      ring

/-- Two-scale Cox--Higham transport bound.

The executed reflector rows are controlled by `reflectorScale`, while the
local residual and the final transported result are controlled by the
independent `residualScale`.  The mixed premise is precisely what the
rank-one term needs:
`reflectorScale l * (‖f‖₂ / ‖v_k‖₂) ≤ gammaTilde * residualScale l`.
This avoids the generally false requirement that the reflector vector itself
be bounded by an RHS-derived scale. -/
theorem applyProd_rawHouseholder_entrywise_le_two_scales {m : ℕ}
    (v : ℕ → Fin m → ℝ) (β : ℕ → ℝ) (f : Fin m → ℝ)
    (reflectorScale residualScale : Fin m → ℝ)
    (gammaTilde : ℝ) (i : ℕ) (l : Fin m)
    (hgammaTilde : 0 ≤ gammaTilde)
    (hreflectorScale : ∀ r, 0 ≤ reflectorScale r)
    (hresidualScale : ∀ r, 0 ≤ residualScale r)
    (horth : ∀ k, IsOrthogonal m (householder m (v k) (β k)))
    (hvpos : ∀ k < i, 0 < vecNorm2 (v k))
    (hbeta : ∀ k < i, β k * vecNorm2 (v k) ^ 2 = 2)
    (hvrow : ∀ k < i, ∀ r, |v k r| ≤ 2 * reflectorScale r)
    (htransport : ∀ k < i,
      reflectorScale l * (vecNorm2 f / vecNorm2 (v k)) ≤
        gammaTilde * residualScale l)
    (hfrow : |f l| ≤ gammaTilde * residualScale l) :
    |Wave19.applyProd (fun t => householder m (v t) (β t)) 0 i f l| ≤
      (1 + 4 * (i : ℝ)) * gammaTilde * residualScale l := by
  let P : ℕ → Fin m → Fin m → ℝ :=
    fun t => householder m (v t) (β t)
  let zterm : ℕ → Fin m → ℝ := rawHouseholderZTerm v β f i
  apply Wave19.y_i_entrywise_bound
    (Wave19.applyProd P 0 i f) f zterm gammaTilde (residualScale l) i l
    hgammaTilde (hresidualScale l)
  · simpa [P, zterm] using
      applyProd_rawHouseholder_coordinate_expansion v β f i l
  · exact hfrow
  · intro k hk
    have hki : k < i := Finset.mem_range.mp hk
    let wk : Fin m → ℝ :=
      Wave19.applyProd P (k + 1) (i - (k + 1)) f
    have hwknorm : vecNorm2 wk = vecNorm2 f := by
      exact Wave19.vecNorm2_applyProd P horth (k + 1)
        (i - (k + 1)) f
    have hrank := Wave19.zk_rankOne_entrywise_le
      (v k) wk (reflectorScale l) l (hvpos k hki)
        (hreflectorScale l) (hvrow k hki l)
    have hmixed : reflectorScale l *
        (vecNorm2 wk / vecNorm2 (v k)) ≤
          gammaTilde * residualScale l := by
      rw [hwknorm]
      exact htransport k hki
    have hbound :
        |(2 / vecNorm2 (v k) ^ 2) * v k l *
            (∑ s : Fin m, v k s * wk s)| ≤
          4 * gammaTilde * residualScale l := by
      calc
        |(2 / vecNorm2 (v k) ^ 2) * v k l *
            (∑ s : Fin m, v k s * wk s)| ≤
            4 * reflectorScale l *
              (vecNorm2 wk / vecNorm2 (v k)) := hrank
        _ = 4 * (reflectorScale l *
              (vecNorm2 wk / vecNorm2 (v k))) := by ring
        _ ≤ 4 * (gammaTilde * residualScale l) :=
          mul_le_mul_of_nonneg_left hmixed (by norm_num)
        _ = 4 * gammaTilde * residualScale l := by ring
    have hvsq_ne : vecNorm2 (v k) ^ 2 ≠ 0 :=
      ne_of_gt (sq_pos_of_pos (hvpos k hki))
    have hcoef : β k = 2 / vecNorm2 (v k) ^ 2 :=
      (eq_div_iff hvsq_ne).2 (hbeta k hki)
    simpa [zterm, rawHouseholderZTerm, P, wk, hcoef] using hbound

/-- Scaled form of the Cox--Higham multiplier estimate.

The usual lemma has `‖w‖₂ ≤ |sigma|` and conclusion `≤ sqrt 2`.  A triangular
correction column has instead `‖w‖₂ ≤ eta |sigma|`; keeping the scale outside
gives the form needed below. -/
theorem householder_multiplier_le_sqrt_two_mul {m : ℕ}
    (v w : Fin m → ℝ) (sigma beta eta : ℝ)
    (hsigma : 0 < |sigma|) (heta : 0 ≤ eta)
    (hvnorm : Real.sqrt 2 * |sigma| ≤ vecNorm2 v)
    (hw : vecNorm2 w ≤ eta * |sigma|)
    (hbeta : beta * vecNorm2 v ^ 2 = 2) :
    |beta * (∑ i : Fin m, v i * w i)| ≤ Real.sqrt 2 * eta := by
  have hsqrt_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hvpos : 0 < vecNorm2 v := by
    have : 0 < Real.sqrt 2 * |sigma| := mul_pos hsqrt_pos hsigma
    linarith
  have hvsq_pos : 0 < vecNorm2 v ^ 2 := by positivity
  have hbeta_val : beta = 2 / vecNorm2 v ^ 2 := by
    apply (eq_div_iff (ne_of_gt hvsq_pos)).2
    simpa [mul_comm] using hbeta
  have hbeta_nonneg : 0 ≤ beta := by
    rw [hbeta_val]
    positivity
  have hcs : |∑ i : Fin m, v i * w i| ≤ vecNorm2 v * vecNorm2 w :=
    abs_vecInnerProduct_le_vecNorm2_mul v w
  have hstep :
      |beta * (∑ i : Fin m, v i * w i)| ≤
        beta * (vecNorm2 v * vecNorm2 w) := by
    rw [abs_mul, abs_of_nonneg hbeta_nonneg]
    exact mul_le_mul_of_nonneg_left hcs hbeta_nonneg
  have heq : beta * (vecNorm2 v * vecNorm2 w) =
      2 * vecNorm2 w / vecNorm2 v := by
    rw [hbeta_val]
    field_simp [ne_of_gt hvpos]
  have hsqrt_sq : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num)
  have hkey : 2 * vecNorm2 w ≤
      (Real.sqrt 2 * eta) * vecNorm2 v := by
    have h1 :
        (Real.sqrt 2 * eta) * (Real.sqrt 2 * |sigma|) ≤
          (Real.sqrt 2 * eta) * vecNorm2 v :=
      mul_le_mul_of_nonneg_left hvnorm
        (mul_nonneg (Real.sqrt_nonneg _) heta)
    have h2 :
        (Real.sqrt 2 * eta) * (Real.sqrt 2 * |sigma|) =
          2 * (eta * |sigma|) := by
      rw [show (Real.sqrt 2 * eta) * (Real.sqrt 2 * |sigma|) =
          (Real.sqrt 2 * Real.sqrt 2) * (eta * |sigma|) by ring,
        hsqrt_sq]
    have h3 : 2 * vecNorm2 w ≤ 2 * (eta * |sigma|) := by linarith
    linarith
  have hfrac : 2 * vecNorm2 w / vecNorm2 v ≤ Real.sqrt 2 * eta := by
    rw [div_le_iff₀ hvpos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hkey
  exact hstep.trans (heq ▸ hfrac)

/-- Minimal executed-reflector row data used by the triangular-correction
argument.  In particular this interface has no cross-stage pivot ordering and
does not inherit the strict-history field refuted for the rounded trace. -/
structure PivotedStoredQRQdRReflectorReady (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (alpha : Fin m → ℝ) : Prop where
  alpha_nonneg : ∀ i, 0 ≤ alpha i
  sigma_pos : ∀ k, k < n → 0 < |pivotedStoredQRSigma fp hmn A k|
  vector_row : ∀ k, k < n → ∀ i,
    |pivotedStoredQRRawVector fp hmn A k i| ≤ 2 * alpha i

/-- The legacy raw-ready bundle projects to the strictly smaller reflector-row
interface.  Positive QdR results below depend only on this projection. -/
theorem PivotedStoredQRRawReady.toQdRReflectorReady
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (alpha : Fin m → ℝ)
    (gammaTilde : ℝ) (errorCoeff : ℕ → ℝ)
    (ready : PivotedStoredQRRawReady fp hmn A alpha gammaTilde errorCoeff) :
    PivotedStoredQRQdRReflectorReady fp hmn A alpha :=
  { alpha_nonneg := ready.alpha_nonneg
    sigma_pos := ready.sigma_pos
    vector_row := ready.vector_row }

/-- Local numerical data needed by the (3.7)--(3.11) triangular-correction
argument.

The two correction fields are the precise row-scale obligations: an entrywise
row bound and an active-tail norm bound at each reflector.  `raw_ratio` is the
independent reflector-history input used only to transport the raw vector
through earlier reflectors.  None of these fields mentions `Q*dR` or the final
least-squares perturbation. -/
structure PivotedStoredQRQdRLocalReady (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (alpha : Fin m → ℝ) (eta : ℝ) (dR : Fin n → Fin n → ℝ) : Prop where
  eta_nonneg : 0 ≤ eta
  correction_row : ∀ i j,
    |rectTopBlock (m := m) dR i j| ≤ eta * alpha i
  raw_ratio : ∀ k, k < n → ∀ q, q < k →
    vecNorm2 (pivotedStoredQRRawVector fp hmn A k) /
        vecNorm2 (pivotedStoredQRRawVector fp hmn A q) ≤ 2
  correction_tail_norm : ∀ k (hk : k < n) (j : Fin n),
    vecNorm2
        (householderTrailingPart m (pivotedQRActiveRow hmn k hk)
          (fun i => rectTopBlock (m := m) dR i j)) ≤
      eta * |pivotedStoredQRSigma fp hmn A k|

/-- Forward-row-policy form of the local `Q[dR;0]` data.

Unlike `PivotedStoredQRQdRLocalReady`, this interface does not encode any
cross-stage comparison of rounded pivot scales or raw-vector norms.  The only
reflector-history datum is the row-wise bound on the *actual prefix image* of
the current raw vector.  This is the Cox--Higham row-growth policy itself, and
is independent of `dR` and of every backward-error conclusion. -/
structure PivotedStoredQRQdRPrefixReady (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (alpha : Fin m → ℝ) (eta : ℝ) (dR : Fin n → Fin n → ℝ) : Prop where
  eta_nonneg : 0 ≤ eta
  correction_row : ∀ i j,
    |rectTopBlock (m := m) dR i j| ≤ eta * alpha i
  prefix_vector_row : ∀ k, k < n → ∀ i,
    |Wave19.applyProd
        (fun q => householder m
          (pivotedStoredQRRawVector fp hmn A q)
          (pivotedStoredQRBeta fp hmn A q)) 0 k
        (pivotedStoredQRRawVector fp hmn A k) i| ≤
      (1 + 4 * (k : ℝ)) * 2 * alpha i
  correction_tail_norm : ∀ k (hk : k < n) (j : Fin n),
    vecNorm2
        (householderTrailingPart m (pivotedQRActiveRow hmn k hk)
          (fun i => rectTopBlock (m := m) dR i j)) ≤
      eta * |pivotedStoredQRSigma fp hmn A k|

/-- The prefix image of a raw vector, obtained from the existing
`applyProd_rawHouseholder_entrywise_le` engine. -/
theorem pivotedStoredQR_rawVector_prefix_entrywise_le
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (alpha : Fin m → ℝ)
    (ready : PivotedStoredQRQdRReflectorReady fp hmn A alpha)
    {eta : ℝ} {dR : Fin n → Fin n → ℝ}
    (qdr : PivotedStoredQRQdRLocalReady fp hmn A alpha eta dR)
    (k : ℕ) (hk : k < n) (r : Fin m) :
    |Wave19.applyProd
        (fun q => householder m
          (pivotedStoredQRRawVector fp hmn A q)
          (pivotedStoredQRBeta fp hmn A q)) 0 k
        (pivotedStoredQRRawVector fp hmn A k) r| ≤
      (1 + 4 * (k : ℝ)) * 2 * alpha r := by
  apply applyProd_rawHouseholder_entrywise_le
    (fun q => pivotedStoredQRRawVector fp hmn A q)
    (fun q => pivotedStoredQRBeta fp hmn A q)
    (pivotedStoredQRRawVector fp hmn A k) alpha 2 k r
    (by norm_num) ready.alpha_nonneg
    (fun q => pivotedStoredQRPseq_orthogonal fp hmn A q)
  · intro q hq
    have hqn : q < n := lt_trans hq hk
    have hlower := pivotedStoredQRRawVector_sigma_sign_bound fp hmn A q hqn
    have hscale : 0 < Real.sqrt 2 * |pivotedStoredQRSigma fp hmn A q| :=
      mul_pos (Real.sqrt_pos.mpr (by norm_num)) (ready.sigma_pos q hqn)
    linarith
  · intro q hq
    apply householderBetaSpec_mul_vecNorm2_sq_eq_two_of_pos
    have hqn : q < n := lt_trans hq hk
    have hlower := pivotedStoredQRRawVector_sigma_sign_bound fp hmn A q hqn
    have hscale : 0 < Real.sqrt 2 * |pivotedStoredQRSigma fp hmn A q| :=
      mul_pos (Real.sqrt_pos.mpr (by norm_num)) (ready.sigma_pos q hqn)
    linarith
  · intro q hq s
    exact ready.vector_row q (lt_trans hq hk) s
  · intro q hq
    exact qdr.raw_ratio k hk q hq
  · exact ready.vector_row k hk r

/-- The legacy norm-ratio readiness implies the strictly weaker, forward
prefix-row readiness.  Producer code may instead establish the latter directly
from its executed row policy, without assuming a rounded sigma history. -/
theorem PivotedStoredQRQdRLocalReady.toPrefixReady
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (alpha : Fin m → ℝ)
    (ready : PivotedStoredQRQdRReflectorReady fp hmn A alpha)
    {eta : ℝ} {dR : Fin n → Fin n → ℝ}
    (qdr : PivotedStoredQRQdRLocalReady fp hmn A alpha eta dR) :
    PivotedStoredQRQdRPrefixReady fp hmn A alpha eta dR :=
  { eta_nonneg := qdr.eta_nonneg
    correction_row := qdr.correction_row
    prefix_vector_row := fun k hk i =>
      pivotedStoredQR_rawVector_prefix_entrywise_le fp hmn A alpha
        ready qdr k hk i
    correction_tail_norm := qdr.correction_tail_norm }

/-- The active-tail field supplies the direct scalar multiplier in (3.7).
The zero prefix of the executed raw vector is used to replace the full
correction column by its active tail before applying Cauchy--Schwarz. -/
theorem pivotedStoredQR_QdR_direct_multiplier_le
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (alpha : Fin m → ℝ)
    (ready : PivotedStoredQRQdRReflectorReady fp hmn A alpha)
    {eta : ℝ} {dR : Fin n → Fin n → ℝ}
    (qdr : PivotedStoredQRQdRLocalReady fp hmn A alpha eta dR)
    (k : ℕ) (hk : k < n) (j : Fin n) :
    |pivotedStoredQRBeta fp hmn A k *
        (∑ s : Fin m, pivotedStoredQRRawVector fp hmn A k s *
          rectTopBlock (m := m) dR s j)| ≤
      Real.sqrt 2 * eta := by
  let v := pivotedStoredQRRawVector fp hmn A k
  let f : Fin m → ℝ := fun s => rectTopBlock (m := m) dR s j
  let p := pivotedQRActiveRow hmn k hk
  let w := householderTrailingPart m p f
  have hinner : (∑ s : Fin m, v s * f s) = ∑ s : Fin m, v s * w s := by
    apply Finset.sum_congr rfl
    intro s _hs
    by_cases hsk : s.val < k
    · have hvzero : v s = 0 := by
        exact pivotedStoredQRRawVector_zero_prefix fp hmn A k hk s hsk
      simp [hvzero]
    · have hsp : ¬ s.val < p.val := by simpa [p, pivotedQRActiveRow] using hsk
      simp [w, householderTrailingPart, hsp]
  have hvnorm : Real.sqrt 2 * |pivotedStoredQRSigma fp hmn A k| ≤
      vecNorm2 v := by
    simpa [v] using pivotedStoredQRRawVector_sigma_sign_bound fp hmn A k hk
  have hvpos : 0 < vecNorm2 v := by
    have hscale : 0 < Real.sqrt 2 * |pivotedStoredQRSigma fp hmn A k| :=
      mul_pos (Real.sqrt_pos.mpr (by norm_num)) (ready.sigma_pos k hk)
    linarith
  have hbeta : pivotedStoredQRBeta fp hmn A k * vecNorm2 v ^ 2 = 2 := by
    simpa [pivotedStoredQRBeta, v] using
      householderBetaSpec_mul_vecNorm2_sq_eq_two_of_pos v hvpos
  have htail : vecNorm2 w ≤ eta * |pivotedStoredQRSigma fp hmn A k| := by
    simpa [w, p, f] using qdr.correction_tail_norm k hk j
  have h := householder_multiplier_le_sqrt_two_mul
    v w (pivotedStoredQRSigma fp hmn A k)
    (pivotedStoredQRBeta fp hmn A k) eta
    (ready.sigma_pos k hk) qdr.eta_nonneg hvnorm htail hbeta
  simpa [v, f, hinner] using h

/-- Direct-multiplier estimate from the prefix-policy readiness.  This is the
same local Cauchy--Schwarz calculation as
`pivotedStoredQR_QdR_direct_multiplier_le`, but it needs no raw-vector ratio
field: only the executed pivot's positivity and the correction-tail budget are
used. -/
theorem pivotedStoredQR_QdR_direct_multiplier_le_of_prefixReady
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (alpha : Fin m → ℝ)
    (hsigma : ∀ k, k < n → 0 < |pivotedStoredQRSigma fp hmn A k|)
    {eta : ℝ} {dR : Fin n → Fin n → ℝ}
    (qdr : PivotedStoredQRQdRPrefixReady fp hmn A alpha eta dR)
    (k : ℕ) (hk : k < n) (j : Fin n) :
    |pivotedStoredQRBeta fp hmn A k *
        (∑ s : Fin m, pivotedStoredQRRawVector fp hmn A k s *
          rectTopBlock (m := m) dR s j)| ≤
      Real.sqrt 2 * eta := by
  let v := pivotedStoredQRRawVector fp hmn A k
  let f : Fin m → ℝ := fun s => rectTopBlock (m := m) dR s j
  let p := pivotedQRActiveRow hmn k hk
  let w := householderTrailingPart m p f
  have hinner : (∑ s : Fin m, v s * f s) = ∑ s : Fin m, v s * w s := by
    apply Finset.sum_congr rfl
    intro s _hs
    by_cases hsk : s.val < k
    · have hvzero : v s = 0 := by
        exact pivotedStoredQRRawVector_zero_prefix fp hmn A k hk s hsk
      simp [hvzero]
    · have hsp : ¬ s.val < p.val := by simpa [p, pivotedQRActiveRow] using hsk
      simp [w, householderTrailingPart, hsp]
  have hvnorm : Real.sqrt 2 * |pivotedStoredQRSigma fp hmn A k| ≤
      vecNorm2 v := by
    simpa [v] using pivotedStoredQRRawVector_sigma_sign_bound fp hmn A k hk
  have hvpos : 0 < vecNorm2 v := by
    have hscale : 0 < Real.sqrt 2 * |pivotedStoredQRSigma fp hmn A k| :=
      mul_pos (Real.sqrt_pos.mpr (by norm_num)) (hsigma k hk)
    linarith
  have hbeta : pivotedStoredQRBeta fp hmn A k * vecNorm2 v ^ 2 = 2 := by
    simpa [pivotedStoredQRBeta, v] using
      householderBetaSpec_mul_vecNorm2_sq_eq_two_of_pos v hvpos
  have htail : vecNorm2 w ≤ eta * |pivotedStoredQRSigma fp hmn A k| := by
    simpa [w, p, f] using qdr.correction_tail_norm k hk j
  have h := householder_multiplier_le_sqrt_two_mul
    v w (pivotedStoredQRSigma fp hmn A k)
    (pivotedStoredQRBeta fp hmn A k) eta
    (hsigma k hk) qdr.eta_nonneg hvnorm htail hbeta
  simpa [v, f, hinner] using h

/-- Cox--Higham `(3.7)--(3.11)` from an executed forward row policy.

The reflector prefix is bounded directly by `prefix_vector_row`; consequently
this theorem has no strict or weak rounded-pivot history premise. -/
theorem pivotedStoredQR_QdR_entrywise_le_of_prefixReady
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (alpha : Fin m → ℝ)
    (halpha : ∀ i, 0 ≤ alpha i)
    (hsigma : ∀ k, k < n → 0 < |pivotedStoredQRSigma fp hmn A k|)
    {eta : ℝ} {dR : Fin n → Fin n → ℝ}
    (qdr : PivotedStoredQRQdRPrefixReady fp hmn A alpha eta dR)
    (i : Fin m) (j : Fin n) :
    |matMulRect m m n
        (Wave19.Qacc (pivotedStoredQRPseq fp hmn A) n)
        (rectTopBlock (m := m) dR) i j| ≤
      (1 + 3 * (n : ℝ) * (1 + 4 * (n : ℝ))) * eta * alpha i := by
  let v : ℕ → Fin m → ℝ := fun k => pivotedStoredQRRawVector fp hmn A k
  let beta : ℕ → ℝ := fun k => pivotedStoredQRBeta fp hmn A k
  let P : ℕ → Fin m → Fin m → ℝ :=
    fun k => householder m (v k) (beta k)
  let f : Fin m → ℝ := fun s => rectTopBlock (m := m) dR s j
  have hQ :
      matMulRect m m n
          (Wave19.Qacc (pivotedStoredQRPseq fp hmn A) n)
          (rectTopBlock (m := m) dR) i j =
        Wave19.applyProd P 0 n f i := by
    simpa [P, v, beta, f, pivotedStoredQRPseq] using
      qacc_matMulRect_eq_applyProd P
        (fun k => householder_symmetric m (v k) (beta k)) n
        (rectTopBlock (m := m) dR) i j
  rw [hQ, applyProd_rawHouseholder_direct_expansion]
  have hsqrt : 2 * Real.sqrt 2 ≤ (3 : ℝ) := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hn := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  have hterm : ∀ k ∈ Finset.range n,
      |Wave19.applyProd P 0 k (rawHouseholderDirectTerm v beta f k) i| ≤
        3 * (1 + 4 * (n : ℝ)) * eta * alpha i := by
    intro k hkset
    have hk : k < n := Finset.mem_range.mp hkset
    have hmult :
        |beta k * (∑ s : Fin m, v k s * f s)| ≤ Real.sqrt 2 * eta := by
      simpa [v, beta, f] using
        pivotedStoredQR_QdR_direct_multiplier_le_of_prefixReady
          fp hmn A alpha hsigma qdr k hk j
    have hprefix :
        |Wave19.applyProd P 0 k (v k) i| ≤
          (1 + 4 * (k : ℝ)) * 2 * alpha i := by
      simpa [P, v, beta] using qdr.prefix_vector_row k hk i
    rw [applyProd_rawHouseholderDirectTerm, abs_mul]
    have hmul :
        |beta k * (∑ s : Fin m, v k s * f s)| *
            |Wave19.applyProd P 0 k (v k) i| ≤
          (Real.sqrt 2 * eta) *
            ((1 + 4 * (k : ℝ)) * 2 * alpha i) := by
      exact mul_le_mul hmult hprefix (abs_nonneg _)
        (mul_nonneg (Real.sqrt_nonneg _) qdr.eta_nonneg)
    have hkn : (k : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.le_of_lt hk
    have hkcoeff : 0 ≤ 1 + 4 * (k : ℝ) := by positivity
    have hncoeff : 1 + 4 * (k : ℝ) ≤ 1 + 4 * (n : ℝ) := by linarith
    have hcoef :
        (2 * Real.sqrt 2) * (1 + 4 * (k : ℝ)) ≤
          3 * (1 + 4 * (n : ℝ)) := by
      calc
        (2 * Real.sqrt 2) * (1 + 4 * (k : ℝ)) ≤
            3 * (1 + 4 * (k : ℝ)) :=
          mul_le_mul_of_nonneg_right hsqrt hkcoeff
        _ ≤ 3 * (1 + 4 * (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hncoeff (by norm_num)
    have hscale : 0 ≤ eta * alpha i :=
      mul_nonneg qdr.eta_nonneg (halpha i)
    calc
      |beta k * (∑ s : Fin m, v k s * f s)| *
            |Wave19.applyProd P 0 k (v k) i| ≤
          (Real.sqrt 2 * eta) *
            ((1 + 4 * (k : ℝ)) * 2 * alpha i) := hmul
      _ = ((2 * Real.sqrt 2) * (1 + 4 * (k : ℝ))) *
            (eta * alpha i) := by ring
      _ ≤ (3 * (1 + 4 * (n : ℝ))) * (eta * alpha i) :=
        mul_le_mul_of_nonneg_right hcoef hscale
      _ = 3 * (1 + 4 * (n : ℝ)) * eta * alpha i := by ring
  have hsum :
      |∑ k ∈ Finset.range n,
          Wave19.applyProd P 0 k (rawHouseholderDirectTerm v beta f k) i| ≤
        (n : ℝ) * (3 * (1 + 4 * (n : ℝ)) * eta * alpha i) := by
    calc
      |∑ k ∈ Finset.range n,
          Wave19.applyProd P 0 k (rawHouseholderDirectTerm v beta f k) i| ≤
          ∑ k ∈ Finset.range n,
            |Wave19.applyProd P 0 k
              (rawHouseholderDirectTerm v beta f k) i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ Finset.range n,
          (3 * (1 + 4 * (n : ℝ)) * eta * alpha i) := by
        apply Finset.sum_le_sum
        intro k hk
        exact hterm k hk
      _ = (n : ℝ) * (3 * (1 + 4 * (n : ℝ)) * eta * alpha i) := by
        simp
  have hsub := abs_sub_le (f i) 0
    (∑ k ∈ Finset.range n,
      Wave19.applyProd P 0 k (rawHouseholderDirectTerm v beta f k) i)
  have hf : |f i| ≤ eta * alpha i := by
    simpa [f] using qdr.correction_row i j
  calc
    |f i - ∑ k ∈ Finset.range n,
        Wave19.applyProd P 0 k (rawHouseholderDirectTerm v beta f k) i| ≤
      |f i| +
        |∑ k ∈ Finset.range n,
          Wave19.applyProd P 0 k (rawHouseholderDirectTerm v beta f k) i| := by
      simpa using hsub
    _ ≤ eta * alpha i +
        (n : ℝ) * (3 * (1 + 4 * (n : ℝ)) * eta * alpha i) :=
      add_le_add hf hsum
    _ = (1 + 3 * (n : ℝ) * (1 + 4 * (n : ℝ))) * eta * alpha i := by
      ring

/-- Cox--Higham (3.7)--(3.11) bound for the actual pulled-back triangular
correction, under the explicit local row/tail readiness data.

The polynomial is kept visible: the initial correction contributes `1`, and
the `n` transported rank-one terms contribute at most
`3 * n * (1 + 4*n)`. -/
theorem pivotedStoredQR_QdR_entrywise_le
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (alpha : Fin m → ℝ)
    (ready : PivotedStoredQRQdRReflectorReady fp hmn A alpha)
    {eta : ℝ} {dR : Fin n → Fin n → ℝ}
    (qdr : PivotedStoredQRQdRLocalReady fp hmn A alpha eta dR)
    (i : Fin m) (j : Fin n) :
    |matMulRect m m n
        (Wave19.Qacc (pivotedStoredQRPseq fp hmn A) n)
        (rectTopBlock (m := m) dR) i j| ≤
      (1 + 3 * (n : ℝ) * (1 + 4 * (n : ℝ))) * eta * alpha i := by
  let v : ℕ → Fin m → ℝ := fun k => pivotedStoredQRRawVector fp hmn A k
  let beta : ℕ → ℝ := fun k => pivotedStoredQRBeta fp hmn A k
  let P : ℕ → Fin m → Fin m → ℝ :=
    fun k => householder m (v k) (beta k)
  let f : Fin m → ℝ := fun s => rectTopBlock (m := m) dR s j
  have hQ :
      matMulRect m m n
          (Wave19.Qacc (pivotedStoredQRPseq fp hmn A) n)
          (rectTopBlock (m := m) dR) i j =
        Wave19.applyProd P 0 n f i := by
    simpa [P, v, beta, f, pivotedStoredQRPseq] using
      qacc_matMulRect_eq_applyProd P
        (fun k => householder_symmetric m (v k) (beta k)) n
        (rectTopBlock (m := m) dR) i j
  rw [hQ, applyProd_rawHouseholder_direct_expansion]
  have hsqrt : 2 * Real.sqrt 2 ≤ (3 : ℝ) := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hn := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  have hterm : ∀ k ∈ Finset.range n,
      |Wave19.applyProd P 0 k (rawHouseholderDirectTerm v beta f k) i| ≤
        3 * (1 + 4 * (n : ℝ)) * eta * alpha i := by
    intro k hkset
    have hk : k < n := Finset.mem_range.mp hkset
    have hmult :
        |beta k * (∑ s : Fin m, v k s * f s)| ≤ Real.sqrt 2 * eta := by
      simpa [v, beta, f] using
        pivotedStoredQR_QdR_direct_multiplier_le fp hmn A alpha
          ready qdr k hk j
    have hprefix :
        |Wave19.applyProd P 0 k (v k) i| ≤
          (1 + 4 * (k : ℝ)) * 2 * alpha i := by
      simpa [P, v, beta] using
        pivotedStoredQR_rawVector_prefix_entrywise_le fp hmn A alpha
          ready qdr k hk i
    rw [applyProd_rawHouseholderDirectTerm, abs_mul]
    have hmul :
        |beta k * (∑ s : Fin m, v k s * f s)| *
            |Wave19.applyProd P 0 k (v k) i| ≤
          (Real.sqrt 2 * eta) *
            ((1 + 4 * (k : ℝ)) * 2 * alpha i) := by
      exact mul_le_mul hmult hprefix (abs_nonneg _)
        (mul_nonneg (Real.sqrt_nonneg _ ) qdr.eta_nonneg)
    have hkn : (k : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.le_of_lt hk
    have hkcoeff : 0 ≤ 1 + 4 * (k : ℝ) := by positivity
    have hncoeff : 1 + 4 * (k : ℝ) ≤ 1 + 4 * (n : ℝ) := by linarith
    have hcoef :
        (2 * Real.sqrt 2) * (1 + 4 * (k : ℝ)) ≤
          3 * (1 + 4 * (n : ℝ)) := by
      calc
        (2 * Real.sqrt 2) * (1 + 4 * (k : ℝ)) ≤
            3 * (1 + 4 * (k : ℝ)) :=
          mul_le_mul_of_nonneg_right hsqrt hkcoeff
        _ ≤ 3 * (1 + 4 * (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hncoeff (by norm_num)
    have hscale : 0 ≤ eta * alpha i :=
      mul_nonneg qdr.eta_nonneg (ready.alpha_nonneg i)
    calc
      |beta k * (∑ s : Fin m, v k s * f s)| *
            |Wave19.applyProd P 0 k (v k) i| ≤
          (Real.sqrt 2 * eta) *
            ((1 + 4 * (k : ℝ)) * 2 * alpha i) := hmul
      _ = ((2 * Real.sqrt 2) * (1 + 4 * (k : ℝ))) *
            (eta * alpha i) := by ring
      _ ≤ (3 * (1 + 4 * (n : ℝ))) * (eta * alpha i) :=
        mul_le_mul_of_nonneg_right hcoef hscale
      _ = 3 * (1 + 4 * (n : ℝ)) * eta * alpha i := by ring
  have hsum :
      |∑ k ∈ Finset.range n,
          Wave19.applyProd P 0 k (rawHouseholderDirectTerm v beta f k) i| ≤
        (n : ℝ) * (3 * (1 + 4 * (n : ℝ)) * eta * alpha i) := by
    calc
      |∑ k ∈ Finset.range n,
          Wave19.applyProd P 0 k (rawHouseholderDirectTerm v beta f k) i| ≤
          ∑ k ∈ Finset.range n,
            |Wave19.applyProd P 0 k
              (rawHouseholderDirectTerm v beta f k) i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ Finset.range n,
          (3 * (1 + 4 * (n : ℝ)) * eta * alpha i) := by
        apply Finset.sum_le_sum
        intro k hk
        exact hterm k hk
      _ = (n : ℝ) * (3 * (1 + 4 * (n : ℝ)) * eta * alpha i) := by
        simp
  have hsub := abs_sub_le (f i) 0
    (∑ k ∈ Finset.range n,
      Wave19.applyProd P 0 k (rawHouseholderDirectTerm v beta f k) i)
  have hf : |f i| ≤ eta * alpha i := by
    simpa [f] using qdr.correction_row i j
  calc
    |f i - ∑ k ∈ Finset.range n,
        Wave19.applyProd P 0 k (rawHouseholderDirectTerm v beta f k) i| ≤
      |f i| +
        |∑ k ∈ Finset.range n,
          Wave19.applyProd P 0 k (rawHouseholderDirectTerm v beta f k) i| := by
      simpa using hsub
    _ ≤ eta * alpha i +
        (n : ℝ) * (3 * (1 + 4 * (n : ℝ)) * eta * alpha i) :=
      add_le_add hf hsum
    _ = (1 + 3 * (n : ℝ) * (1 + 4 * (n : ℝ))) * eta * alpha i := by
      ring

/-- Permutation-independent `n^2` packaging of the QdR estimate.

Thus the exact coefficient mapping to
`PivotedStoredQRSplit3BNumericalContract.backSub_transport_source_row` is
`backSubCoeff = 16 * eta`. -/
theorem pivotedStoredQR_QdR_source_n_sq_le
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (alpha : Fin m → ℝ)
    (ready : PivotedStoredQRQdRReflectorReady fp hmn A alpha)
    {eta : ℝ} {dR : Fin n → Fin n → ℝ}
    (qdr : PivotedStoredQRQdRLocalReady fp hmn A alpha eta dR)
    (i : Fin m) (j : Fin n) :
    |matMulRect m m n
        (Wave19.Qacc (pivotedStoredQRPseq fp hmn A) n)
        (rectTopBlock (m := m) dR) i
        ((pivotPermAcc (pivotedStoredQRSwapSeq fp hmn A) n).symm j)| ≤
      (n : ℝ) ^ 2 * (16 * eta) * alpha i := by
  have h := pivotedStoredQR_QdR_entrywise_le fp hmn A alpha ready qdr i
    ((pivotPermAcc (pivotedStoredQRSwapSeq fp hmn A) n).symm j)
  have hn : (1 : ℝ) ≤ (n : ℝ) := by
    have hj : j.val < n := j.isLt
    have hnNat : 1 ≤ n := by omega
    exact_mod_cast hnNat
  have hfactor :
      1 + 3 * (n : ℝ) * (1 + 4 * (n : ℝ)) ≤ 16 * (n : ℝ) ^ 2 := by
    have hprod : 0 ≤ ((n : ℝ) - 1) * (4 * (n : ℝ) + 1) :=
      mul_nonneg (sub_nonneg.mpr hn) (by positivity)
    nlinarith
  have hscale : 0 ≤ eta * alpha i :=
    mul_nonneg qdr.eta_nonneg (ready.alpha_nonneg i)
  calc
    |matMulRect m m n
        (Wave19.Qacc (pivotedStoredQRPseq fp hmn A) n)
        (rectTopBlock (m := m) dR) i
        ((pivotPermAcc (pivotedStoredQRSwapSeq fp hmn A) n).symm j)| ≤
      (1 + 3 * (n : ℝ) * (1 + 4 * (n : ℝ))) * eta * alpha i := h
    _ = (1 + 3 * (n : ℝ) * (1 + 4 * (n : ℝ))) *
        (eta * alpha i) := by ring
    _ ≤ (16 * (n : ℝ) ^ 2) * (eta * alpha i) :=
      mul_le_mul_of_nonneg_right hfactor hscale
    _ = (n : ℝ) ^ 2 * (16 * eta) * alpha i := by ring

/-- `n²` packaging of the prefix-policy QdR estimate. -/
theorem pivotedStoredQR_QdR_source_n_sq_le_of_prefixReady
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (alpha : Fin m → ℝ)
    (halpha : ∀ i, 0 ≤ alpha i)
    (hsigma : ∀ k, k < n → 0 < |pivotedStoredQRSigma fp hmn A k|)
    {eta : ℝ} {dR : Fin n → Fin n → ℝ}
    (qdr : PivotedStoredQRQdRPrefixReady fp hmn A alpha eta dR)
    (i : Fin m) (j : Fin n) :
    |matMulRect m m n
        (Wave19.Qacc (pivotedStoredQRPseq fp hmn A) n)
        (rectTopBlock (m := m) dR) i
        ((pivotPermAcc (pivotedStoredQRSwapSeq fp hmn A) n).symm j)| ≤
      (n : ℝ) ^ 2 * (16 * eta) * alpha i := by
  have h := pivotedStoredQR_QdR_entrywise_le_of_prefixReady
    fp hmn A alpha halpha hsigma qdr i
      ((pivotPermAcc (pivotedStoredQRSwapSeq fp hmn A) n).symm j)
  have hn : (1 : ℝ) ≤ (n : ℝ) := by
    have hj : j.val < n := j.isLt
    have hnNat : 1 ≤ n := by omega
    exact_mod_cast hnNat
  have hfactor :
      1 + 3 * (n : ℝ) * (1 + 4 * (n : ℝ)) ≤ 16 * (n : ℝ) ^ 2 := by
    have hprod : 0 ≤ ((n : ℝ) - 1) * (4 * (n : ℝ) + 1) :=
      mul_nonneg (sub_nonneg.mpr hn) (by positivity)
    nlinarith
  have hscale : 0 ≤ eta * alpha i :=
    mul_nonneg qdr.eta_nonneg (halpha i)
  calc
    |matMulRect m m n
        (Wave19.Qacc (pivotedStoredQRPseq fp hmn A) n)
        (rectTopBlock (m := m) dR) i
        ((pivotPermAcc (pivotedStoredQRSwapSeq fp hmn A) n).symm j)| ≤
      (1 + 3 * (n : ℝ) * (1 + 4 * (n : ℝ))) * eta * alpha i := h
    _ = (1 + 3 * (n : ℝ) * (1 + 4 * (n : ℝ))) *
        (eta * alpha i) := by ring
    _ ≤ (16 * (n : ℝ) ^ 2) * (eta * alpha i) :=
      mul_le_mul_of_nonneg_right hfactor hscale
    _ = (n : ℝ) ^ 2 * (16 * eta) * alpha i := by ring

/-- Direct discharge shape for the Split 3B contract's triangular-transport
field.  It remains only to construct the local row/tail readiness record for
each componentwise-admissible back-substitution perturbation.

The coefficient is explicit: `backSubCoeff = 16 * gamma fp n`. -/
theorem pivotedStoredQR_backSub_transport_source_row_of_localReady
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (alpha : Fin m → ℝ)
    (ready : PivotedStoredQRQdRReflectorReady fp hmn A alpha)
    (hlocal : ∀ dR : Fin n → Fin n → ℝ,
      (∀ i j,
        |dR i j| ≤ gamma fp n * |pivotedStoredQRTopR fp hmn A i j|) →
      PivotedStoredQRQdRLocalReady fp hmn A alpha (gamma fp n) dR) :
    ∀ dR : Fin n → Fin n → ℝ,
      (∀ i j,
        |dR i j| ≤ gamma fp n * |pivotedStoredQRTopR fp hmn A i j|) →
      ∀ i j,
        |matMulRect m m n
            (Wave19.Qacc (pivotedStoredQRPseq fp hmn A) n)
            (rectTopBlock (m := m) dR) i
            ((pivotPermAcc (pivotedStoredQRSwapSeq fp hmn A) n).symm j)| ≤
          (n : ℝ) ^ 2 * (16 * gamma fp n) * alpha i := by
  intro dR hdR i j
  exact pivotedStoredQR_QdR_source_n_sq_le fp hmn A alpha ready
    (hlocal dR hdR) i j

end Theorem20_7

end NumStability
