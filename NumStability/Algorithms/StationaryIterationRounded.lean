-- Algorithms/StationaryIterationRounded.lean
--
-- Concrete floating-point producers for Higham, Chapter 17.  This file closes
-- the gap between the abstract local-error premise in equation (17.2) and the
-- rounded matvec/add/triangular-solve algorithms formalized elsewhere.

import NumStability.Algorithms.StationaryIteration
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution

namespace NumStability

open scoped BigOperators

/-- The actually rounded formation of `N x + b`: first the row-by-row rounded
    matrix-vector product, then one rounded addition in every component. -/
noncomputable def stationaryRoundedRhs (fp : FPModel) (n : ℕ)
    (N : Fin n → Fin n → ℝ) (b x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => fp.fl_add (fl_matVec fp n n N x i) (b i)

/-- The local error with Higham's source sign, defined from the computed
    iterates themselves.  With this definition equation (17.1) is exact. -/
noncomputable def stationaryLocalError (n : ℕ) (M N : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (x_hat : ℕ → Fin n → ℝ) : ℕ → Fin n → ℝ :=
  fun k i =>
    (∑ j : Fin n, N i j * x_hat k j) + b i -
      ∑ j : Fin n, M i j * x_hat (k + 1) j

/-- The canonical local error makes the source-sign computed iteration (17.1)
    hold without an additional premise. -/
theorem stationaryLocalError_sourceComputedIteration (n : ℕ)
    (M N : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (x_hat : ℕ → Fin n → ℝ) :
    SourceComputedIteration n M N b x_hat
      (stationaryLocalError n M N b x_hat) := by
  constructor
  intro k i
  simp only [stationaryLocalError]
  ring

/-- A reusable certificate saying that every stationary-iteration step is an
    exact solve with a componentwise-small perturbation of `M`, for the
    actually rounded right-hand side. -/
def RoundedStationarySolveCertificate (fp : FPModel) (n : ℕ)
    (M N : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (x_hat : ℕ → Fin n → ℝ) : Prop :=
  ∀ k, ∃ ΔM : Fin n → Fin n → ℝ,
    (∀ i j, |ΔM i j| ≤ gamma fp n * |M i j|) ∧
    ∀ i, ∑ j : Fin n, (M i j + ΔM i j) * x_hat (k + 1) j =
      stationaryRoundedRhs fp n N b (x_hat k) i

/-- Forming `N x + b` by a rounded matrix-vector product followed by a rounded
    componentwise addition has the sharp accumulated `γ_(n+1)` envelope. -/
theorem stationaryRoundedRhs_error_bound (fp : FPModel) (n : ℕ)
    (N : Fin n → Fin n → ℝ) (b x : Fin n → ℝ)
    (hvalid : gammaValid fp (n + 1)) :
    ∀ i, |stationaryRoundedRhs fp n N b x i -
        ((∑ j : Fin n, N i j * x j) + b i)| ≤
      gamma fp (n + 1) *
        ((∑ j : Fin n, |N i j| * |x j|) + |b i|) := by
  intro i
  let y : ℝ := ∑ j : Fin n, N i j * x j
  let y_hat : ℝ := fl_matVec fp n n N x i
  let s : ℝ := ∑ j : Fin n, |N i j| * |x j|
  have hn : gammaValid fp n := gammaValid_mono fp (by omega) hvalid
  have h1 : gammaValid fp 1 := gammaValid_mono fp (by omega) hvalid
  have hgamma_n : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have hgamma_1 : 0 ≤ gamma fp 1 := gamma_nonneg fp h1
  have hs : 0 ≤ s := by
    dsimp [s]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hy : |y| ≤ s := by
    dsimp [y, s]
    calc
      |∑ j : Fin n, N i j * x j|
          ≤ ∑ j : Fin n, |N i j * x j| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin n, |N i j| * |x j| := by
            apply Finset.sum_congr rfl
            intro j _
            exact abs_mul _ _
  have hmat : |y_hat - y| ≤ gamma fp n * s := by
    simpa [y_hat, y, s] using matVec_error_bound fp n n N x hn i
  have hy_hat : |y_hat| ≤ (1 + gamma fp n) * s := by
    calc
      |y_hat| = |(y_hat - y) + y| := by congr 1 <;> ring
      _ ≤ |y_hat - y| + |y| := abs_add_le _ _
      _ ≤ gamma fp n * s + s := add_le_add hmat hy
      _ = (1 + gamma fp n) * s := by ring
  obtain ⟨δ, hδ, hadd⟩ := fp.model_add y_hat (b i)
  have hδgamma : |δ| ≤ gamma fp 1 :=
    le_trans hδ (u_le_gamma fp (by omega) h1)
  have hgamma_acc :
      gamma fp n + gamma fp 1 + gamma fp n * gamma fp 1 ≤
        gamma fp (n + 1) :=
    gamma_sum_le fp n 1 hvalid
  have hgamma_one_mono : gamma fp 1 ≤ gamma fp (n + 1) :=
    gamma_mono fp (by omega) hvalid
  calc
    |stationaryRoundedRhs fp n N b x i -
        ((∑ j : Fin n, N i j * x j) + b i)|
        = |(y_hat + b i) * (1 + δ) - (y + b i)| := by
            simp only [stationaryRoundedRhs, y_hat, y, hadd]
    _ = |(y_hat - y) + δ * (y_hat + b i)| := by congr 1 <;> ring
    _ ≤ |y_hat - y| + |δ * (y_hat + b i)| := abs_add_le _ _
    _ = |y_hat - y| + |δ| * |y_hat + b i| := by rw [abs_mul]
    _ ≤ gamma fp n * s + gamma fp 1 * (|y_hat| + |b i|) := by
          gcongr
          exact abs_add_le _ _
    _ ≤ gamma fp n * s +
          gamma fp 1 * ((1 + gamma fp n) * s + |b i|) := by
          gcongr
    _ = (gamma fp n + gamma fp 1 + gamma fp n * gamma fp 1) * s +
          gamma fp 1 * |b i| := by ring
    _ ≤ gamma fp (n + 1) * s + gamma fp (n + 1) * |b i| := by
          exact add_le_add
            (mul_le_mul_of_nonneg_right hgamma_acc hs)
            (mul_le_mul_of_nonneg_right hgamma_one_mono (abs_nonneg _))
    _ = gamma fp (n + 1) *
          ((∑ j : Fin n, |N i j| * |x j|) + |b i|) := by
          dsimp [s]
          ring

/-- A rounded-solve certificate and the rounded `N x + b` producer imply the
    abstract local-error premise (17.2), with an explicit `γ_(n+1)` constant. -/
theorem localErrorBound_of_roundedStationarySolveCertificate (fp : FPModel)
    (n : ℕ) (M N : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (x_hat : ℕ → Fin n → ℝ)
    (hvalid : gammaValid fp (n + 1))
    (hsolve : RoundedStationarySolveCertificate fp n M N b x_hat) :
    LocalErrorBound n M N b x_hat
      (stationaryLocalError n M N b x_hat) (gamma fp (n + 1)) := by
  intro k i
  obtain ⟨ΔM, hΔM, hstep⟩ := hsolve k
  let mTerm : ℝ := ∑ j : Fin n, |M i j| * |x_hat (k + 1) j|
  let nTerm : ℝ := ∑ j : Fin n, |N i j| * |x_hat k j|
  have hn : gammaValid fp n := gammaValid_mono fp (by omega) hvalid
  have hgamma_n : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have hgamma_succ : 0 ≤ gamma fp (n + 1) := gamma_nonneg fp hvalid
  have hgamma_mono : gamma fp n ≤ gamma fp (n + 1) :=
    gamma_mono fp (by omega) hvalid
  have hm_nonneg : 0 ≤ mTerm := by
    dsimp [mTerm]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hn_nonneg : 0 ≤ nTerm := by
    dsimp [nTerm]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hsplit :
      (∑ j : Fin n, (M i j + ΔM i j) * x_hat (k + 1) j) =
        (∑ j : Fin n, M i j * x_hat (k + 1) j) +
          ∑ j : Fin n, ΔM i j * x_hat (k + 1) j := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hlocal_eq :
      stationaryLocalError n M N b x_hat k i =
        (((∑ j : Fin n, N i j * x_hat k j) + b i) -
            stationaryRoundedRhs fp n N b (x_hat k) i) +
          ∑ j : Fin n, ΔM i j * x_hat (k + 1) j := by
    simp only [stationaryLocalError]
    rw [← hstep i, hsplit]
    ring
  have hperturb :
      |∑ j : Fin n, ΔM i j * x_hat (k + 1) j| ≤
        gamma fp (n + 1) * mTerm := by
    calc
      |∑ j : Fin n, ΔM i j * x_hat (k + 1) j|
          ≤ ∑ j : Fin n, |ΔM i j * x_hat (k + 1) j| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin n, |ΔM i j| * |x_hat (k + 1) j| := by
            apply Finset.sum_congr rfl
            intro j _
            exact abs_mul _ _
      _ ≤ ∑ j : Fin n,
            (gamma fp n * |M i j|) * |x_hat (k + 1) j| := by
            gcongr with j _
            exact hΔM i j
      _ = gamma fp n * mTerm := by
            dsimp [mTerm]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ ≤ gamma fp (n + 1) * mTerm :=
            mul_le_mul_of_nonneg_right hgamma_mono hm_nonneg
  have hrhs := stationaryRoundedRhs_error_bound fp n N b (x_hat k) hvalid i
  have hrhs' :
      |((∑ j : Fin n, N i j * x_hat k j) + b i) -
          stationaryRoundedRhs fp n N b (x_hat k) i| ≤
        gamma fp (n + 1) * (nTerm + |b i|) := by
    simpa [nTerm, abs_sub_comm] using hrhs
  rw [hlocal_eq]
  calc
    |(((∑ j : Fin n, N i j * x_hat k j) + b i) -
          stationaryRoundedRhs fp n N b (x_hat k) i) +
        ∑ j : Fin n, ΔM i j * x_hat (k + 1) j|
        ≤ |((∑ j : Fin n, N i j * x_hat k j) + b i) -
              stationaryRoundedRhs fp n N b (x_hat k) i| +
            |∑ j : Fin n, ΔM i j * x_hat (k + 1) j| := abs_add_le _ _
    _ ≤ gamma fp (n + 1) * (nTerm + |b i|) +
          gamma fp (n + 1) * mTerm := add_le_add hrhs' hperturb
    _ = gamma fp (n + 1) *
          ((∑ j : Fin n, |M i j| * |x_hat (k + 1) j|) +
            ∑ j : Fin n, |N i j| * |x_hat k j| + |b i|) := by
          dsimp [mTerm, nTerm]
          ring

/-- Actual rounded stationary iteration when `M` is lower triangular. -/
noncomputable def flStationaryIterationLower (fp : FPModel) (n : ℕ)
    (M N : Fin n → Fin n → ℝ) (b x₀ : Fin n → ℝ) :
    ℕ → Fin n → ℝ
  | 0 => x₀
  | k + 1 =>
      fl_forwardSub fp n M
        (stationaryRoundedRhs fp n N b
          (flStationaryIterationLower fp n M N b x₀ k))

/-- Actual rounded stationary iteration when `M` is upper triangular. -/
noncomputable def flStationaryIterationUpper (fp : FPModel) (n : ℕ)
    (M N : Fin n → Fin n → ℝ) (b x₀ : Fin n → ℝ) :
    ℕ → Fin n → ℝ
  | 0 => x₀
  | k + 1 =>
      fl_backSub fp n M
        (stationaryRoundedRhs fp n N b
          (flStationaryIterationUpper fp n M N b x₀ k))

/-- Forward substitution supplies the rounded-solve certificate for every
    lower-triangular stationary-iteration step. -/
theorem flStationaryIterationLower_solveCertificate (fp : FPModel) (n : ℕ)
    (M N : Fin n → Fin n → ℝ) (b x₀ : Fin n → ℝ)
    (hdiag : ∀ i, M i i ≠ 0)
    (hLower : ∀ i j : Fin n, i.val < j.val → M i j = 0)
    (hvalid : gammaValid fp n) :
    RoundedStationarySolveCertificate fp n M N b
      (flStationaryIterationLower fp n M N b x₀) := by
  intro k
  simpa only [flStationaryIterationLower] using
    forwardSub_backward_error fp n M
      (stationaryRoundedRhs fp n N b
        (flStationaryIterationLower fp n M N b x₀ k))
      hdiag hLower hvalid

/-- Back substitution supplies the rounded-solve certificate for every
    upper-triangular stationary-iteration step. -/
theorem flStationaryIterationUpper_solveCertificate (fp : FPModel) (n : ℕ)
    (M N : Fin n → Fin n → ℝ) (b x₀ : Fin n → ℝ)
    (hdiag : ∀ i, M i i ≠ 0)
    (hUpper : ∀ i j : Fin n, j.val < i.val → M i j = 0)
    (hvalid : gammaValid fp n) :
    RoundedStationarySolveCertificate fp n M N b
      (flStationaryIterationUpper fp n M N b x₀) := by
  intro k
  simpa only [flStationaryIterationUpper] using
    backSub_backward_error fp n M
      (stationaryRoundedRhs fp n N b
        (flStationaryIterationUpper fp n M N b x₀ k))
      hdiag hUpper hvalid

/-- Concrete producer for equation (17.2), for lower-triangular `M`. -/
theorem flStationaryIterationLower_localErrorBound (fp : FPModel) (n : ℕ)
    (M N : Fin n → Fin n → ℝ) (b x₀ : Fin n → ℝ)
    (hdiag : ∀ i, M i i ≠ 0)
    (hLower : ∀ i j : Fin n, i.val < j.val → M i j = 0)
    (hvalid : gammaValid fp (n + 1)) :
    LocalErrorBound n M N b (flStationaryIterationLower fp n M N b x₀)
      (stationaryLocalError n M N b
        (flStationaryIterationLower fp n M N b x₀))
      (gamma fp (n + 1)) := by
  apply localErrorBound_of_roundedStationarySolveCertificate fp n M N b
      (flStationaryIterationLower fp n M N b x₀) hvalid
  exact flStationaryIterationLower_solveCertificate fp n M N b x₀ hdiag hLower
    (gammaValid_mono fp (by omega) hvalid)

/-- Concrete producer for equation (17.2), for upper-triangular `M`. -/
theorem flStationaryIterationUpper_localErrorBound (fp : FPModel) (n : ℕ)
    (M N : Fin n → Fin n → ℝ) (b x₀ : Fin n → ℝ)
    (hdiag : ∀ i, M i i ≠ 0)
    (hUpper : ∀ i j : Fin n, j.val < i.val → M i j = 0)
    (hvalid : gammaValid fp (n + 1)) :
    LocalErrorBound n M N b (flStationaryIterationUpper fp n M N b x₀)
      (stationaryLocalError n M N b
        (flStationaryIterationUpper fp n M N b x₀))
      (gamma fp (n + 1)) := by
  apply localErrorBound_of_roundedStationarySolveCertificate fp n M N b
      (flStationaryIterationUpper fp n M N b x₀) hvalid
  exact flStationaryIterationUpper_solveCertificate fp n M N b x₀ hdiag hUpper
    (gammaValid_mono fp (by omega) hvalid)

-- ============================================================
-- Actual-iterate consumer for equations (17.5)--(17.13)
-- ============================================================

/-- Equation (17.13) with the actual computed error on the left.  This theorem
    composes the exact source-sign recurrence (17.5), the produced local bound
    (17.2), its simplification (17.10), and the finite partial-sum certificate
    (17.12).  In particular, the conclusion is not merely a bound on a
    separately defined correction-budget vector. -/
theorem sourceComputedIteration_actual_forward_bound (n : ℕ)
    (A M N M_inv A_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_hat : ℕ → Fin n → ℝ) (ξ : ℕ → Fin n → ℝ)
    (hIter : SourceComputedIteration n M N b x_hat ξ)
    (cn_u θ_x cA : ℝ) (hcn : 0 ≤ cn_u) (hcA : 0 ≤ cA) (hθ : 0 ≤ θ_x)
    (hx_bound : ∀ k i, |x_hat k i| ≤ θ_x * |x i|)
    (hLocal : LocalErrorBound n M N b x_hat ξ cn_u)
    (m : ℕ)
    (hPartial : PartialSumBound n (iterMatrix n M_inv N) M_inv A_inv cA m) :
    ∀ i, |x i - x_hat (m + 1) i| ≤
      (∑ j : Fin n,
        |matPow n (iterMatrix n M_inv N) (m + 1) i j| *
          |x j - x_hat 0 j|) +
      cn_u * (1 + θ_x) * cA *
        mainForwardBoundVector n A_inv M N x i := by
  have hMN : ∀ i, ∑ j : Fin n, (M i j - N i j) * x j = b i := by
    intro i
    rw [← hAx i]
    apply Finset.sum_congr rfl
    intro j _
    rw [hS.splitting i j]
  have hξ : ∀ k i, |ξ k i| ≤
      cn_u * (1 + θ_x) *
        ∑ p : Fin n, (|M i p| + |N i p|) * |x p| :=
    local_error_simplified n M N b x hMN x_hat ξ cn_u θ_x
      hcn hθ hx_bound hLocal
  let q : Fin n → ℝ := fun j =>
    cn_u * (1 + θ_x) *
      ∑ p : Fin n, (|M j p| + |N j p|) * |x p|
  let w : ℕ → Fin n → ℝ := fun k => matMulVec n M_inv (ξ k)
  let μ : ℕ → Fin n → ℝ := fun _ l =>
    ∑ j : Fin n, |M_inv l j| * q j
  have hq : ∀ j, 0 ≤ q j := by
    intro j
    dsimp [q]
    exact mul_nonneg (mul_nonneg hcn (by linarith))
      (Finset.sum_nonneg fun p _ =>
        mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _))
  have hμ : ∀ k l, 0 ≤ μ k l := by
    intro k l
    dsimp [μ]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (hq j)
  have hw : ∀ k l, |w k l| ≤ μ k l := by
    intro k l
    dsimp [w, μ, matMulVec]
    calc
      |∑ j : Fin n, M_inv l j * ξ k j|
          ≤ ∑ j : Fin n, |M_inv l j * ξ k j| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin n, |M_inv l j| * |ξ k j| := by
            apply Finset.sum_congr rfl
            intro j _
            exact abs_mul _ _
      _ ≤ ∑ j : Fin n, |M_inv l j| * q j := by
            gcongr with j _
            exact hξ k j
  have hcorrection : ∀ i,
      (∑ k ∈ Finset.range (m + 1),
        ∑ l : Fin n,
          |matPow n (iterMatrix n M_inv N) k i l| * μ (m - k) l) =
      finiteForwardCorrection n (iterMatrix n M_inv N) M_inv M N x
        cn_u θ_x m i := by
    intro i
    unfold finiteForwardCorrection
    dsimp [μ, q]
    apply Finset.sum_congr rfl
    intro k hk
    calc
      (∑ l : Fin n,
          |matPow n (iterMatrix n M_inv N) k i l| *
            ∑ j : Fin n, |M_inv l j| *
              (cn_u * (1 + θ_x) *
                ∑ p : Fin n, (|M j p| + |N j p|) * |x p|)) =
        ∑ l : Fin n, ∑ j : Fin n,
          |matPow n (iterMatrix n M_inv N) k i l| *
            (|M_inv l j| *
              (cn_u * (1 + θ_x) *
                ∑ p : Fin n, (|M j p| + |N j p|) * |x p|)) := by
          apply Finset.sum_congr rfl
          intro l _
          rw [Finset.mul_sum]
      _ = ∑ j : Fin n, ∑ l : Fin n,
          |matPow n (iterMatrix n M_inv N) k i l| *
            (|M_inv l j| *
              (cn_u * (1 + θ_x) *
                ∑ p : Fin n, (|M j p| + |N j p|) * |x p|)) :=
          Finset.sum_comm
      _ = ∑ j : Fin n,
          (∑ l : Fin n,
            |matPow n (iterMatrix n M_inv N) k i l| * |M_inv l j|) *
              (cn_u * (1 + θ_x) *
                ∑ p : Fin n, (|M j p| + |N j p|) * |x p|) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro l _
          ring
  intro i
  have herr := sourceComputedIteration_error_finite_sum n A M N M_inv hS
    b x hAx x_hat ξ hIter m i
  have hcomponent := componentwise_forward_bound n (iterMatrix n M_inv N)
    (fun j => x j - x_hat 0 j) m w μ hw hμ i
  calc
    |x i - x_hat (m + 1) i| =
        |matMulVec n (matPow n (iterMatrix n M_inv N) (m + 1))
            (fun j => x j - x_hat 0 j) i +
          ∑ k ∈ Finset.range (m + 1),
            matMulVec n (matPow n (iterMatrix n M_inv N) k)
              (matMulVec n M_inv (ξ (m - k))) i| := by rw [herr]
    _ ≤ (∑ j : Fin n,
          |matPow n (iterMatrix n M_inv N) (m + 1) i j| *
            |x j - x_hat 0 j|) +
        ∑ k ∈ Finset.range (m + 1),
          ∑ l : Fin n,
            |matPow n (iterMatrix n M_inv N) k i l| * μ (m - k) l := by
          simpa [matMulVec, w] using hcomponent
    _ = (∑ j : Fin n,
          |matPow n (iterMatrix n M_inv N) (m + 1) i j| *
            |x j - x_hat 0 j|) +
        finiteForwardCorrection n (iterMatrix n M_inv N) M_inv M N x
          cn_u θ_x m i := by rw [hcorrection i]
    _ ≤ (∑ j : Fin n,
          |matPow n (iterMatrix n M_inv N) (m + 1) i j| *
            |x j - x_hat 0 j|) +
        cn_u * (1 + θ_x) * cA *
          mainForwardBoundVector n A_inv M N x i := by
          exact add_le_add (le_refl _)
            (finiteForwardCorrection_le_mainForwardBoundVector n
              (iterMatrix n M_inv N) M_inv A_inv M N x cn_u θ_x cA
              hcn hcA hθ m hPartial i)

/-- Equation (17.15) for the actual computed error.  This is the infinity-norm
    corollary of `sourceComputedIteration_actual_forward_bound`; unlike the old
    correction-vector wrapper, its left side is `‖x - x_hat_(m+1)‖∞`. -/
theorem sourceComputedIteration_actual_norm_forward_bound (n : ℕ)
    (A M N M_inv A_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_hat : ℕ → Fin n → ℝ) (ξ : ℕ → Fin n → ℝ)
    (hIter : SourceComputedIteration n M N b x_hat ξ)
    (cn_u θ_x cA : ℝ) (hcn : 0 ≤ cn_u) (hcA : 0 ≤ cA) (hθ : 0 ≤ θ_x)
    (hx_bound : ∀ k i, |x_hat k i| ≤ θ_x * |x i|)
    (hLocal : LocalErrorBound n M N b x_hat ξ cn_u)
    (m : ℕ)
    (hPartial : PartialSumBound n (iterMatrix n M_inv N) M_inv A_inv cA m) :
    infNormVec (fun i => x i - x_hat (m + 1) i) ≤
      infNorm (matPow n (iterMatrix n M_inv N) (m + 1)) *
        infNormVec (fun j => x j - x_hat 0 j) +
      cn_u * (1 + θ_x) * cA *
        infNormVec (mainForwardBoundVector n A_inv M N x) := by
  let P := matPow n (iterMatrix n M_inv N) (m + 1)
  let e₀ : Fin n → ℝ := fun j => x j - x_hat 0 j
  let c : ℝ := cn_u * (1 + θ_x) * cA
  have hc : 0 ≤ c := mul_nonneg (mul_nonneg hcn (by linarith)) hcA
  have hpoint := sourceComputedIteration_actual_forward_bound n
    A M N M_inv A_inv hS b x hAx x_hat ξ hIter cn_u θ_x cA
    hcn hcA hθ hx_bound hLocal m hPartial
  have hmain_nonneg := mainForwardBoundVector_nonneg n A_inv M N x
  have hbound_nonneg :
      0 ≤ infNorm P * infNormVec e₀ +
        c * infNormVec (mainForwardBoundVector n A_inv M N x) :=
    add_nonneg
      (mul_nonneg (infNorm_nonneg P) (infNormVec_nonneg e₀))
      (mul_nonneg hc (infNormVec_nonneg _))
  apply infNormVec_le_of_abs_le
  · intro i
    have hinitial :
        (∑ j : Fin n, |P i j| * |e₀ j|) ≤
          infNorm P * infNormVec e₀ := by
      calc
        (∑ j : Fin n, |P i j| * |e₀ j|)
            ≤ ∑ j : Fin n, |P i j| * infNormVec e₀ := by
              gcongr with j _
              exact abs_le_infNormVec e₀ j
        _ = (∑ j : Fin n, |P i j|) * infNormVec e₀ := by
              rw [Finset.sum_mul]
        _ ≤ infNorm P * infNormVec e₀ :=
              mul_le_mul_of_nonneg_right (row_sum_le_infNorm P i)
                (infNormVec_nonneg e₀)
    have hmain :
        c * mainForwardBoundVector n A_inv M N x i ≤
          c * infNormVec (mainForwardBoundVector n A_inv M N x) := by
      apply mul_le_mul_of_nonneg_left _ hc
      have habs := abs_le_infNormVec (mainForwardBoundVector n A_inv M N x) i
      simpa [abs_of_nonneg (hmain_nonneg i)] using habs
    calc
      |(fun r => x r - x_hat (m + 1) r) i|
          ≤ (∑ j : Fin n,
              |matPow n (iterMatrix n M_inv N) (m + 1) i j| *
                |x j - x_hat 0 j|) +
            cn_u * (1 + θ_x) * cA *
              mainForwardBoundVector n A_inv M N x i := hpoint i
      _ = (∑ j : Fin n, |P i j| * |e₀ j|) +
            c * mainForwardBoundVector n A_inv M N x i := by rfl
      _ ≤ infNorm P * infNormVec e₀ +
            c * infNormVec (mainForwardBoundVector n A_inv M N x) :=
          add_le_add hinitial hmain
  · exact hbound_nonneg

/-- End-to-end lower-triangular specialization of (17.13): the hypotheses now
    refer to an actual rounded stationary iteration, not an assumed local-error
    sequence. -/
theorem flStationaryIterationLower_actual_forward_bound (fp : FPModel) (n : ℕ)
    (A M N M_inv A_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x x₀ : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (hdiag : ∀ i, M i i ≠ 0)
    (hLower : ∀ i j : Fin n, i.val < j.val → M i j = 0)
    (hvalid : gammaValid fp (n + 1))
    (θ_x cA : ℝ) (hcA : 0 ≤ cA) (hθ : 0 ≤ θ_x)
    (hx_bound : ∀ k i,
      |flStationaryIterationLower fp n M N b x₀ k i| ≤ θ_x * |x i|)
    (m : ℕ)
    (hPartial : PartialSumBound n (iterMatrix n M_inv N) M_inv A_inv cA m) :
    ∀ i,
      |x i - flStationaryIterationLower fp n M N b x₀ (m + 1) i| ≤
        (∑ j : Fin n,
          |matPow n (iterMatrix n M_inv N) (m + 1) i j| * |x j - x₀ j|) +
        gamma fp (n + 1) * (1 + θ_x) * cA *
          mainForwardBoundVector n A_inv M N x i := by
  apply sourceComputedIteration_actual_forward_bound n A M N M_inv A_inv hS
    b x hAx (flStationaryIterationLower fp n M N b x₀)
    (stationaryLocalError n M N b
      (flStationaryIterationLower fp n M N b x₀))
    (stationaryLocalError_sourceComputedIteration n M N b
      (flStationaryIterationLower fp n M N b x₀))
    (gamma fp (n + 1)) θ_x cA (gamma_nonneg fp hvalid) hcA hθ
    hx_bound
    (flStationaryIterationLower_localErrorBound fp n M N b x₀
      hdiag hLower hvalid)
    m hPartial

/-- End-to-end upper-triangular specialization of (17.13). -/
theorem flStationaryIterationUpper_actual_forward_bound (fp : FPModel) (n : ℕ)
    (A M N M_inv A_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x x₀ : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (hdiag : ∀ i, M i i ≠ 0)
    (hUpper : ∀ i j : Fin n, j.val < i.val → M i j = 0)
    (hvalid : gammaValid fp (n + 1))
    (θ_x cA : ℝ) (hcA : 0 ≤ cA) (hθ : 0 ≤ θ_x)
    (hx_bound : ∀ k i,
      |flStationaryIterationUpper fp n M N b x₀ k i| ≤ θ_x * |x i|)
    (m : ℕ)
    (hPartial : PartialSumBound n (iterMatrix n M_inv N) M_inv A_inv cA m) :
    ∀ i,
      |x i - flStationaryIterationUpper fp n M N b x₀ (m + 1) i| ≤
        (∑ j : Fin n,
          |matPow n (iterMatrix n M_inv N) (m + 1) i j| * |x j - x₀ j|) +
        gamma fp (n + 1) * (1 + θ_x) * cA *
          mainForwardBoundVector n A_inv M N x i := by
  apply sourceComputedIteration_actual_forward_bound n A M N M_inv A_inv hS
    b x hAx (flStationaryIterationUpper fp n M N b x₀)
    (stationaryLocalError n M N b
      (flStationaryIterationUpper fp n M N b x₀))
    (stationaryLocalError_sourceComputedIteration n M N b
      (flStationaryIterationUpper fp n M N b x₀))
    (gamma fp (n + 1)) θ_x cA (gamma_nonneg fp hvalid) hcA hθ
    hx_bound
    (flStationaryIterationUpper_localErrorBound fp n M N b x₀
      hdiag hUpper hvalid)
    m hPartial

end NumStability
