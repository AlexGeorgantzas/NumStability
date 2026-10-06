import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.MatVec

/-!
# Rounded stationary-iteration certificates

Reusable rounded right-hand-side formation, local-error data, and triangular
stationary-solve certificates.
-/

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


end NumStability
