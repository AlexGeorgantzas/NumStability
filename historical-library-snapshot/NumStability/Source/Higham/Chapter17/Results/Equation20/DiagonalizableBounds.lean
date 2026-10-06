import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Convergence.Singular.FixedSubspaces
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.ErrorAnalysis.Forward.ComplementDecomposition
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.ErrorAnalysis.Local.OneStep
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.ErrorAnalysis.Residual.Identities
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Execution.Computed.Model
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Projectors.Drazin.Algebra
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Recurrences.Affine.Unrolling
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Splittings.Core.Definitions
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Splittings.Scaling.Diagonal
import NumStability.Analysis.Conditioning.LinearSystems.SubordinatePerturbation
import NumStability.Analysis.LinearOperators.MatrixPowers.JordanScaling.RealDiagonal
import NumStability.Analysis.MatrixAlgebra
import NumStability.Source.Higham.Chapter17.Equation01.ComputedIteration.Results
import NumStability.Source.Higham.Chapter17.Equation02.LocalError.Results
import NumStability.Source.Higham.Chapter17.Equation03.ComputedRecurrence.Results
import NumStability.Source.Higham.Chapter17.Equation04.FixedPoint.Results
import NumStability.Source.Higham.Chapter17.Equation05.ErrorExpansion.Results
import NumStability.Source.Higham.Chapter17.Equation06.ComponentwiseForward.Results
import NumStability.Source.Higham.Chapter17.Equation07.NormwiseGrowth.Results
import NumStability.Source.Higham.Chapter17.Equation08.NormwiseForward.Results
import NumStability.Source.Higham.Chapter17.Equation09.ComponentwiseGrowth.Results
import NumStability.Source.Higham.Chapter17.Equation10.LocalErrorSimplification.Results
import NumStability.Source.Higham.Chapter17.Equation12.PartialSumBound.Results
import NumStability.Source.Higham.Chapter17.Equation13.ComponentwiseForward.Results
import NumStability.Source.Higham.Chapter17.Equation15.NormwiseForward.Results
import NumStability.Source.Higham.Chapter17.Equation16.Jacobi.Results
import NumStability.Source.Higham.Chapter17.Equation17.SOR.Results
import NumStability.Source.Higham.Chapter17.Equation18.ResidualRecurrence.Results
import NumStability.Source.Higham.Chapter17.Equation19.ResidualBound.Results
import NumStability.Source.Higham.Chapter17.Equation20.ResidualSigma.Results
import NumStability.Source.Higham.Chapter17.Equation21.SingularIteration.Results
import NumStability.Source.Higham.Chapter17.Equation27.SingularErrorSplit.Results
import NumStability.Source.Higham.Chapter17.Equation28.SingularErrorSplit.Results
import NumStability.Source.Higham.Chapter17.Equation29.SingularSource.Results
import NumStability.Source.Higham.Chapter17.Equation33.StoppingTests.Results
import NumStability.Source.Higham.Chapter17.Section02.ScaleIndependence.Results
import NumStability.Source.Higham.Chapter17.Section04.PrintedConclusions.Results

/-!
# Higham Chapter 17, Equation 17.20: diagonalizable residual bounds

Canonical finite, supremum, and `tsum` residual-sigma bounds for a real
diagonalization.
-/

namespace NumStability

open scoped BigOperators

/-- Geometric series partial sum bound: ∑_{k=0}^m q^k ≤ 1/(1-q) for 0 ≤ q < 1. -/
private theorem geom_partial_sum_le (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), q ^ k ≤ 1 / (1 - q) := by
  have hq1' : (0 : ℝ) < 1 - q := by linarith
  rw [le_div_iff₀ hq1']
  calc (∑ k ∈ Finset.range (m + 1), q ^ k) * (1 - q)
      = ∑ k ∈ Finset.range (m + 1), (q ^ k - q ^ (k + 1)) := by
        rw [Finset.sum_mul]; congr 1; ext k; ring
    _ = 1 - q ^ (m + 1) := by
        induction m with
        | zero => simp
        | succ m ih =>
          rw [Finset.sum_range_succ]; linarith
    _ ≤ 1 := by linarith [pow_nonneg hq (m + 1)]

/-- **σ bound** (§17.3): ∑_{k=0}^m ‖H^k(I−H)‖∞ ≤ ‖I−H‖∞/(1−q) when ‖H‖∞ ≤ q < 1. -/
theorem sigma_bound (n : ℕ) (hn : 0 < n)
    (H : Fin n → Fin n → ℝ)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hH : infNorm H ≤ q) (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1),
      infNorm (matMul n (matPow n H k) (matSub_id n H)) ≤
    infNorm (matSub_id n H) / (1 - q) := by
  have hq1' : (0 : ℝ) < 1 - q := by linarith
  calc ∑ k ∈ Finset.range (m + 1),
        infNorm (matMul n (matPow n H k) (matSub_id n H))
      ≤ ∑ k ∈ Finset.range (m + 1),
        (q ^ k * infNorm (matSub_id n H)) := by
        gcongr with k _
        calc infNorm (matMul n (matPow n H k) (matSub_id n H))
            ≤ infNorm (matPow n H k) * infNorm (matSub_id n H) :=
              infNorm_matMul_le hn _ _
          _ ≤ q ^ k * infNorm (matSub_id n H) := by
              apply mul_le_mul_of_nonneg_right _ (infNorm_nonneg _)
              exact (infNorm_matPow_le hn H k).trans (pow_le_pow_left₀ (infNorm_nonneg H) hH k)
    _ = (∑ k ∈ Finset.range (m + 1), q ^ k) * infNorm (matSub_id n H) := by
        rw [Finset.sum_mul]
    _ ≤ (1 / (1 - q)) * infNorm (matSub_id n H) := by
        apply mul_le_mul_of_nonneg_right (geom_partial_sum_le q hq hq1 m) (infNorm_nonneg _)
    _ = infNorm (matSub_id n H) / (1 - q) := by
        rw [one_div, mul_comm, div_eq_mul_inv]






























































































































private theorem residual_geometric_partial_le_ratio (lam : ℝ)
    (hLam : |lam| < 1) (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), |lam| ^ k * |1 - lam| ≤
      |1 - lam| / (1 - |lam|) := by
  have hden : 0 < 1 - |lam| := by linarith
  calc
    ∑ k ∈ Finset.range (m + 1), |lam| ^ k * |1 - lam|
        = (∑ k ∈ Finset.range (m + 1), |lam| ^ k) * |1 - lam| := by
            rw [Finset.sum_mul]
    _ ≤ (1 / (1 - |lam|)) * |1 - lam| := by
            exact mul_le_mul_of_nonneg_right
              (geom_partial_sum_le |lam| (abs_nonneg lam) hLam m) (abs_nonneg _)
    _ = |1 - lam| / (1 - |lam|) := by
            rw [one_div, div_eq_mul_inv]
            ring

private theorem residual_term_entry_abs_le_of_real_diagonalization (n : ℕ)
    (H X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n H X) = J)
    (hdiag : ∀ i j, i ≠ j → J i j = 0)
    (k : ℕ) (i j : Fin n) :
    |matMul n (matPow n H k) (matSub_id n H) i j| ≤
      ∑ a : Fin n, |X i a| * (|J a a| ^ k * |1 - J a a|) * |X_inv a j| := by
  have hterm :
      matMul n (matPow n H k) (matSub_id n H) i j =
        matPow n H k i j - matPow n H (k + 1) i j := by
    unfold matMul matSub_id
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    have hid :
        (∑ l : Fin n, matPow n H k i l * idMatrix n l j) =
          matPow n H k i j := by
      unfold idMatrix
      simp [Finset.sum_ite_eq', Finset.mem_univ]
    have hmul :
        (∑ l : Fin n, matPow n H k i l * H l j) =
          matPow n H (k + 1) i j := by
      rw [matPow_succ_right n H k]
      rfl
    rw [hid, hmul]
  have hpow_entry :
      ∀ p (r c : Fin n),
        matPow n H p r c =
          ∑ a : Fin n, X r a * (J a a ^ p * X_inv a c) := by
    intro p r c
    have hpow := congrFun
      (congrFun (matPow_similarity n H X X_inv J hXr hXl hsim p) r) c
    rw [hpow]
    unfold matMul
    apply Finset.sum_congr rfl
    intro a _ha
    congr 1
    have hinner :
        (∑ b : Fin n, matPow n J p a b * X_inv b c) =
          J a a ^ p * X_inv a c := by
      rw [Finset.sum_eq_single a]
      · rw [matPow_diagonal n J hdiag p a a, if_pos rfl]
      · intro b _hb hba
        rw [matPow_diagonal n J hdiag p a b, if_neg (Ne.symm hba), zero_mul]
      · intro hnot
        exact absurd (Finset.mem_univ a) hnot
    exact hinner
  have hsource :
      matMul n (matPow n H k) (matSub_id n H) i j =
        ∑ a : Fin n, X i a * (J a a ^ k * (1 - J a a) * X_inv a j) := by
    rw [hterm, hpow_entry k i j, hpow_entry (k + 1) i j]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _ha
    rw [pow_succ]
    ring
  rw [hsource]
  calc
    |∑ a : Fin n, X i a * (J a a ^ k * (1 - J a a) * X_inv a j)|
        ≤ ∑ a : Fin n, |X i a * (J a a ^ k * (1 - J a a) * X_inv a j)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a : Fin n,
          |X i a| * (|J a a| ^ k * |1 - J a a|) * |X_inv a j| := by
          apply Finset.sum_congr rfl
          intro a _ha
          rw [abs_mul, abs_mul, abs_mul, abs_pow]
          ring

/-- Higham, 2nd ed., Chapter 17, Section 17.3, equation (17.20), finite
    diagonalization-certificate form: if `H = X J X^{-1}` with diagonal `J`
    and `|lambda_i| < 1`, then every finite source-sigma partial matrix is
    bounded by `kappa_infty(X) * max_i |1-lambda_i|/(1-|lambda_i|)`.

    The theorem takes the displayed maximum as an explicit scalar upper bound
    `sigmaDiag`; the literal infinite-series sigma is still a later wrapper. -/
theorem finiteResidualSigma_le_diagonalizable_bound (n : ℕ) (_hn : 0 < n)
    (H X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n H X) = J)
    (hdiag : ∀ i j, i ≠ j → J i j = 0)
    (sigmaDiag : ℝ) (hsigma : 0 ≤ sigmaDiag)
    (hLam : ∀ i : Fin n, |J i i| < 1)
    (hratio : ∀ i : Fin n, |1 - J i i| / (1 - |J i i|) ≤ sigmaDiag)
    (m : ℕ) :
    finiteResidualSigma n H m ≤ (infNorm X * infNorm X_inv) * sigmaDiag := by
  unfold finiteResidualSigma
  apply infNorm_le_of_row_sum_le
  · intro i
    have hrowEntry_nonneg :
        ∀ j : Fin n, 0 ≤ finiteResidualSigmaMatrix n H m i j := by
      intro j
      unfold finiteResidualSigmaMatrix
      exact Finset.sum_nonneg (fun k _hk => abs_nonneg _)
    calc
      ∑ j : Fin n, |finiteResidualSigmaMatrix n H m i j|
          = ∑ j : Fin n, finiteResidualSigmaMatrix n H m i j := by
              apply Finset.sum_congr rfl
              intro j _hj
              exact abs_of_nonneg (hrowEntry_nonneg j)
      _ = ∑ j : Fin n, ∑ k ∈ Finset.range (m + 1),
            |matMul n (matPow n H k) (matSub_id n H) i j| := by
              rfl
      _ ≤ ∑ j : Fin n, ∑ a : Fin n,
            |X i a| * sigmaDiag * |X_inv a j| := by
              apply Finset.sum_le_sum
              intro j _hj
              calc
                ∑ k ∈ Finset.range (m + 1),
                    |matMul n (matPow n H k) (matSub_id n H) i j|
                    ≤ ∑ k ∈ Finset.range (m + 1), ∑ a : Fin n,
                        |X i a| * (|J a a| ^ k * |1 - J a a|) *
                          |X_inv a j| := by
                        apply Finset.sum_le_sum
                        intro k _hk
                        exact residual_term_entry_abs_le_of_real_diagonalization
                          n H X X_inv J hXr hXl hsim hdiag k i j
                _ = ∑ a : Fin n, ∑ k ∈ Finset.range (m + 1),
                        |X i a| * (|J a a| ^ k * |1 - J a a|) *
                          |X_inv a j| := by
                        rw [Finset.sum_comm]
                _ ≤ ∑ a : Fin n, |X i a| * sigmaDiag * |X_inv a j| := by
                        apply Finset.sum_le_sum
                        intro a _ha
                        have hgeom :
                            ∑ k ∈ Finset.range (m + 1),
                              |J a a| ^ k * |1 - J a a| ≤ sigmaDiag :=
                            (residual_geometric_partial_le_ratio (J a a)
                            (hLam a) m).trans (hratio a)
                        calc
                          ∑ k ∈ Finset.range (m + 1),
                              |X i a| * (|J a a| ^ k * |1 - J a a|) *
                                |X_inv a j|
                              = |X i a| *
                                  (∑ k ∈ Finset.range (m + 1),
                                    |J a a| ^ k * |1 - J a a|) *
                                  |X_inv a j| := by
                                  rw [Finset.mul_sum, Finset.sum_mul]
                          _ ≤ |X i a| * sigmaDiag * |X_inv a j| := by
                                  exact mul_le_mul_of_nonneg_right
                                    (mul_le_mul_of_nonneg_left hgeom (abs_nonneg _))
                                    (abs_nonneg _)
      _ = ∑ a : Fin n, |X i a| * sigmaDiag * (∑ j : Fin n, |X_inv a j|) := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro a _ha
              rw [← Finset.mul_sum]
      _ ≤ ∑ a : Fin n, |X i a| * sigmaDiag * infNorm X_inv := by
              apply Finset.sum_le_sum
              intro a _ha
              exact mul_le_mul_of_nonneg_left
                (row_sum_le_infNorm X_inv a)
                (mul_nonneg (abs_nonneg _) hsigma)
      _ = sigmaDiag * infNorm X_inv * (∑ a : Fin n, |X i a|) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro a _ha
              ring
      _ ≤ sigmaDiag * infNorm X_inv * infNorm X := by
              exact mul_le_mul_of_nonneg_left
                (row_sum_le_infNorm X i)
                (mul_nonneg hsigma (infNorm_nonneg _))
      _ = (infNorm X * infNorm X_inv) * sigmaDiag := by
              ring
  · exact mul_nonneg (mul_nonneg (infNorm_nonneg X) (infNorm_nonneg X_inv)) hsigma

/-- Higham, 2nd ed., Chapter 17, Section 17.3, equation (17.20), finite
    maximum form: if `H = X J X^{-1}` with diagonal `J` and `|lambda_i| < 1`,
    then every finite source-sigma partial norm is bounded by
    `kappa_infty(X)` times the displayed maximum eigenvalue ratio. -/
theorem finiteResidualSigma_le_diagonalizable_max_bound (n : ℕ) (hn : 0 < n)
    (H X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n H X) = J)
    (hdiag : ∀ i j, i ≠ j → J i j = 0)
    (hLam : ∀ i : Fin n, |J i i| < 1)
    (m : ℕ) :
    finiteResidualSigma n H m ≤
      (infNorm X * infNorm X_inv) * diagonalResidualRatioMax n J hn := by
  exact finiteResidualSigma_le_diagonalizable_bound n hn H X X_inv J
    hXr hXl hsim hdiag (diagonalResidualRatioMax n J hn)
    (diagonalResidualRatioMax_nonneg n J hn hLam) hLam
    (diagonalResidualRatio_le_max n J hn) m

private theorem residualSigmaTsum_entry_le_of_real_diagonalization (n : ℕ)
    (H X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n H X) = J)
    (hdiag : ∀ i j, i ≠ j → J i j = 0)
    (sigmaDiag : ℝ)
    (hLam : ∀ i : Fin n, |J i i| < 1)
    (hratio : ∀ i : Fin n, |1 - J i i| / (1 - |J i i|) ≤ sigmaDiag)
    (i j : Fin n) :
    residualSigmaTsumMatrix n H i j ≤
      ∑ a : Fin n, |X i a| * sigmaDiag * |X_inv a j| := by
  let f : ℕ → ℝ :=
    fun k => |matMul n (matPow n H k) (matSub_id n H) i j|
  let g : ℕ → ℝ :=
    fun k => ∑ a : Fin n,
      |X i a| * (|J a a| ^ k * |1 - J a a|) * |X_inv a j|
  have hfg : ∀ k : ℕ, f k ≤ g k := by
    intro k
    simpa [f, g] using
      residual_term_entry_abs_le_of_real_diagonalization
        n H X X_inv J hXr hXl hsim hdiag k i j
  have hg_a : ∀ a : Fin n,
      Summable (fun k : ℕ =>
        |X i a| * (|J a a| ^ k * |1 - J a a|) * |X_inv a j|) := by
    intro a
    have hgeom : Summable (fun k : ℕ => |J a a| ^ k) :=
      summable_geometric_of_lt_one (abs_nonneg _) (hLam a)
    have hscaled :
        Summable (fun k : ℕ => |J a a| ^ k * |1 - J a a|) :=
      Summable.mul_right _ hgeom
    have hleft :
        Summable (fun k : ℕ =>
          |X i a| * (|J a a| ^ k * |1 - J a a|)) :=
      Summable.mul_left _ hscaled
    exact Summable.mul_right _ hleft
  have hg : Summable g := by
    dsimp [g]
    simpa using
      (summable_sum (s := Finset.univ)
        (fun a _ha => hg_a a))
  have hf : Summable f :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) hfg hg
  have hle_tsum : (∑' k : ℕ, f k) ≤ ∑' k : ℕ, g k :=
    Summable.tsum_le_tsum hfg hf hg
  have hg_tsum_eq :
      (∑' k : ℕ, g k) =
        ∑ a : Fin n, ∑' k : ℕ,
          |X i a| * (|J a a| ^ k * |1 - J a a|) * |X_inv a j| := by
    dsimp [g]
    simpa using
      (Summable.tsum_finsetSum (s := Finset.univ)
        (fun a _ha => hg_a a))
  have hg_tsum_le :
      (∑' k : ℕ, g k) ≤
        ∑ a : Fin n, |X i a| * sigmaDiag * |X_inv a j| := by
    rw [hg_tsum_eq]
    apply Finset.sum_le_sum
    intro a _ha
    have hgeom_tsum :
        (∑' k : ℕ, |J a a| ^ k * |1 - J a a|) =
          |1 - J a a| / (1 - |J a a|) := by
      rw [tsum_mul_right, tsum_geometric_of_lt_one (abs_nonneg _) (hLam a)]
      rw [div_eq_mul_inv, mul_comm]
    have hweighted_tsum :
        (∑' k : ℕ,
          |X i a| * (|J a a| ^ k * |1 - J a a|) * |X_inv a j|) =
          |X i a| * (|1 - J a a| / (1 - |J a a|)) * |X_inv a j| := by
      rw [tsum_mul_right, tsum_mul_left, hgeom_tsum]
    rw [hweighted_tsum]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hratio a) (abs_nonneg _))
      (abs_nonneg _)
  calc
    residualSigmaTsumMatrix n H i j = ∑' k : ℕ, f k := by rfl
    _ ≤ ∑' k : ℕ, g k := hle_tsum
    _ ≤ ∑ a : Fin n, |X i a| * sigmaDiag * |X_inv a j| := hg_tsum_le

/-- Higham, 2nd ed., Chapter 17, Section 17.3, equation (17.20), literal
    `tsum` diagonalization-certificate form: if `H = X J X^{-1}` with diagonal
    `J` and `|lambda_i| < 1`, then the entrywise infinite source residual sigma
    is bounded by `kappa_infty(X) * sigmaDiag`. -/
theorem residualSigmaTsum_le_diagonalizable_bound (n : ℕ) (_hn : 0 < n)
    (H X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n H X) = J)
    (hdiag : ∀ i j, i ≠ j → J i j = 0)
    (sigmaDiag : ℝ) (hsigma : 0 ≤ sigmaDiag)
    (hLam : ∀ i : Fin n, |J i i| < 1)
    (hratio : ∀ i : Fin n, |1 - J i i| / (1 - |J i i|) ≤ sigmaDiag) :
    residualSigmaTsum n H ≤ (infNorm X * infNorm X_inv) * sigmaDiag := by
  apply residualSigmaTsum_le_of_row_sum_le
  · intro i
    have hentry_nonneg :
        ∀ j : Fin n, 0 ≤ residualSigmaTsumMatrix n H i j := by
      intro j
      unfold residualSigmaTsumMatrix
      exact tsum_nonneg (fun k => abs_nonneg _)
    calc
      ∑ j : Fin n, |residualSigmaTsumMatrix n H i j|
          = ∑ j : Fin n, residualSigmaTsumMatrix n H i j := by
              apply Finset.sum_congr rfl
              intro j _hj
              exact abs_of_nonneg (hentry_nonneg j)
      _ ≤ ∑ j : Fin n, ∑ a : Fin n,
            |X i a| * sigmaDiag * |X_inv a j| := by
              apply Finset.sum_le_sum
              intro j _hj
              exact residualSigmaTsum_entry_le_of_real_diagonalization
                n H X X_inv J hXr hXl hsim hdiag sigmaDiag
                hLam hratio i j
      _ = ∑ a : Fin n, |X i a| * sigmaDiag *
            (∑ j : Fin n, |X_inv a j|) := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro a _ha
              rw [← Finset.mul_sum]
      _ ≤ ∑ a : Fin n, |X i a| * sigmaDiag * infNorm X_inv := by
              apply Finset.sum_le_sum
              intro a _ha
              exact mul_le_mul_of_nonneg_left
                (row_sum_le_infNorm X_inv a)
                (mul_nonneg (abs_nonneg _) hsigma)
      _ = sigmaDiag * infNorm X_inv * (∑ a : Fin n, |X i a|) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro a _ha
              ring
      _ ≤ sigmaDiag * infNorm X_inv * infNorm X := by
              exact mul_le_mul_of_nonneg_left
                (row_sum_le_infNorm X i)
                (mul_nonneg hsigma (infNorm_nonneg _))
      _ = (infNorm X * infNorm X_inv) * sigmaDiag := by
              ring
  · exact mul_nonneg (mul_nonneg (infNorm_nonneg X) (infNorm_nonneg X_inv)) hsigma

/-- Higham, 2nd ed., Chapter 17, Section 17.3, equation (17.20), literal
    `tsum` maximum form: the entrywise infinite source residual sigma is bounded
    by `kappa_infty(X)` times the displayed maximum eigenvalue ratio. -/
theorem residualSigmaTsum_le_diagonalizable_max_bound_direct (n : ℕ) (hn : 0 < n)
    (H X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n H X) = J)
    (hdiag : ∀ i j, i ≠ j → J i j = 0)
    (hLam : ∀ i : Fin n, |J i i| < 1) :
    residualSigmaTsum n H ≤
      (infNorm X * infNorm X_inv) * diagonalResidualRatioMax n J hn := by
  exact residualSigmaTsum_le_diagonalizable_bound n hn H X X_inv J
    hXr hXl hsim hdiag (diagonalResidualRatioMax n J hn)
    (diagonalResidualRatioMax_nonneg n J hn hLam) hLam
    (diagonalResidualRatio_le_max n J hn)

/-- Higham, 2nd ed., Chapter 17, Section 17.3, equation (17.20), supremum
    wrapper: the supremum of all finite source-sigma partial norms is bounded by
    `kappa_infty(X)` times the displayed maximum eigenvalue ratio.  This is a
    source-facing infinite-sigma envelope, not a proof that an entrywise infinite
    matrix series has been constructed as a `tsum`. -/
theorem residualSigmaSup_le_diagonalizable_max_bound (n : ℕ) (hn : 0 < n)
    (H X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n H X) = J)
    (hdiag : ∀ i j, i ≠ j → J i j = 0)
    (hLam : ∀ i : Fin n, |J i i| < 1) :
    residualSigmaSup n H ≤
      (infNorm X * infNorm X_inv) * diagonalResidualRatioMax n J hn := by
  apply residualSigmaSup_le_of_finiteResidualSigma_le
  intro m
  exact finiteResidualSigma_le_diagonalizable_max_bound n hn H X X_inv J
    hXr hXl hsim hdiag hLam m

end NumStability
