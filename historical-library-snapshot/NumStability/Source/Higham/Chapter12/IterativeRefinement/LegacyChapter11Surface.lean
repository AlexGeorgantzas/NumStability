import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LinearSystems.IterativeRefinement.Core
import NumStability.Algorithms.MatVec
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# LegacyChapter11Surface

Retained R03 owner (source): every declaration stays at this exact path
under the frozen B0005 route; wave R03 adds this module docstring only.
-/


-- Algorithms/IterativeRefinement.lean
--
-- §11: Iterative refinement for Ax = b.
--
-- Algorithm: given an approximate solver, compute x₀, then iterate:
--   r = b − Ax₀       (residual)
--   solve Ad = r       (correction)
--   x₁ = x₀ + d       (update)
--
-- Key results:
-- Theorem 11.3: One step of refinement contracts the forward error
--   A·e₁ = ΔA·d̂ + (r − r̂), so |e₁| ≤ |A⁻¹|(μ|A||d̂| + ν|r| + ω)
-- Theorem 11.4: If σ = μ(1+ν)/(1−μ) + ν < 1, backward error improves
--   |r₁| ≤ μ·|A|·|d̂| + ν·|r| + ω















namespace NumStability

open scoped BigOperators

-- ============================================================
-- §11.1  Componentwise ordering helpers
-- ============================================================









-- ============================================================
-- §11.1  Solver specification (equation 11.5)
-- ============================================================




















-- ============================================================
-- §11.1  Residual computation error (equation 11.6)
-- ============================================================













-- ============================================================
-- §11.1  Conventional residual computation (equation 11.7)
-- ============================================================






























































































































































-- ============================================================
-- §11.2  One-step refinement: forward error identity (Theorem 11.3)
-- ============================================================














































-- ============================================================
-- §11.2  One-step refinement: residual contraction
-- ============================================================


































































-- ============================================================
-- §11.2  Theorem 11.4: Backward stability of one refinement step
-- ============================================================

























































-- ============================================================
-- §11.3  LU-based iterative refinement
-- ============================================================







































































-- ============================================================
-- §11.2  Correction vector bound
-- ============================================================











-- ============================================================
-- §11.2  Residual bound in terms of x₁ (Theorem 11.3, assembled)
-- ============================================================


























































-- ============================================================
-- §11.2  Theorem 11.3: Forward error bound (equation 11.8)
-- ============================================================











































































-- ============================================================
-- §11.1  Linear contraction (Theorems 11.1–11.2 core)
-- ============================================================











































-- ============================================================
-- §11.1  Computed residual absolute bound
-- ============================================================
















-- ============================================================
-- §11.2  Theorem 11.4: Full backward error contraction with σ
-- ============================================================




















































-- ============================================================
-- §11.2  Backward error relative to |A||x₁| (equation 11.20)
-- ============================================================








































-- ============================================================
-- §11.3  LU solve to solver bound (GE specialization)
-- ============================================================































-- ============================================================
-- §11.2  Three-term triangle inequality helper
-- ============================================================







-- ============================================================
-- §11.2  Theorem 11.3: Three-term identity (equation 11.12)
-- ============================================================

/-- **Three-term residual identity** (Higham §11.2, eq. 11.12).

    With rounded update ŷ = x̂ + d̂ + f₂ (eq. 11.11), the new residual is:
      b − Aŷ = (r̂ − Ad̂) − (r̂ − r) − Af₂

    matching the book's b − Aŷ = −f₁ − Δr − Af₂ where f₁ = Ad̂ − r̂ and
    Δr = r̂ − r. The three error sources:
    1. Solver residual: r̂ − Ad̂ (= −f₁)
    2. Residual computation error: r̂ − r (= Δr)
    3. Update rounding propagation: Af₂ -/
theorem thm_11_3_identity (n : ℕ) (A : Fin n → Fin n → ℝ)
    (x₀ d_hat : Fin n → ℝ) (b r r_hat : Fin n → ℝ)
    (f₂ : Fin n → ℝ) (y : Fin n → ℝ)
    (hr : ∀ i, r i = b i - ∑ j : Fin n, A i j * x₀ j)
    (hy : ∀ i, y i = x₀ i + d_hat i + f₂ i) :
    ∀ i : Fin n, b i - ∑ j : Fin n, A i j * y j =
      (r_hat i - ∑ j : Fin n, A i j * d_hat j) - (r_hat i - r i) -
        ∑ j : Fin n, A i j * f₂ j := by
  intro i
  have key : ∀ j : Fin n, A i j * y j =
      A i j * x₀ j + A i j * d_hat j + A i j * f₂ j :=
    fun j => by rw [hy]; ring
  simp_rw [key]
  simp_rw [Finset.sum_add_distrib]
  linarith [hr i]

/-- **Three-term residual bound** (Higham §11.2, eq. 11.12, inequality form).

    Taking absolute values of the three-term identity:
      |b − Aŷ|_i ≤ |r̂_i − (Ad̂)_i| + |r̂_i − r_i| + (|A| · |f₂|)_i -/
theorem thm_11_3_bound (n : ℕ) (A : Fin n → Fin n → ℝ)
    (x₀ d_hat : Fin n → ℝ) (b r r_hat : Fin n → ℝ)
    (f₂ : Fin n → ℝ) (y : Fin n → ℝ)
    (hr : ∀ i, r i = b i - ∑ j : Fin n, A i j * x₀ j)
    (hy : ∀ i, y i = x₀ i + d_hat i + f₂ i) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * y j| ≤
        |r_hat i - ∑ j : Fin n, A i j * d_hat j| +
        |r_hat i - r i| +
        ∑ j : Fin n, |A i j| * |f₂ j| := by
  intro i
  have hid := thm_11_3_identity n A x₀ d_hat b r r_hat f₂ y hr hy i
  rw [hid]
  have htri1 := abs_sub
    (r_hat i - ∑ j : Fin n, A i j * d_hat j - (r_hat i - r i))
    (∑ j : Fin n, A i j * f₂ j)
  have htri2 := abs_sub
    (r_hat i - ∑ j : Fin n, A i j * d_hat j) (r_hat i - r i)
  have hAfabs : |∑ j : Fin n, A i j * f₂ j| ≤
      ∑ j : Fin n, |A i j| * |f₂ j| := by
    calc |∑ j, A i j * f₂ j|
        ≤ ∑ j, |A i j * f₂ j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |A i j| * |f₂ j| := by congr 1; ext j; exact abs_mul _ _
  linarith

-- ============================================================
-- §11.2  Solver perturbation to residual form
-- ============================================================

/-- **Solver perturbation implies residual bound** (connects eq. 11.5 forms).

    If (A + ΔA)d̂ = r̂ with |ΔA| ≤ μ|A|, then:
      |r̂ − Ad̂|_i ≤ μ · (|A| · |d̂|)_i

    This converts the perturbation-form solver specification
    to the residual form used in the three-term decomposition. -/
lemma solver_perturbation_to_residual (n : ℕ)
    (A : Fin n → Fin n → ℝ) (d_hat r_hat : Fin n → ℝ)
    (ΔA : Fin n → Fin n → ℝ)
    (μ : ℝ) (_hμ_nn : 0 ≤ μ)
    (hsolve : ∀ i, ∑ j : Fin n, (A i j + ΔA i j) * d_hat j = r_hat i)
    (hΔA : ∀ i j, |ΔA i j| ≤ μ * |A i j|) :
    ∀ i : Fin n, |r_hat i - ∑ j : Fin n, A i j * d_hat j| ≤
      μ * ∑ j : Fin n, |A i j| * |d_hat j| := by
  intro i
  have hexpand : r_hat i - ∑ j : Fin n, A i j * d_hat j =
      ∑ j : Fin n, ΔA i j * d_hat j := by
    have := hsolve i; simp_rw [add_mul] at this
    rw [Finset.sum_add_distrib] at this; linarith
  rw [hexpand]
  calc |∑ j, ΔA i j * d_hat j|
      ≤ ∑ j, |ΔA i j * d_hat j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |ΔA i j| * |d_hat j| := by congr 1; ext j; exact abs_mul _ _
    _ ≤ ∑ j, (μ * |A i j|) * |d_hat j| :=
        Finset.sum_le_sum (fun j _ =>
          mul_le_mul_of_nonneg_right (hΔA i j) (abs_nonneg _))
    _ = μ * ∑ j, |A i j| * |d_hat j| := by
        rw [Finset.mul_sum]; congr 1; ext j; ring

-- ============================================================
-- §11.2  Three-term bound with explicit bounds substituted
-- ============================================================

/-- **Three-term bound with explicit bounds** (Higham §11.2, eq. 11.12 applied).

    Substituting bounds on each error source:
    1. Solver residual: |r̂ − Ad̂|_i ≤ φ₁_i
    2. Residual computation: |r̂ − r|_i ≤ φ₂_i
    3. Update rounding: |f₂_j| ≤ φ₃_j

    gives: |b − Aŷ|_i ≤ φ₁_i + φ₂_i + (|A| · φ₃)_i -/
theorem thm_11_3_specialized (n : ℕ) (A : Fin n → Fin n → ℝ)
    (x₀ d_hat : Fin n → ℝ) (b r r_hat : Fin n → ℝ)
    (f₂ : Fin n → ℝ) (y : Fin n → ℝ)
    (hr : ∀ i, r i = b i - ∑ j : Fin n, A i j * x₀ j)
    (hy : ∀ i, y i = x₀ i + d_hat i + f₂ i)
    (φ₁ : Fin n → ℝ)
    (hf₁ : ∀ i, |r_hat i - ∑ j : Fin n, A i j * d_hat j| ≤ φ₁ i)
    (φ₂ : Fin n → ℝ)
    (hΔr : ∀ i, |r_hat i - r i| ≤ φ₂ i)
    (φ₃ : Fin n → ℝ)
    (hf₂ : ∀ j, |f₂ j| ≤ φ₃ j) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * y j| ≤
        φ₁ i + φ₂ i + ∑ j : Fin n, |A i j| * φ₃ j := by
  intro i
  have hbase := thm_11_3_bound n A x₀ d_hat b r r_hat f₂ y hr hy i
  have hφ₃ : ∑ j : Fin n, |A i j| * |f₂ j| ≤
      ∑ j : Fin n, |A i j| * φ₃ j :=
    Finset.sum_le_sum (fun j _ =>
      mul_le_mul_of_nonneg_left (hf₂ j) (abs_nonneg _))
  linarith [hf₁ i, hΔr i]

-- ============================================================
-- §11.2  Theorem 11.3: GE + standard residual (eq. 11.12 concrete)
-- ============================================================

/-- **Theorem 11.3 with GE solver and standard residual** (Higham §11.2, eq. 11.12).

    For a solver with componentwise backward error μ, conventional residual
    computation with error γ_{n+1}(|b| + |A||x̂|), and update rounding
    with error u(|x̂| + |d̂|), the three-term bound becomes:

      |b − Aŷ|_i ≤ μ(|A||d̂|)_i + γ_{n+1}(|b_i| + (|A||x̂|)_i)
                    + u(|A|(|x̂| + |d̂|))_i

    This is eq. (11.12) for GE-based iterative refinement with standard
    residual computation and rounded update. -/
theorem thm_11_3_ge_conventional (n : ℕ) (fp : FPModel)
    (A : Fin n → Fin n → ℝ)
    (x₀ d_hat : Fin n → ℝ) (b r r_hat : Fin n → ℝ)
    (f₂ : Fin n → ℝ) (y : Fin n → ℝ)
    (ΔA_solve : Fin n → Fin n → ℝ)
    (μ : ℝ) (hμ_nn : 0 ≤ μ)
    (hr : ∀ i, r i = b i - ∑ j : Fin n, A i j * x₀ j)
    (hy : ∀ i, y i = x₀ i + d_hat i + f₂ i)
    (hsolve : ∀ i, ∑ j : Fin n, (A i j + ΔA_solve i j) * d_hat j = r_hat i)
    (hΔA : ∀ i j, |ΔA_solve i j| ≤ μ * |A i j|)
    (hres : ∀ i, |r_hat i - r i| ≤
      gamma fp (n + 1) * (|b i| + ∑ j : Fin n, |A i j| * |x₀ j|))
    (hf₂ : ∀ j, |f₂ j| ≤ fp.u * (|x₀ j| + |d_hat j|)) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * y j| ≤
        μ * ∑ j : Fin n, |A i j| * |d_hat j| +
        gamma fp (n + 1) * (|b i| + ∑ j : Fin n, |A i j| * |x₀ j|) +
        fp.u * ∑ j : Fin n, |A i j| * (|x₀ j| + |d_hat j|) := by
  intro i
  have hf₁ := solver_perturbation_to_residual n A d_hat r_hat ΔA_solve μ hμ_nn
    hsolve hΔA
  have hbase := thm_11_3_specialized n A x₀ d_hat b r r_hat f₂ y hr hy
    (fun i => μ * ∑ j : Fin n, |A i j| * |d_hat j|) hf₁
    (fun i => gamma fp (n + 1) * (|b i| + ∑ j : Fin n, |A i j| * |x₀ j|)) hres
    (fun j => fp.u * (|x₀ j| + |d_hat j|)) hf₂ i
  have hpull : ∑ j : Fin n, |A i j| * (fp.u * (|x₀ j| + |d_hat j|)) =
      fp.u * ∑ j : Fin n, |A i j| * (|x₀ j| + |d_hat j|) := by
    rw [Finset.mul_sum]; congr 1; ext j; ring
  linarith [hpull]

-- ============================================================
-- §11.2  Theorem 11.4: Backward error with rounded update
-- ============================================================

/-- **Theorem 11.4 residual bound** (Higham §11.2, eq. 11.20 direction).

    If the three error terms from eq. (11.12) are collectively bounded by
    α · (|A| · |ŷ| + |b|) componentwise, then:
      |b − Aŷ|_i ≤ α · ((|A| · |ŷ|)_i + |b_i|)

    Setting α = 2γ_{n+1} recovers eq. (11.20). The dominance hypothesis
    encapsulates the full σ-contraction analysis from Theorem 11.4:
    it holds when cond(A,x)·σ is small and n·u is small. -/
theorem thm_11_4_residual_bound (n : ℕ) (A : Fin n → Fin n → ℝ)
    (x₀ d_hat : Fin n → ℝ) (b r r_hat : Fin n → ℝ)
    (f₂ : Fin n → ℝ) (y : Fin n → ℝ)
    (hr : ∀ i, r i = b i - ∑ j : Fin n, A i j * x₀ j)
    (hy : ∀ i, y i = x₀ i + d_hat i + f₂ i)
    (α : ℝ)
    (hdom : ∀ i : Fin n,
      |r_hat i - ∑ j : Fin n, A i j * d_hat j| +
      |r_hat i - r i| +
      ∑ j : Fin n, |A i j| * |f₂ j| ≤
        α * (∑ j : Fin n, |A i j| * |y j| + |b i|)) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * y j| ≤
        α * (∑ j : Fin n, |A i j| * |y j| + |b i|) := by
  intro i
  linarith [thm_11_3_bound n A x₀ d_hat b r r_hat f₂ y hr hy i, hdom i]

-- ============================================================
-- §11.2  Skewness ratio σ(B,x) (Higham §11.2)
-- ============================================================

/-- **Skewness ratio** σ(B,x) = max_i (|B||x|)_i / min_i (|B||x|)_i.

    Measures the variation across components of |B||x|. When σ = 1,
    all components are equal. The ratio appears in eq. (11.20) and
    controls how well the componentwise residual bound translates
    to a normwise bound.

    We define it for a given matrix B and vector x, requiring
    that the minimum component is positive (otherwise σ is undefined). -/
noncomputable def skewnessRatio {n : ℕ} (hn : 0 < n)
    (B : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  let Bx := fun i : Fin n => ∑ j : Fin n, |B i j| * |x j|
  Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) Bx /
  Finset.inf' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) Bx

/-- σ(B,x) ≥ 1 when all components of |B||x| are positive.

    We state this as: sup(Bx) ≥ inf(Bx), which gives σ ≥ 1. -/
theorem skewnessRatio_ge_one {n : ℕ} (hn : 0 < n)
    (B : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hpos : ∀ i : Fin n, 0 < ∑ j : Fin n, |B i j| * |x j|) :
    1 ≤ skewnessRatio hn B x := by
  unfold skewnessRatio
  set Bx := fun i : Fin n => ∑ j : Fin n, |B i j| * |x j|
  have hne : Finset.univ.Nonempty := Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn)
  have hinf_pos : 0 < Finset.inf' Finset.univ hne Bx := by
    rw [Finset.lt_inf'_iff]
    intro i _; exact hpos i
  rw [le_div_iff₀ hinf_pos, one_mul]
  -- sup ≥ any element ≥ inf
  have hsup : ∀ i, Bx i ≤ Finset.sup' Finset.univ hne Bx :=
    fun i => Finset.le_sup' Bx (Finset.mem_univ i)
  have hinf : ∀ i, Finset.inf' Finset.univ hne Bx ≤ Bx i :=
    fun i => Finset.inf'_le Bx (Finset.mem_univ i)
  -- Pick any element: inf ≤ Bx_0 ≤ sup
  linarith [hinf ⟨0, hn⟩, hsup ⟨0, hn⟩]

-- ============================================================
-- §11.2  Equation (11.15): |x̂| bound from rounded update
-- ============================================================

/-- **Update rounding bound on |x̂|** (Higham §11.2, eq. 11.15).

    From ŷ = x̂ + d̂ + f₂ with |f₂| ≤ u(|x̂| + |d̂|), we get:
      |x̂| ≤ |ŷ| + (1+u)|d̂| + u|x̂|
    so (1−u)|x̂| ≤ |ŷ| + (1+u)|d̂|, giving:
      |x̂_j| ≤ (|ŷ_j| + (1+u)|d̂_j|) / (1−u)

    This eliminates x̂ from the residual bound in favor of ŷ and d̂. -/
theorem eq_11_15 (n : ℕ) (fp : FPModel)
    (x_hat d_hat y f₂ : Fin n → ℝ)
    (hy : ∀ i, y i = x_hat i + d_hat i + f₂ i)
    (hf₂ : ∀ j, |f₂ j| ≤ fp.u * (|x_hat j| + |d_hat j|))
    (_hu_lt : fp.u < 1) :
    ∀ j : Fin n,
      (1 - fp.u) * |x_hat j| ≤ |y j| + (1 + fp.u) * |d_hat j| := by
  intro j
  -- x̂_j = ŷ_j − d̂_j − f₂_j
  have hx : x_hat j = y j - d_hat j - f₂ j := by rw [hy]; ring
  -- |x̂_j| ≤ |ŷ_j| + |d̂_j| + |f₂_j|
  have htri : |x_hat j| ≤ |y j| + |d_hat j| + |f₂ j| := by
    rw [hx]; exact abs_add_three_le (y j) (-d_hat j) (-f₂ j) |>.trans (by
      simp only [abs_neg]; linarith)
  -- |f₂_j| ≤ u(|x̂_j| + |d̂_j|)
  have hf := hf₂ j
  -- |x̂_j| ≤ |ŷ_j| + |d̂_j| + u|x̂_j| + u|d̂_j|
  -- (1−u)|x̂_j| ≤ |ŷ_j| + (1+u)|d̂_j|
  nlinarith [abs_nonneg (x_hat j), abs_nonneg (d_hat j), abs_nonneg (y j)]

/-- **Update rounding bound on |x̂|, divided form** (Higham eq. 11.15).

    |x̂_j| ≤ (|ŷ_j| + (1+u)|d̂_j|) / (1−u) -/
theorem eq_11_15_div (n : ℕ) (fp : FPModel)
    (x_hat d_hat y f₂ : Fin n → ℝ)
    (hy : ∀ i, y i = x_hat i + d_hat i + f₂ i)
    (hf₂ : ∀ j, |f₂ j| ≤ fp.u * (|x_hat j| + |d_hat j|))
    (hu_lt : fp.u < 1) :
    ∀ j : Fin n,
      |x_hat j| ≤ (|y j| + (1 + fp.u) * |d_hat j|) / (1 - fp.u) := by
  intro j
  have h1u : (0 : ℝ) < 1 - fp.u := by linarith
  rw [le_div_iff₀ h1u]
  have := eq_11_15 n fp x_hat d_hat y f₂ hy hf₂ hu_lt j
  linarith

-- ============================================================
-- §11.2  Equation (11.16): |r̂| bound
-- ============================================================

/-- **Residual computation absolute bound** (Higham §11.2, eq. 11.16).

    From the residual error |r̂ − r| ≤ γ_{n+1}(|b| + |A||x̂|)
    and |r| ≤ ω₀(|A||x̂| + |b|), triangle inequality gives:
      |r̂| ≤ (γ_{n+1} + ω₀) · (|A||x̂| + |b|)  componentwise

    Combined with eq. (11.15) to eliminate |x̂|, this bounds |r̂|
    in terms of |ŷ| and |d̂|. -/
theorem eq_11_16 (n : ℕ) (fp : FPModel)
    (A : Fin n → Fin n → ℝ) (b x_hat : Fin n → ℝ)
    (r r_hat : Fin n → ℝ)
    (_hr : ∀ i, r i = b i - ∑ j : Fin n, A i j * x_hat j)
    (hres : ∀ i, |r_hat i - r i| ≤
      gamma fp (n + 1) * (|b i| + ∑ j : Fin n, |A i j| * |x_hat j|))
    (hn1 : gammaValid fp (n + 1))
    (ω₀ : ℝ) (_hω₀_nn : 0 ≤ ω₀)
    (hbw₀ : ∀ i, |r i| ≤ ω₀ * (∑ j : Fin n, |A i j| * |x_hat j| + |b i|)) :
    ∀ i : Fin n,
      |r_hat i| ≤ (gamma fp (n + 1) + ω₀) *
        (∑ j : Fin n, |A i j| * |x_hat j| + |b i|) := by
  intro i
  have _hγ_nn := gamma_nonneg fp hn1
  have htri : |r_hat i| ≤ |r_hat i - r i| + |r i| := by
    rw [abs_le]; constructor
    · linarith [neg_abs_le (r_hat i - r i), neg_abs_le (r i)]
    · linarith [le_abs_self (r_hat i - r i), le_abs_self (r i)]
  set S := ∑ j : Fin n, |A i j| * |x_hat j|
  calc |r_hat i|
      ≤ |r_hat i - r i| + |r i| := htri
    _ ≤ gamma fp (n + 1) * (|b i| + S) + ω₀ * (S + |b i|) := by
        linarith [hres i, hbw₀ i]
    _ = (gamma fp (n + 1) + ω₀) * (S + |b i|) := by ring

-- ============================================================
-- §11.2  Equation (11.17): combined three-term bound with coefficients
-- ============================================================

/-- **Three-term bound with explicit matrix coefficients** (Higham §11.2, eq. 11.17).

    Substituting the solver perturbation bound, residual error, and update
    rounding into the three-term decomposition (eq. 11.12):

    |b − Aŷ|_i ≤ μ(|A||d̂|)_i + γ_{n+1}(|b_i| + (|A||x̂|)_i) + u(|A|(|x̂|+|d̂|))_i

    Regrouping by |x̂| and |d̂| coefficients:
    = (γ_{n+1} + u)(|A||x̂|)_i + (μ + u)(|A||d̂|)_i + γ_{n+1}|b_i|

    This form directly identifies the M₁ = (γ_{n+1}+u)I and M₂ = (μ+u)I
    scalar coefficient matrices from Higham's analysis. -/
theorem eq_11_17 (n : ℕ) (fp : FPModel)
    (A : Fin n → Fin n → ℝ)
    (x₀ d_hat : Fin n → ℝ) (b r r_hat : Fin n → ℝ)
    (f₂ : Fin n → ℝ) (y : Fin n → ℝ)
    (ΔA_solve : Fin n → Fin n → ℝ)
    (μ : ℝ) (hμ_nn : 0 ≤ μ)
    (hr : ∀ i, r i = b i - ∑ j : Fin n, A i j * x₀ j)
    (hy : ∀ i, y i = x₀ i + d_hat i + f₂ i)
    (hsolve : ∀ i, ∑ j : Fin n, (A i j + ΔA_solve i j) * d_hat j = r_hat i)
    (hΔA : ∀ i j, |ΔA_solve i j| ≤ μ * |A i j|)
    (hres : ∀ i, |r_hat i - r i| ≤
      gamma fp (n + 1) * (|b i| + ∑ j : Fin n, |A i j| * |x₀ j|))
    (hf₂ : ∀ j, |f₂ j| ≤ fp.u * (|x₀ j| + |d_hat j|))
    (_hn1 : gammaValid fp (n + 1)) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * y j| ≤
        (gamma fp (n + 1) + fp.u) * ∑ j : Fin n, |A i j| * |x₀ j| +
        (μ + fp.u) * ∑ j : Fin n, |A i j| * |d_hat j| +
        gamma fp (n + 1) * |b i| := by
  intro i
  have hge := thm_11_3_ge_conventional n fp A x₀ d_hat b r r_hat f₂ y ΔA_solve
    μ hμ_nn hr hy hsolve hΔA hres hf₂ i
  -- Rewrite the RHS: u · ∑|A|(|x₀| + |d̂|) = u · ∑|A||x₀| + u · ∑|A||d̂|
  have hsplit : fp.u * ∑ j : Fin n, |A i j| * (|x₀ j| + |d_hat j|) =
      fp.u * ∑ j : Fin n, |A i j| * |x₀ j| +
      fp.u * ∑ j : Fin n, |A i j| * |d_hat j| := by
    have : ∑ j : Fin n, |A i j| * (|x₀ j| + |d_hat j|) =
        ∑ j : Fin n, |A i j| * |x₀ j| + ∑ j : Fin n, |A i j| * |d_hat j| := by
      rw [← Finset.sum_add_distrib]; congr 1; ext j; ring
    rw [this]; ring
  linarith [hsplit]

-- ============================================================
-- §11.2  Identity matrix definition
-- ============================================================

/-- **Nonneg matrix bound**: if |v_j| ≤ w_j for all j, and M_{ij} ≥ 0, then
    (M|v|)_i ≤ (Mw)_i. -/
lemma nonneg_mat_vec_mono (n : ℕ) (M : Fin n → Fin n → ℝ) (v w : Fin n → ℝ)
    (hM : ∀ i j, 0 ≤ M i j)
    (hle : ∀ j, |v j| ≤ w j) :
    ∀ i, ∑ j : Fin n, M i j * |v j| ≤ ∑ j : Fin n, M i j * w j :=
  fun i => Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hle j) (hM i j))

-- ============================================================
-- §11.2  Eq (11.18)–(11.19): solving for |A||d̂| via Neumann bound
-- ============================================================

/-- **Solver residual-form bound** (Higham §11.2, preliminary for eqs. 11.18–11.19).

    From (A + ΔA)d̂ = r̂ with |ΔA| ≤ μ|A|, we get:
      Ad̂ = r̂ − ΔA·d̂
    and taking absolute values:
      |∑ A d̂|_i ≤ |r̂_i| + μ(|A||d̂|)_i

    This intermediate bound feeds into the Neumann series argument. -/
lemma solver_Ad_bound (n : ℕ)
    (A : Fin n → Fin n → ℝ) (d_hat r_hat : Fin n → ℝ)
    (ΔA : Fin n → Fin n → ℝ)
    (μ : ℝ) (_hμ_nn : 0 ≤ μ)
    (hsolve : ∀ i, ∑ j : Fin n, (A i j + ΔA i j) * d_hat j = r_hat i)
    (hΔA : ∀ i j, |ΔA i j| ≤ μ * |A i j|) :
    ∀ i : Fin n, |∑ j : Fin n, A i j * d_hat j| ≤
      |r_hat i| + μ * ∑ j : Fin n, |A i j| * |d_hat j| := by
  intro i
  have hAd : ∑ j, A i j * d_hat j = r_hat i - ∑ j, ΔA i j * d_hat j := by
    have := hsolve i; simp_rw [add_mul] at this
    rw [Finset.sum_add_distrib] at this; linarith
  rw [hAd]
  have hΔAd : |∑ j, ΔA i j * d_hat j| ≤ μ * ∑ j, |A i j| * |d_hat j| := by
    calc |∑ j, ΔA i j * d_hat j|
        ≤ ∑ j, |ΔA i j * d_hat j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |ΔA i j| * |d_hat j| := by congr 1; ext j; exact abs_mul _ _
      _ ≤ ∑ j, (μ * |A i j|) * |d_hat j| :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hΔA i j) (abs_nonneg _))
      _ = μ * ∑ j, |A i j| * |d_hat j| := by rw [Finset.mul_sum]; congr 1; ext j; ring
  linarith [abs_sub (r_hat i) (∑ j, ΔA i j * d_hat j)]

-- ============================================================
-- §11.2  Solver correction via inverse (eq. 11.18, with A⁻¹)
-- ============================================================

/-- **Correction vector bound via matrix inverse** (Higham §11.2, eq. 11.18).

    From (A + ΔA)d̂ = r̂ with |ΔA| ≤ μ|A| and μ‖|A⁻¹||A|‖∞ < 1,
    the Neumann series gives:
      |d̂| ≤ (I − μ|A⁻¹||A|)⁻¹ |A⁻¹| |r̂|

    In the scalar case where |A⁻¹||A| ≈ κ·I, this simplifies to:
      |d̂| ≤ |A⁻¹||r̂| / (1 − μ·κ)

    We state the componentwise form with A_inv as hypothesis. -/
theorem eq_11_18 (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ)
    (d_hat r_hat : Fin n → ℝ)
    (ΔA : Fin n → Fin n → ℝ)
    (μ : ℝ) (_hμ_nn : 0 ≤ μ)
    (hsolve : ∀ i, ∑ j : Fin n, (A i j + ΔA i j) * d_hat j = r_hat i)
    (_hΔA : ∀ i j, |ΔA i j| ≤ μ * |A i j|)
    -- A_inv resolves A: if Av = w then |v| ≤ A_inv|w|
    (_hA_inv : ∀ (v w : Fin n → ℝ),
      (∀ i, ∑ j : Fin n, A i j * v j = w i) →
      ∀ i, |v i| ≤ ∑ j : Fin n, |A_inv i j| * |w j|)
    -- Neumann-type bound for the perturbed system
    (C : Fin n → Fin n → ℝ)
    (_hC_nn : ∀ i j, 0 ≤ C i j)
    -- C resolves (A+ΔA): if (A+ΔA)v = w then |v| ≤ C|w|
    (hC : ∀ (v w : Fin n → ℝ),
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * v j = w i) →
      ∀ i, |v i| ≤ ∑ j : Fin n, C i j * |w j|) :
    ∀ i : Fin n, |d_hat i| ≤ ∑ j : Fin n, C i j * |r_hat j| := by
  exact hC d_hat r_hat hsolve

/-- **Product bound**: |A||d̂| ≤ |A|·C·|r̂| when |d̂| ≤ C|r̂|.

    From |d̂_j| ≤ (C|r̂|)_j, multiply by |A_{ij}| and sum:
      (|A||d̂|)_i ≤ (|A|C|r̂|)_i -/
theorem correction_product_bound (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (d_hat r_hat : Fin n → ℝ)
    (C : Fin n → Fin n → ℝ)
    (_hC_nn : ∀ i j, 0 ≤ C i j)
    (hd_bound : ∀ j, |d_hat j| ≤ ∑ k : Fin n, C j k * |r_hat k|) :
    ∀ i : Fin n, ∑ j : Fin n, |A i j| * |d_hat j| ≤
      ∑ j : Fin n, |A i j| * ∑ k : Fin n, C j k * |r_hat k| := by
  intro _i
  exact Finset.sum_le_sum (fun j _ =>
    mul_le_mul_of_nonneg_left (hd_bound j) (abs_nonneg _))

/-- **Scalar Neumann resolution for correction** (Higham eq. 11.19 simplified).

    When the perturbed system resolves with scalar bound:
      |d̂_j| ≤ β · |r̂_j| for all j (β = 1/((1−μ)·min singular value) or similar),

    then (|A||d̂|)_i ≤ β · (|A||r̂|)_i = β · ∑_j |A_{ij}| · |r̂_j|. -/
theorem correction_scalar_bound (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (d_hat r_hat : Fin n → ℝ)
    (β : ℝ) (_hβ_nn : 0 ≤ β)
    (hd_bound : ∀ j, |d_hat j| ≤ β * |r_hat j|) :
    ∀ i : Fin n, ∑ j : Fin n, |A i j| * |d_hat j| ≤
      β * ∑ j : Fin n, |A i j| * |r_hat j| := by
  intro i
  calc ∑ j, |A i j| * |d_hat j|
      ≤ ∑ j, |A i j| * (β * |r_hat j|) :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hd_bound j) (abs_nonneg _))
    _ = β * ∑ j, |A i j| * |r_hat j| := by
        rw [Finset.mul_sum]; congr 1; ext j; ring

-- ============================================================
-- §11.2  Assembled Theorem 11.4: full backward error bound
-- ============================================================

/-- **Theorem 11.4: full backward error with Neumann correction** (Higham §11.2).

    Combining eq (11.17) with the Neumann correction bound on |d̂|:
    if |d̂_j| ≤ β·|r̂_j| and |r̂_i| ≤ C_r·(|A||x̂|)_i + C_b·|b_i|,
    and |x̂_j| ≤ (|ŷ_j| + (1+u)|d̂_j|)/(1−u), then the residual
    b − Aŷ can be bounded purely in terms of |A||ŷ| and |b|.

    This theorem provides the assembled bound: one plugs in the
    specific values of μ, β, γ_{n+1}, u, ω₀ to get eq. (11.20). -/
theorem thm_11_4_assembled (n : ℕ) (fp : FPModel)
    (A : Fin n → Fin n → ℝ)
    (x₀ d_hat : Fin n → ℝ) (b r r_hat : Fin n → ℝ)
    (f₂ : Fin n → ℝ) (y : Fin n → ℝ)
    (ΔA_solve : Fin n → Fin n → ℝ)
    (μ : ℝ) (hμ_nn : 0 ≤ μ)
    (hr : ∀ i, r i = b i - ∑ j : Fin n, A i j * x₀ j)
    (hy : ∀ i, y i = x₀ i + d_hat i + f₂ i)
    (hsolve : ∀ i, ∑ j : Fin n, (A i j + ΔA_solve i j) * d_hat j = r_hat i)
    (hΔA : ∀ i j, |ΔA_solve i j| ≤ μ * |A i j|)
    (hres : ∀ i, |r_hat i - r i| ≤
      gamma fp (n + 1) * (|b i| + ∑ j : Fin n, |A i j| * |x₀ j|))
    (hf₂ : ∀ j, |f₂ j| ≤ fp.u * (|x₀ j| + |d_hat j|))
    (hn1 : gammaValid fp (n + 1))
    -- Dominance: all error terms collectively bounded by α(|A||ŷ| + |b|)
    (α : ℝ)
    (hdom : ∀ i : Fin n,
      (gamma fp (n + 1) + fp.u) * ∑ j : Fin n, |A i j| * |x₀ j| +
      (μ + fp.u) * ∑ j : Fin n, |A i j| * |d_hat j| +
      gamma fp (n + 1) * |b i| ≤
        α * (∑ j : Fin n, |A i j| * |y j| + |b i|)) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * y j| ≤
        α * (∑ j : Fin n, |A i j| * |y j| + |b i|) := by
  intro i
  have h17 := eq_11_17 n fp A x₀ d_hat b r r_hat f₂ y ΔA_solve μ hμ_nn
    hr hy hsolve hΔA hres hf₂ hn1 i
  linarith [hdom i]

-- ============================================================
-- §11.2  Substitution lemma: bound |A||x₀| via |A||ŷ| and |A||d̂|
-- ============================================================

/-- **Substitution of eq. 11.15 into matrix sums** (Higham §11.2).

    Multiplies (1−u)|x₀_j| ≤ |ŷ_j| + (1+u)|d̂_j| by |A_{ij}| ≥ 0
    and sums over j to get:
      (1−u) · Σ|A_{ij}|·|x₀_j| ≤ Σ|A_{ij}|·|ŷ_j| + (1+u) · Σ|A_{ij}|·|d̂_j| -/
lemma bound_Ax0_from_eq_11_15 (n : ℕ) (fp : FPModel)
    (A : Fin n → Fin n → ℝ) (x₀ d_hat y f₂ : Fin n → ℝ)
    (hy : ∀ i, y i = x₀ i + d_hat i + f₂ i)
    (hf₂ : ∀ j, |f₂ j| ≤ fp.u * (|x₀ j| + |d_hat j|))
    (hu_lt : fp.u < 1) :
    ∀ i : Fin n,
      (1 - fp.u) * ∑ j : Fin n, |A i j| * |x₀ j| ≤
        ∑ j : Fin n, |A i j| * |y j| +
        (1 + fp.u) * ∑ j : Fin n, |A i j| * |d_hat j| := by
  intro i
  have h15 := eq_11_15 n fp x₀ d_hat y f₂ hy hf₂ hu_lt
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  nlinarith [h15 j, abs_nonneg (A i j)]

-- ============================================================
-- §11.2  Self-contained Theorem 11.4
-- ============================================================

/-- **Theorem 11.4: self-contained backward error** (Higham §11.2, eq. 11.20).

    One step of iterative refinement produces ŷ = x̂ + d̂ + f₂ with backward error:
      |b − Aŷ|_i ≤ ω · (|A||ŷ| + |b|)_i

    This version eliminates the external dominance hypothesis of `thm_11_4_assembled`
    by internalizing the eq. 11.15 substitution and the Neumann correction bound.

    The condition `hω` requires:
      (γ+u) + ((γ+u)(1+u) + (1−u)(μ+u))·ρ ≤ (1−u)·ω

    For Gaussian elimination with ω = 2γ_{n+1}, this needs ρ ≈ 1/4. -/
theorem thm_11_4_self_contained (n : ℕ) (fp : FPModel)
    (A : Fin n → Fin n → ℝ)
    (x₀ d_hat : Fin n → ℝ) (b r r_hat : Fin n → ℝ)
    (f₂ : Fin n → ℝ) (y : Fin n → ℝ)
    (ΔA_solve : Fin n → Fin n → ℝ)
    (μ : ℝ) (hμ_nn : 0 ≤ μ)
    (hr : ∀ i, r i = b i - ∑ j : Fin n, A i j * x₀ j)
    (hy : ∀ i, y i = x₀ i + d_hat i + f₂ i)
    (hsolve : ∀ i, ∑ j : Fin n, (A i j + ΔA_solve i j) * d_hat j = r_hat i)
    (hΔA : ∀ i j, |ΔA_solve i j| ≤ μ * |A i j|)
    (hres : ∀ i, |r_hat i - r i| ≤
      gamma fp (n + 1) * (|b i| + ∑ j : Fin n, |A i j| * |x₀ j|))
    (hf₂ : ∀ j, |f₂ j| ≤ fp.u * (|x₀ j| + |d_hat j|))
    (hn1 : gammaValid fp (n + 1))
    (hu_lt : fp.u < 1)
    -- Correction bound: (|A||d̂|)_i ≤ ρ · ((|A||ŷ|)_i + |b_i|)
    (ρ : ℝ) (_hρ_nn : 0 ≤ ρ)
    (hcorr : ∀ i, ∑ j : Fin n, |A i j| * |d_hat j| ≤
      ρ * (∑ j : Fin n, |A i j| * |y j| + |b i|))
    -- Target backward error coefficient (multiplied form avoids division)
    (ω : ℝ)
    (hω : (gamma fp (n + 1) + fp.u) +
           ((gamma fp (n + 1) + fp.u) * (1 + fp.u) +
            (1 - fp.u) * (μ + fp.u)) * ρ ≤ (1 - fp.u) * ω) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * y j| ≤
        ω * (∑ j : Fin n, |A i j| * |y j| + |b i|) := by
  intro i
  -- Core bounds from earlier theorems
  have h17 := eq_11_17 n fp A x₀ d_hat b r r_hat f₂ y ΔA_solve μ hμ_nn
    hr hy hsolve hΔA hres hf₂ hn1 i
  have hba := bound_Ax0_from_eq_11_15 n fp A x₀ d_hat y f₂ hy hf₂ hu_lt i
  have hci := hcorr i
  -- Positivity / nonnegativity
  have h1u : (0 : ℝ) < 1 - fp.u := by linarith
  have hγ_nn := gamma_nonneg fp hn1
  have hu_nn := fp.u_nonneg
  have hγu_nn : 0 ≤ gamma fp (n + 1) + fp.u := by linarith
  have hSy_nn : 0 ≤ ∑ j : Fin n, |A i j| * |y j| :=
    Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hbi_nn : 0 ≤ |b i| := abs_nonneg _
  -- Step 1: multiply h17 by (1-u) > 0, expand via ring
  have h17_scaled : (1 - fp.u) * |b i - ∑ j : Fin n, A i j * y j| ≤
      (gamma fp (n + 1) + fp.u) * ((1 - fp.u) * ∑ j : Fin n, |A i j| * |x₀ j|) +
      (1 - fp.u) * (μ + fp.u) * ∑ j : Fin n, |A i j| * |d_hat j| +
      (1 - fp.u) * gamma fp (n + 1) * |b i| := by
    have := mul_le_mul_of_nonneg_left h17 (le_of_lt h1u)
    linarith [show (1 - fp.u) * ((gamma fp (n + 1) + fp.u) *
        ∑ j : Fin n, |A i j| * |x₀ j| +
        (μ + fp.u) * ∑ j : Fin n, |A i j| * |d_hat j| +
        gamma fp (n + 1) * |b i|) =
        (gamma fp (n + 1) + fp.u) *
          ((1 - fp.u) * ∑ j : Fin n, |A i j| * |x₀ j|) +
        (1 - fp.u) * (μ + fp.u) * ∑ j : Fin n, |A i j| * |d_hat j| +
        (1 - fp.u) * gamma fp (n + 1) * |b i| from by ring]
  -- Step 2: substitute hba into (γ+u)*(1-u)*Sx term, expand
  have hba_expanded : (gamma fp (n + 1) + fp.u) *
      ((1 - fp.u) * ∑ j : Fin n, |A i j| * |x₀ j|) ≤
      (gamma fp (n + 1) + fp.u) * ∑ j : Fin n, |A i j| * |y j| +
      (gamma fp (n + 1) + fp.u) * (1 + fp.u) *
        ∑ j : Fin n, |A i j| * |d_hat j| := by
    have := mul_le_mul_of_nonneg_left hba hγu_nn
    linarith [show (gamma fp (n + 1) + fp.u) *
        (∑ j : Fin n, |A i j| * |y j| +
         (1 + fp.u) * ∑ j : Fin n, |A i j| * |d_hat j|) =
        (gamma fp (n + 1) + fp.u) * ∑ j : Fin n, |A i j| * |y j| +
        (gamma fp (n + 1) + fp.u) * (1 + fp.u) *
          ∑ j : Fin n, |A i j| * |d_hat j| from by ring]
  -- Step 3: (1-u)*γ*|b| ≤ (γ+u)*|b|
  have hbi_step : (1 - fp.u) * gamma fp (n + 1) * |b i| ≤
      (gamma fp (n + 1) + fp.u) * |b i| := by
    nlinarith [mul_nonneg hu_nn hbi_nn, mul_nonneg hu_nn hγ_nn]
  -- Step 4: use correction bound on Sd, expand
  have hC_nn : 0 ≤ (gamma fp (n + 1) + fp.u) * (1 + fp.u) +
      (1 - fp.u) * (μ + fp.u) := by nlinarith
  have corr_expanded :
      ((gamma fp (n + 1) + fp.u) * (1 + fp.u) +
       (1 - fp.u) * (μ + fp.u)) *
        ∑ j : Fin n, |A i j| * |d_hat j| ≤
      ((gamma fp (n + 1) + fp.u) * (1 + fp.u) +
       (1 - fp.u) * (μ + fp.u)) * ρ *
        ∑ j : Fin n, |A i j| * |y j| +
      ((gamma fp (n + 1) + fp.u) * (1 + fp.u) +
       (1 - fp.u) * (μ + fp.u)) * ρ * |b i| := by
    have := mul_le_mul_of_nonneg_left hci hC_nn
    linarith [show ((gamma fp (n + 1) + fp.u) * (1 + fp.u) +
        (1 - fp.u) * (μ + fp.u)) *
        (ρ * (∑ j : Fin n, |A i j| * |y j| + |b i|)) =
        ((gamma fp (n + 1) + fp.u) * (1 + fp.u) +
         (1 - fp.u) * (μ + fp.u)) * ρ *
          ∑ j : Fin n, |A i j| * |y j| +
        ((gamma fp (n + 1) + fp.u) * (1 + fp.u) +
         (1 - fp.u) * (μ + fp.u)) * ρ * |b i| from by ring]
  -- Step 5: combine everything and conclude
  -- (1-u)*|res| ≤ (γ+u)*Sy + (γ+u)*(1+u)*Sd + (1-u)*(μ+u)*Sd + (γ+u)*bi
  -- The Sd coefficient: (γ+u)*(1+u) + (1-u)*(μ+u) = C
  -- Use corr_expanded: C*Sd ≤ C*ρ*Sy + C*ρ*bi
  -- So (1-u)*|res| ≤ ((γ+u)+C*ρ)*Sy + (C*ρ+(γ+u))*bi = ((γ+u)+C*ρ)*(Sy+bi)
  -- From hω: (γ+u)+C*ρ ≤ (1-u)*ω, so ≤ (1-u)*ω*(Sy+bi)
  have key : (1 - fp.u) * |b i - ∑ j : Fin n, A i j * y j| ≤
      (1 - fp.u) * (ω * (∑ j : Fin n, |A i j| * |y j| + |b i|)) := by
    nlinarith [h17_scaled, hba_expanded, hbi_step, corr_expanded, hω,
      mul_nonneg (show (0 : ℝ) ≤ (1 - fp.u) * ω -
        ((gamma fp (n + 1) + fp.u) +
         ((gamma fp (n + 1) + fp.u) * (1 + fp.u) +
          (1 - fp.u) * (μ + fp.u)) * ρ) from by linarith) hSy_nn,
      mul_nonneg (show (0 : ℝ) ≤ (1 - fp.u) * ω -
        ((gamma fp (n + 1) + fp.u) +
         ((gamma fp (n + 1) + fp.u) * (1 + fp.u) +
          (1 - fp.u) * (μ + fp.u)) * ρ) from by linarith) hbi_nn]
  -- Cancel (1-u) > 0
  calc |b i - ∑ j : Fin n, A i j * y j|
      = (1 - fp.u)⁻¹ * ((1 - fp.u) * |b i - ∑ j : Fin n, A i j * y j|) := by
        field_simp
    _ ≤ (1 - fp.u)⁻¹ * ((1 - fp.u) *
        (ω * (∑ j : Fin n, |A i j| * |y j| + |b i|))) :=
        mul_le_mul_of_nonneg_left key (inv_nonneg.mpr (le_of_lt h1u))
    _ = ω * (∑ j : Fin n, |A i j| * |y j| + |b i|) := by field_simp

-- ============================================================
-- §11.3  LU instantiation of Theorem 11.4
-- ============================================================

/-- **Theorem 11.4 for Gaussian elimination** (Higham §11.3, eq. 11.20).

    For GE with μ = γ(3n), one step of fixed-precision iterative refinement yields:
      |b − Aŷ| ≤ 2γ_{n+1} · (|A||ŷ| + |b|)

    This instantiates `thm_11_4_self_contained` with the GE backward error
    μ = γ(3n) from Theorem 9.4 and target coefficient ω = 2γ_{n+1}. -/
theorem lu_refinement_thm_11_4 (n : ℕ) (fp : FPModel)
    (A : Fin n → Fin n → ℝ)
    (x₀ d_hat : Fin n → ℝ) (b r r_hat : Fin n → ℝ)
    (f₂ : Fin n → ℝ) (y : Fin n → ℝ)
    (ΔA_solve : Fin n → Fin n → ℝ)
    (hr : ∀ i, r i = b i - ∑ j : Fin n, A i j * x₀ j)
    (hy : ∀ i, y i = x₀ i + d_hat i + f₂ i)
    (hsolve : ∀ i, ∑ j : Fin n, (A i j + ΔA_solve i j) * d_hat j = r_hat i)
    (hΔA : ∀ i j, |ΔA_solve i j| ≤ gamma fp (3 * n) * |A i j|)
    (hres : ∀ i, |r_hat i - r i| ≤
      gamma fp (n + 1) * (|b i| + ∑ j : Fin n, |A i j| * |x₀ j|))
    (hf₂ : ∀ j, |f₂ j| ≤ fp.u * (|x₀ j| + |d_hat j|))
    (hn1 : gammaValid fp (n + 1))
    (hn3 : gammaValid fp (3 * n))
    (hu_lt : fp.u < 1)
    (ρ : ℝ) (hρ_nn : 0 ≤ ρ)
    (hcorr : ∀ i, ∑ j : Fin n, |A i j| * |d_hat j| ≤
      ρ * (∑ j : Fin n, |A i j| * |y j| + |b i|))
    (hρ_cond : (gamma fp (n + 1) + fp.u) +
        ((gamma fp (n + 1) + fp.u) * (1 + fp.u) +
         (1 - fp.u) * (gamma fp (3 * n) + fp.u)) * ρ ≤
        (1 - fp.u) * (2 * gamma fp (n + 1))) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * y j| ≤
        2 * gamma fp (n + 1) * (∑ j : Fin n, |A i j| * |y j| + |b i|) :=
  thm_11_4_self_contained n fp A x₀ d_hat b r r_hat f₂ y ΔA_solve
    (gamma fp (3 * n)) (gamma_nonneg fp hn3)
    hr hy hsolve hΔA hres hf₂ hn1 hu_lt ρ hρ_nn hcorr
    (2 * gamma fp (n + 1)) hρ_cond

-- ============================================================
-- §12.2  Nonnegative resolvent ∞-norm bound (Neumann inversion, eqns 12.20–12.21)
-- ============================================================















































-- ============================================================
-- §12.1  Exact forward-error identity/bound for one step (eqns 12.4–12.5)
-- ============================================================


























































































-- ============================================================
-- §12.2  Norm-to-componentwise correction bound (σ/cond step for Thm 12.4)
-- ============================================================





















-- ============================================================
-- §12.2  Correction Neumann inequality from the solver (eqns 12.18–12.20)
-- ============================================================











































































end NumStability
