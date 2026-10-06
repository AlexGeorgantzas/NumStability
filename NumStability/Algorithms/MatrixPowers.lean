-- Algorithms/MatrixPowers.lean
--
-- Higham Chapter 18: Error analysis of matrix powers.
--
-- Covers §18.2 (finite precision bounds for computed A^m via repeated
-- matrix-vector products) and the similarity-based convergence engine
-- underlying Theorem 18.1 (Higham–Knight).

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecificLimits.Basic
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.Algorithms.MatVec
namespace NumStability

open scoped BigOperators

-- ============================================================
-- §18.2  Backward error model for computed matrix powers
-- ============================================================

/-- Model for computing A^m v by repeated matrix-vector multiplication.

    At each step the computed vector satisfies
      v_{k+1} = (A + ΔA_k) · v_k,   |ΔA_k| ≤ c · |A|  componentwise
    corresponding to Higham eq (18.10)–(18.11).

    The constant c is `gamma fp n` when each step is a standard matVec
    of an n-column matrix (from `matVec_backward_error`). -/
structure ComputedMatPowVec (n : ℕ) (A : Fin n → Fin n → ℝ)
    (v : ℕ → (Fin n → ℝ)) (c : ℝ) : Prop where
  step : ∀ k, ∃ ΔA : Fin n → Fin n → ℝ,
    (∀ i j, |ΔA i j| ≤ c * |A i j|) ∧
    (∀ i, v (k + 1) i = ∑ j : Fin n, (A i j + ΔA i j) * v k j)

/-- Weakening the per-step perturbation constant: a computed-power sequence
    with componentwise budget `c` also satisfies any larger budget `c'`. -/
theorem ComputedMatPowVec.mono {n : ℕ} {A : Fin n → Fin n → ℝ}
    {v : ℕ → (Fin n → ℝ)} {c c' : ℝ} (hcc : c ≤ c')
    (h : ComputedMatPowVec n A v c) : ComputedMatPowVec n A v c' := by
  constructor
  intro k
  obtain ⟨ΔA, hΔ, heq⟩ := h.step k
  exact ⟨ΔA, fun i j =>
    (hΔ i j).trans (mul_le_mul_of_nonneg_right hcc (abs_nonneg _)), heq⟩

-- ============================================================
-- §18.2  Concrete floating-point realization of (18.10)–(18.11)
-- ============================================================

/-- The computed iteration `v_{k+1} = fl(A · v_k)` by repeated floating-point
    matrix–vector products, starting from `v0`.  This is the concrete
    algorithm whose error recurrence is eq (18.10). -/
noncomputable def fl_matPowVecSeq (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (v0 : Fin n → ℝ) : ℕ → (Fin n → ℝ)
  | 0 => v0
  | k + 1 => fl_matVec fp n n A (fl_matPowVecSeq fp n A v0 k)

/-- **Concrete realization of the error model (18.10)–(18.11)**: the
    floating-point iteration `v_{k+1} = fl(A v_k)` satisfies the perturbed
    recurrence `v_{k+1} = (A + ΔA_k) v_k` with `|ΔA_k| ≤ γ_n |A|`
    componentwise.  Each step is one `fl_matVec` with inner dimension `n`
    (from `matVec_backward_error`), so the per-step constant is `γ_n`;
    the book's (18.11) uses the weaker constant `γ_{n+2}`, recovered in
    `computedMatPowVec_fl_matVec_gamma_add_two` by monotonicity. -/
theorem computedMatPowVec_fl_matVec (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (v0 : Fin n → ℝ) (hn : gammaValid fp n) :
    ComputedMatPowVec n A (fl_matPowVecSeq fp n A v0) (gamma fp n) := by
  constructor
  intro k
  obtain ⟨ΔA, hΔ, heq⟩ :=
    matVec_backward_error fp n n A (fl_matPowVecSeq fp n A v0 k) hn
  refine ⟨ΔA, hΔ, fun i => ?_⟩
  show fl_matPowVecSeq fp n A v0 (k + 1) i = _
  simp only [fl_matPowVecSeq]
  exact heq i

/-- The concrete realization stated with the book's (18.11) constant
    `γ_{n+2}` (valid since `γ_n ≤ γ_{n+2}`). -/
theorem computedMatPowVec_fl_matVec_gamma_add_two (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (v0 : Fin n → ℝ)
    (hn2 : gammaValid fp (n + 2)) :
    ComputedMatPowVec n A (fl_matPowVecSeq fp n A v0) (gamma fp (n + 2)) :=
  (computedMatPowVec_fl_matVec fp n A v0
      (gammaValid_mono fp (Nat.le_add_right n 2) hn2)).mono
    (gamma_mono fp (Nat.le_add_right n 2) hn2)

-- ============================================================
-- One-step componentwise bound
-- ============================================================

/-- **One-step componentwise bound**: if v_{k+1} = (A+ΔA)v_k with
    |ΔA_{ij}| ≤ c·|A_{ij}|, then
    |v_{k+1,i}| ≤ (1+c) · ∑_j |A_{ij}| · |v_{k,j}|. -/
theorem one_step_matpow_bound (n : ℕ) (A ΔA : Fin n → Fin n → ℝ)
    (v : Fin n → ℝ) (c : ℝ)
    (hΔ : ∀ i j, |ΔA i j| ≤ c * |A i j|)
    (w : Fin n → ℝ) (hw : ∀ i, w i = ∑ j : Fin n, (A i j + ΔA i j) * v j) :
    ∀ i, |w i| ≤ (1 + c) * ∑ j : Fin n, |A i j| * |v j| := by
  intro i
  rw [hw i]
  calc |∑ j : Fin n, (A i j + ΔA i j) * v j|
      ≤ ∑ j : Fin n, |(A i j + ΔA i j) * v j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin n, |A i j + ΔA i j| * |v j| := by
        congr 1; ext j; exact abs_mul _ _
    _ ≤ ∑ j : Fin n, (|A i j| + c * |A i j|) * |v j| := by
        apply Finset.sum_le_sum; intro j _
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        calc |A i j + ΔA i j|
            ≤ |A i j| + |ΔA i j| := abs_add_le _ _
          _ ≤ |A i j| + c * |A i j| := by linarith [hΔ i j]
    _ = (1 + c) * ∑ j : Fin n, |A i j| * |v j| := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring

-- ============================================================
-- §18.2  Componentwise forward bound (consequence of 18.10–18.11)
-- ============================================================

/-- **Componentwise bound for computed matrix powers** (§18.2).

    If v_{k+1} = (A+ΔA_k)v_k with |ΔA_k| ≤ c|A|, then
      |v_m i| ≤ (1+c)^m · (|A|^m |v_0|)_i
    componentwise, where |A|^m denotes the mth power of the entrywise
    absolute value matrix. -/
theorem matPow_componentwise_bound (n : ℕ) (A : Fin n → Fin n → ℝ)
    (v : ℕ → (Fin n → ℝ)) (c : ℝ) (hc : 0 ≤ c)
    (hComp : ComputedMatPowVec n A v c) (m : ℕ) :
    ∀ i, |v m i| ≤ (1 + c) ^ m *
      matMulVec n (matPow n (absMatrix n A) m) (absVec n (v 0)) i := by
  induction m with
  | zero =>
    intro i
    simp only [pow_zero, one_mul, matPow]
    unfold matMulVec absVec idMatrix
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true, le_refl]
  | succ m ih =>
    intro i
    obtain ⟨ΔA, hΔ, hstep⟩ := hComp.step m
    have h1 := one_step_matpow_bound n A ΔA (v m) c hΔ (v (m + 1)) hstep i
    calc |v (m + 1) i|
        ≤ (1 + c) * ∑ j : Fin n, |A i j| * |v m j| := h1
      _ ≤ (1 + c) * ∑ j : Fin n, |A i j| *
          ((1 + c) ^ m * matMulVec n (matPow n (absMatrix n A) m)
            (absVec n (v 0)) j) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          apply Finset.sum_le_sum; intro j _
          apply mul_le_mul_of_nonneg_left (ih j) (abs_nonneg _)
      _ = (1 + c) ^ (m + 1) * ∑ j : Fin n, |A i j| *
          matMulVec n (matPow n (absMatrix n A) m) (absVec n (v 0)) j := by
          simp_rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
          set w := matMulVec n (matPow n (absMatrix n A) m) (absVec n (v 0)) j; ring
      _ = (1 + c) ^ (m + 1) *
          matMulVec n (matPow n (absMatrix n A) (m + 1)) (absVec n (v 0)) i := by
          congr 1
          show ∑ j, |A i j| * matMulVec n (matPow n (absMatrix n A) m)
              (absVec n (v 0)) j =
            matMulVec n (matMul n (absMatrix n A) (matPow n (absMatrix n A) m))
              (absVec n (v 0)) i
          unfold matMulVec matMul absMatrix
          simp_rw [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro k _
          apply Finset.sum_congr rfl; intro j _; ring

-- ============================================================
-- §18.2  Normwise forward bound
-- ============================================================

/-- **Normwise bound for computed matrix powers** (§18.2).

    ‖v_m‖∞ ≤ ((1+c) · ‖A‖∞)^m · ‖v_0‖∞. -/
theorem matPow_normwise_bound (n : ℕ) (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (v : ℕ → (Fin n → ℝ)) (c : ℝ) (hc : 0 ≤ c)
    (hComp : ComputedMatPowVec n A v c) (m : ℕ) :
    infNormVec (v m) ≤ ((1 + c) * infNorm A) ^ m * infNormVec (v 0) := by
  apply infNormVec_le_of_abs_le
  · intro i
    have hcw := matPow_componentwise_bound n A v c hc hComp m i
    -- Pointwise bound on the matMulVec term
    have hmv : matMulVec n (matPow n (absMatrix n A) m) (absVec n (v 0)) i ≤
        infNorm A ^ m * infNormVec (v 0) := by
      calc matMulVec n (matPow n (absMatrix n A) m) (absVec n (v 0)) i
          ≤ |matMulVec n (matPow n (absMatrix n A) m) (absVec n (v 0)) i| :=
            le_abs_self _
        _ ≤ infNormVec (matMulVec n (matPow n (absMatrix n A) m) (absVec n (v 0))) :=
            abs_le_infNormVec _ i
        _ ≤ infNorm (matPow n (absMatrix n A) m) * infNormVec (absVec n (v 0)) :=
            infNormVec_matMulVec_le hn _ _
        _ ≤ infNorm A ^ m * infNormVec (absVec n (v 0)) := by
            apply mul_le_mul_of_nonneg_right _ (infNormVec_nonneg _)
            calc infNorm (matPow n (absMatrix n A) m)
                ≤ infNorm (absMatrix n A) ^ m := infNorm_matPow_le hn _ _
              _ = infNorm A ^ m := by rw [infNorm_absMatrix hn]
        _ = infNorm A ^ m * infNormVec (v 0) := by
            rw [infNormVec_absVec hn]
    calc |v m i|
        ≤ (1 + c) ^ m * matMulVec n (matPow n (absMatrix n A) m) (absVec n (v 0)) i := hcw
      _ ≤ (1 + c) ^ m * (infNorm A ^ m * infNormVec (v 0)) :=
          mul_le_mul_of_nonneg_left hmv (pow_nonneg (by linarith) m)
      _ = ((1 + c) * infNorm A) ^ m * infNormVec (v 0) := by
          rw [← mul_assoc, ← mul_pow]
  · exact mul_nonneg
      (pow_nonneg (mul_nonneg (by linarith) (infNorm_nonneg A)) m)
      (infNormVec_nonneg _)

-- ============================================================
-- §18.2  Sufficient convergence condition (normwise, eq 18.12)
-- ============================================================

/-- **Sufficient condition for convergence of computed matrix powers**
    (normwise version of eq 18.12).

    If q := (1+c)·‖A‖∞ ≤ some q₀ < 1, then ‖v_m‖∞ ≤ q₀^m · ‖v_0‖∞.

    The book states (18.12) as ρ(|A|) < 1/(1+γ_n), which is sharper
    since ρ(|A|) ≤ ‖A‖∞. -/
theorem matPow_convergence_bound (n : ℕ) (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (v : ℕ → (Fin n → ℝ)) (c : ℝ) (hc : 0 ≤ c)
    (hComp : ComputedMatPowVec n A v c)
    (q : ℝ) (hq : (1 + c) * infNorm A ≤ q) (m : ℕ) :
    infNormVec (v m) ≤ q ^ m * infNormVec (v 0) := by
  calc infNormVec (v m)
      ≤ ((1 + c) * infNorm A) ^ m * infNormVec (v 0) :=
        matPow_normwise_bound n hn A v c hc hComp m
    _ ≤ q ^ m * infNormVec (v 0) := by
        apply mul_le_mul_of_nonneg_right _ (infNormVec_nonneg _)
        exact pow_le_pow_left₀
          (mul_nonneg (by linarith) (infNorm_nonneg A)) hq m

-- ============================================================
-- §18.2  Matrix-level componentwise bound (column by column)
-- ============================================================

/-- **Matrix-level componentwise bound**: if each column of fl(A^m) is
    computed by repeated matVec starting from e_j (so B_0 = I), then
    |fl(A^m)_{ij}| ≤ (1+c)^m · (|A|^m)_{ij}. -/
theorem matPow_matrix_bound (n : ℕ) (A : Fin n → Fin n → ℝ)
    (B : ℕ → (Fin n → Fin n → ℝ)) (c : ℝ) (hc : 0 ≤ c)
    (hInit : B 0 = idMatrix n)
    (hCol : ∀ j : Fin n, ComputedMatPowVec n A (fun k => fun i => B k i j) c)
    (m : ℕ) :
    ∀ i j, |B m i j| ≤ (1 + c) ^ m * matPow n (absMatrix n A) m i j := by
  intro i j
  have hcw := matPow_componentwise_bound n A
    (fun k => fun i' => B k i' j) c hc (hCol j) m i
  calc |B m i j|
      ≤ (1 + c) ^ m * matMulVec n (matPow n (absMatrix n A) m)
          (absVec n (fun i' => B 0 i' j)) i := hcw
    _ = (1 + c) ^ m * ∑ l : Fin n,
          matPow n (absMatrix n A) m i l * |B 0 l j| := by
        unfold matMulVec absVec; ring_nf
    _ = (1 + c) ^ m * matPow n (absMatrix n A) m i j := by
        congr 1
        have hid : ∀ l : Fin n, |B 0 l j| = if l = j then 1 else 0 := by
          intro l; rw [hInit]; unfold idMatrix; split <;> simp
        simp_rw [hid, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
          Finset.mem_univ, if_true]

-- ============================================================
-- §18.2  Nonneg matrix specialization
-- ============================================================

/-- **Nonneg matrix simplification**: when A ≥ 0, |A| = A so the
    componentwise bound simplifies to |v_m i| ≤ (1+c)^m · (A^m |v_0|)_i. -/
theorem matPow_nonneg_componentwise_bound (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    (v : ℕ → (Fin n → ℝ)) (c : ℝ) (hc : 0 ≤ c)
    (hComp : ComputedMatPowVec n A v c) (m : ℕ) :
    ∀ i, |v m i| ≤ (1 + c) ^ m *
      matMulVec n (matPow n A m) (absVec n (v 0)) i := by
  have habs : absMatrix n A = A := by
    ext i j; unfold absMatrix; exact abs_of_nonneg (hA i j)
  intro i
  have hcw := matPow_componentwise_bound n A v c hc hComp m i
  rwa [habs] at hcw

-- ============================================================
-- §18.2  Similarity-based convergence engine (eq 18.14)
-- ============================================================

/-- **Similarity-based convergence criterion** (eq 18.14 in Theorem 18.1 proof).

    If there exists a nonsingular S such that for all perturbations ΔA_k,
      ‖S⁻¹(A+ΔA_k)S‖∞ ≤ q < 1,
    then ‖S⁻¹ v_m‖∞ ≤ q^m · ‖S⁻¹ v_0‖∞.

    This is the reusable engine underlying Theorem 18.1. The Jordan form
    is only used to CONSTRUCT the right S; this engine works for any S. -/
theorem similarity_product_bound (n : ℕ) (hn : 0 < n)
    (A : Fin n → Fin n → ℝ)
    (S S_inv : Fin n → Fin n → ℝ)
    (hSr : IsRightInverse n S S_inv)
    (v : ℕ → (Fin n → ℝ)) (c : ℝ)
    (hComp : ComputedMatPowVec n A v c)
    (q : ℝ) (hq : 0 ≤ q)
    (hBound : ∀ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ c * |A i j|) →
      infNorm (matMul n S_inv (matMul n (fun i j => A i j + ΔA i j) S)) ≤ q) :
    ∀ m, infNormVec (matMulVec n S_inv (v m)) ≤
      q ^ m * infNormVec (matMulVec n S_inv (v 0)) := by
  intro m; induction m with
  | zero => simp [pow_zero, one_mul]
  | succ m ih =>
    obtain ⟨ΔA, hΔ, hstep⟩ := hComp.step m
    have hBk := hBound ΔA hΔ
    let B := fun i j => A i j + ΔA i j
    have hSS : matMul n S S_inv = idMatrix n := by ext a b; exact hSr a b
    -- Establish v_{m+1} = B v_m
    have hBv : ∀ k, v (m + 1) k = matMulVec n B (v m) k := by
      intro k; exact hstep k
    -- Key algebraic identity: (S⁻¹BS) · S⁻¹ = S⁻¹B
    have h_eq : matMul n (matMul n S_inv (matMul n B S)) S_inv =
        matMul n S_inv B := by
      rw [matMul_assoc, matMul_assoc, hSS, matMul_id_right]
    -- Key: S⁻¹ v_{m+1} = (S⁻¹ B S)(S⁻¹ v_m)
    have key : ∀ i, matMulVec n S_inv (v (m + 1)) i =
        matMulVec n (matMul n S_inv (matMul n B S))
          (matMulVec n S_inv (v m)) i := by
      intro i
      -- S⁻¹ v_{m+1} = S⁻¹ (B v_m)
      have h1 : matMulVec n S_inv (v (m + 1)) i =
          matMulVec n S_inv (matMulVec n B (v m)) i := by
        unfold matMulVec; congr 1; ext k; congr 1; exact hBv k
      -- S⁻¹ (B v_m) = (S⁻¹ B) v_m
      have h2 : matMulVec n S_inv (matMulVec n B (v m)) i =
          matMulVec n (matMul n S_inv B) (v m) i :=
        (matMulVec_matMul n S_inv B (v m) i).symm
      -- (S⁻¹ B) v_m = ((S⁻¹BS)S⁻¹) v_m
      have h3 : matMulVec n (matMul n S_inv B) (v m) i =
          matMulVec n (matMul n (matMul n S_inv (matMul n B S)) S_inv) (v m) i := by
        rw [h_eq]
      -- ((S⁻¹BS)S⁻¹) v_m = (S⁻¹BS)(S⁻¹ v_m)
      have h4 : matMulVec n (matMul n (matMul n S_inv (matMul n B S)) S_inv) (v m) i =
          matMulVec n (matMul n S_inv (matMul n B S)) (matMulVec n S_inv (v m)) i :=
        matMulVec_matMul n (matMul n S_inv (matMul n B S)) S_inv (v m) i
      exact h1.trans (h2.trans (h3.trans h4))
    -- ‖S⁻¹ v_{m+1}‖ ≤ ‖S⁻¹BS‖ · ‖S⁻¹ v_m‖ ≤ q · ‖S⁻¹ v_m‖
    have h1 : infNormVec (matMulVec n S_inv (v (m + 1))) ≤
        q * infNormVec (matMulVec n S_inv (v m)) := by
      calc infNormVec (matMulVec n S_inv (v (m + 1)))
          = infNormVec (matMulVec n (matMul n S_inv (matMul n B S))
              (matMulVec n S_inv (v m))) := by
            exact congrArg infNormVec (funext key)
        _ ≤ infNorm (matMul n S_inv (matMul n B S)) *
            infNormVec (matMulVec n S_inv (v m)) :=
            infNormVec_matMulVec_le hn _ _
        _ ≤ q * infNormVec (matMulVec n S_inv (v m)) :=
            mul_le_mul_of_nonneg_right hBk (infNormVec_nonneg _)
    calc infNormVec (matMulVec n S_inv (v (m + 1)))
        ≤ q * infNormVec (matMulVec n S_inv (v m)) := h1
      _ ≤ q * (q ^ m * infNormVec (matMulVec n S_inv (v 0))) :=
          mul_le_mul_of_nonneg_left ih hq
      _ = q ^ (m + 1) * infNormVec (matMulVec n S_inv (v 0)) := by ring

-- ============================================================
-- §18.2  Corollary: normwise bound via similarity
-- ============================================================

/-- **Normwise bound via similarity**: ‖v_m‖∞ ≤ κ∞(S) · q^m · ‖v_0‖∞.

    Since v = S(S⁻¹v), we have ‖v‖ ≤ ‖S‖·‖S⁻¹v‖.
    Combined with the similarity product bound and ‖S⁻¹v_0‖ ≤ ‖S⁻¹‖·‖v_0‖. -/
theorem similarity_normwise_bound (n : ℕ) (hn : 0 < n)
    (A : Fin n → Fin n → ℝ)
    (S S_inv : Fin n → Fin n → ℝ)
    (hSr : IsRightInverse n S S_inv)
    (v : ℕ → (Fin n → ℝ)) (c : ℝ)
    (hComp : ComputedMatPowVec n A v c)
    (q : ℝ) (hq : 0 ≤ q)
    (hBound : ∀ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ c * |A i j|) →
      infNorm (matMul n S_inv (matMul n (fun i j => A i j + ΔA i j) S)) ≤ q)
    (m : ℕ) :
    infNormVec (v m) ≤
      infNorm S * infNorm S_inv * q ^ m * infNormVec (v 0) := by
  have hSS : matMul n S S_inv = idMatrix n := by ext a b; exact hSr a b
  -- Step 1: w = S(S⁻¹w) so ‖w‖ ≤ ‖S‖·‖S⁻¹w‖
  have hv_eq : ∀ (w : Fin n → ℝ) (i : Fin n),
      w i = matMulVec n S (matMulVec n S_inv w) i := by
    intro w i
    have h1 := (matMulVec_matMul n S S_inv w i).symm
    rw [h1, hSS]; unfold matMulVec idMatrix; simp [Finset.mem_univ]
  have h_norm_le : ∀ (w : Fin n → ℝ),
      infNormVec w ≤ infNorm S * infNormVec (matMulVec n S_inv w) := by
    intro w
    apply infNormVec_le_of_abs_le
    · intro i
      rw [hv_eq w i]
      calc |matMulVec n S (matMulVec n S_inv w) i|
          ≤ ∑ j, |S i j| * |matMulVec n S_inv w j| := abs_matMulVec_le n S _ i
        _ ≤ ∑ j : Fin n, |S i j| * infNormVec (matMulVec n S_inv w) := by
            apply Finset.sum_le_sum; intro j _
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            exact abs_le_infNormVec (matMulVec n S_inv w) j
        _ = (∑ j : Fin n, |S i j|) * infNormVec (matMulVec n S_inv w) :=
            (Finset.sum_mul ..).symm
        _ ≤ infNorm S * infNormVec (matMulVec n S_inv w) :=
            mul_le_mul_of_nonneg_right (row_sum_le_infNorm S i)
              (infNormVec_nonneg _)
    · exact mul_nonneg (infNorm_nonneg _) (infNormVec_nonneg _)
  -- Step 2: combine
  have h2 := similarity_product_bound n hn A S S_inv hSr v c hComp q hq hBound m
  have h3 : infNormVec (matMulVec n S_inv (v 0)) ≤
      infNorm S_inv * infNormVec (v 0) :=
    infNormVec_matMulVec_le hn S_inv (v 0)
  calc infNormVec (v m)
      ≤ infNorm S * infNormVec (matMulVec n S_inv (v m)) := h_norm_le (v m)
    _ ≤ infNorm S * (q ^ m * infNormVec (matMulVec n S_inv (v 0))) :=
        mul_le_mul_of_nonneg_left h2 (infNorm_nonneg S)
    _ ≤ infNorm S * (q ^ m * (infNorm S_inv * infNormVec (v 0))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h3 (pow_nonneg hq m))
          (infNorm_nonneg S)
    _ = infNorm S * infNorm S_inv * q ^ m * infNormVec (v 0) := by ring

-- ============================================================
-- Theorem 18.1: JordanFormSpec and convergence condition
-- ============================================================

/-- Jordan form data for a matrix `A`, **plus one assumed axiom** carrying the
    crux of Theorem 18.1.

    The plain data fields are innocuous: `X`, `X_inv` (similarity `A = X J X⁻¹`),
    `spectral_radius` `ρ(A) < 1` (convergent matrix), and `max_block_size`
    `t = maxᵢ nᵢ` (largest Jordan block).

    ⚠ AXIOM / OPEN OBLIGATION.  The field `similarity_absorbs` is **not proved
    here** — it is an assumed hypothesis that packages the entire non-trivial
    content of Theorem 18.1's proof (Higham pp. 347–348): the `S = X P(ε)`
    Jordan-block δ-scaling construction with `D(δ) = diag(1,δ,…,δ^{nᵢ-1})`, and
    the `(1+1/t)^t < e < 4` optimisation, which turn the Higham–Knight condition
    `4t·η·κ∞(X)·‖A‖∞ < (1-ρ)^t` into a per-step contraction
    `‖S⁻¹(A+ΔA)S‖∞ ≤ q < 1` for all `|ΔA| ≤ η|A|`.  Discharging it needs
    classical Jordan Normal Form over ℂ, which Mathlib does not currently
    provide (only Jordan–Chevalley).  Until it is discharged, every result
    consuming this field is *conditional on this axiom*, not a closure of
    Theorem 18.1.

    Note: κ∞(S) ≤ (1−ρ−ε)^{1−t} · κ∞(X) from eq (18.15), which is
    generally ≥ κ∞(X) when t > 1.  We do not constrain κ∞(S) here;
    the convergence constant C in Theorem 18.1 is κ∞(S), not κ∞(X). -/
structure JordanFormSpec (n : ℕ) (hn : 0 < n)
    (A X X_inv : Fin n → Fin n → ℝ) where
  inv_right : IsRightInverse n X X_inv
  spectral_radius : ℝ
  hr_nonneg : 0 ≤ spectral_radius
  hr_lt_one : spectral_radius < 1
  max_block_size : ℕ
  ht_pos : 0 < max_block_size
  /-- ASSUMED AXIOM (see the structure docstring): under the Higham–Knight
      condition there exists a perturbation-absorbing similarity `S`.  This is
      the undischarged crux of Theorem 18.1 (the `S = X P(ε)` δ-scaling
      construction), not a proved fact. -/
  similarity_absorbs :
    ∀ (η : ℝ), 0 ≤ η →
    4 * max_block_size * η * (infNorm X * infNorm X_inv) *
      infNorm A < (1 - spectral_radius) ^ max_block_size →
    ∃ S S_inv : Fin n → Fin n → ℝ,
    ∃ q : ℝ,
      IsRightInverse n S S_inv ∧
      0 ≤ q ∧ q < 1 ∧
      (∀ ΔA : Fin n → Fin n → ℝ,
        (∀ i j, |ΔA i j| ≤ η * |A i j|) →
        infNorm (matMul n S_inv
          (matMul n (fun i j => A i j + ΔA i j) S)) ≤ q)

/-- **Conditional reduction of Theorem 18.1** (Higham–Knight).

    This is **not** a full proof of Theorem 18.1.  It *assumes* the
    perturbation-absorbing similarity construction via
    `JordanFormSpec.similarity_absorbs` (an undischarged axiom — see there) and
    then performs only the book's elementary telescoping step.  The source row
    for Theorem 18.1 remains OPEN until that axiom is discharged.

    Given Jordan form data (X, X⁻¹, ρ, t) with ρ(A) < 1 and the Higham–Knight
    condition (18.13)

      4t · c · κ∞(X) · ‖A‖∞ < (1 − ρ(A))^t

    where t = max_i n_i (largest Jordan block), c is the per-step backward
    error bound, and κ∞(X) = ‖X‖∞ · ‖X⁻¹‖∞, it concludes geometric decay:
    ∃ C q, q < 1 ∧ ‖v_m‖∞ ≤ C · q^m · ‖v_0‖∞, with C = κ∞(S) for the scaled
    similarity S = X P(ε) (eq 18.15); in general κ∞(S) ≥ κ∞(X) when t > 1.

    Compose with `computedMatPow_tendsto_zero_of_geometric` to obtain the
    book's stated limit conclusion fl(A^m) → 0. -/
theorem higham_knight_18_1 (n : ℕ) (hn : 0 < n)
    (A X X_inv : Fin n → Fin n → ℝ)
    (hJ : JordanFormSpec n hn A X X_inv)
    (v : ℕ → (Fin n → ℝ)) (c : ℝ) (hc : 0 ≤ c)
    (hComp : ComputedMatPowVec n A v c)
    (hCond : 4 * hJ.max_block_size * c *
      (infNorm X * infNorm X_inv) * infNorm A <
      (1 - hJ.spectral_radius) ^ hJ.max_block_size) :
    ∃ (C q : ℝ), 0 ≤ C ∧ 0 ≤ q ∧ q < 1 ∧
      ∀ m, infNormVec (v m) ≤
        C * q ^ m * infNormVec (v 0) := by
  obtain ⟨S, S_inv, q, hSr, hq0, hq1, hAbsorb⟩ :=
    hJ.similarity_absorbs c hc hCond
  exact ⟨infNorm S * infNorm S_inv, q,
    mul_nonneg (infNorm_nonneg S) (infNorm_nonneg S_inv),
    hq0, hq1, fun m =>
    similarity_normwise_bound n hn A S S_inv hSr v c hComp q hq0 hAbsorb m⟩

-- ============================================================
-- §18.2  Limit form of the convergence conclusion
-- ============================================================

/-- **Computed powers tend to zero from a geometric decay bound**.

    Higham states the conclusion of Theorems 18.1 and 18.2 as the *limit*
    `fl(A^m) → 0` as `m → ∞`, whereas the results above establish only the
    geometric *bound* `‖v_m‖∞ ≤ C · q^m · ‖v_0‖∞` with `q < 1`.  This lemma
    supplies the missing step: any such geometric bound forces
    `‖v_m‖∞ → 0`.

    Reusable for both the Higham–Knight matrix-power theorem (18.1) and its
    diagonalizable/pseudospectral corollary (18.2): apply it to the existential
    output `⟨C, q, _, _, hq1, hbound⟩` of the convergence theorem. Purely a
    real-analysis squeeze; introduces no assumption about `A`. -/
theorem computedMatPow_tendsto_zero_of_geometric (n : ℕ)
    (v : ℕ → (Fin n → ℝ)) (C q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hbound : ∀ m, infNormVec (v m) ≤ C * q ^ m * infNormVec (v 0)) :
    Filter.Tendsto (fun m => infNormVec (v m)) Filter.atTop (nhds 0) := by
  have hpow : Filter.Tendsto (fun m : ℕ => q ^ m) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have htop : Filter.Tendsto (fun m => C * q ^ m * infNormVec (v 0))
      Filter.atTop (nhds 0) := by
    simpa using (hpow.const_mul C).mul_const (infNormVec (v 0))
  exact squeeze_zero (fun m => infNormVec_nonneg _) hbound htop

-- ============================================================
-- §18.2  End-to-end conditional forms with the limit conclusion
-- ============================================================

/-- **End-to-end conditional form of Theorem 18.1 for the actual
    floating-point iteration.**  Composes the concrete (18.10)–(18.11)
    realization (`fl_matPowVecSeq`, per-step constant `γ_{n+2}`), the
    conditional reduction `higham_knight_18_1`, and the limit wrapper: under
    the Jordan-data hypothesis (including the ASSUMED `similarity_absorbs`
    construction — see `JordanFormSpec`) and the Higham–Knight condition
    (18.13) with the printed constant `γ_{n+2}`, the computed vectors
    satisfy `‖fl(Aᵐ v₀)‖∞ → 0`.

    Still conditional on the `similarity_absorbs` axiom; the Theorem 18.1
    source row remains OPEN until that construction is discharged. -/
theorem higham_knight_18_1_fl_tendsto (fp : FPModel) (n : ℕ) (hn : 0 < n)
    (A X X_inv : Fin n → Fin n → ℝ)
    (hJ : JordanFormSpec n hn A X X_inv)
    (v0 : Fin n → ℝ) (hval : gammaValid fp (n + 2))
    (hCond : 4 * hJ.max_block_size * gamma fp (n + 2) *
      (infNorm X * infNorm X_inv) * infNorm A <
      (1 - hJ.spectral_radius) ^ hJ.max_block_size) :
    Filter.Tendsto
      (fun m => infNormVec (fl_matPowVecSeq fp n A v0 m))
      Filter.atTop (nhds 0) := by
  obtain ⟨C, q, hC, hq0, hq1, hbound⟩ :=
    higham_knight_18_1 n hn A X X_inv hJ
      (fl_matPowVecSeq fp n A v0) (gamma fp (n + 2))
      (gamma_nonneg fp hval)
      (computedMatPowVec_fl_matVec_gamma_add_two fp n A v0 hval)
      hCond
  exact computedMatPow_tendsto_zero_of_geometric n
    (fl_matPowVecSeq fp n A v0) C q hq0 hq1 hbound

/-- **Conditional reduction of Theorem 18.2** (Higham–Knight), algebraic
    `t = 1` form.  The book's proof of Theorem 18.2 reduces the
    pseudospectral hypothesis to Theorem 18.1 with `t = 1` (diagonalizable
    `A`), where condition (18.13) becomes
    `4 · c · κ∞(X) · ‖A‖∞ < 1 − ρ(A)`.  This theorem formalizes exactly
    that reduction target with the limit conclusion `‖v_m‖∞ → 0`.

    NOT the full printed Theorem 18.2: the pseudospectral packaging
    (`ρ_ε(A) < 1` with `ε = cₙu‖A‖₂`, eqs (18.8)–(18.9), the unique dominant
    eigenvalue and norm normalizations, and the O(ε²) proviso) is deferred —
    pseudospectra are absent from Mathlib and this repository.  Also
    conditional on the `similarity_absorbs` axiom via `higham_knight_18_1`;
    the Theorem 18.2 source row remains OPEN. -/
theorem higham_knight_18_2_diagonalizable (n : ℕ) (hn : 0 < n)
    (A X X_inv : Fin n → Fin n → ℝ)
    (hJ : JordanFormSpec n hn A X X_inv)
    (ht : hJ.max_block_size = 1)
    (v : ℕ → (Fin n → ℝ)) (c : ℝ) (hc : 0 ≤ c)
    (hComp : ComputedMatPowVec n A v c)
    (hCond : 4 * c * (infNorm X * infNorm X_inv) * infNorm A <
      1 - hJ.spectral_radius) :
    Filter.Tendsto (fun m => infNormVec (v m)) Filter.atTop (nhds 0) := by
  have hCond1 : 4 * hJ.max_block_size * c *
      (infNorm X * infNorm X_inv) * infNorm A <
      (1 - hJ.spectral_radius) ^ hJ.max_block_size := by
    rw [ht]
    simpa using hCond
  obtain ⟨C, q, hC, hq0, hq1, hbound⟩ :=
    higham_knight_18_1 n hn A X X_inv hJ v c hc hComp hCond1
  exact computedMatPow_tendsto_zero_of_geometric n v C q hq0 hq1 hbound

-- ============================================================
-- §18.2  Discharging `similarity_absorbs`: real-diagonalizable case (t = 1)
-- ============================================================

/-- Triangle inequality for the matrix ∞-norm (entrywise sum). -/
theorem infNorm_add_le {n : ℕ} (M N : Fin n → Fin n → ℝ) :
    infNorm (fun i j => M i j + N i j) ≤ infNorm M + infNorm N := by
  apply infNorm_le_of_row_sum_le
  · intro i
    calc ∑ j : Fin n, |M i j + N i j|
        ≤ ∑ j : Fin n, (|M i j| + |N i j|) :=
          Finset.sum_le_sum (fun j _ => abs_add_le _ _)
      _ = (∑ j : Fin n, |M i j|) + ∑ j : Fin n, |N i j| :=
          Finset.sum_add_distrib
      _ ≤ infNorm M + infNorm N :=
          add_le_add (row_sum_le_infNorm M i) (row_sum_le_infNorm N i)
  · exact add_nonneg (infNorm_nonneg M) (infNorm_nonneg N)

/-- Componentwise domination `|ΔA| ≤ η|A|` transfers to the matrix ∞-norm:
    `‖ΔA‖∞ ≤ η‖A‖∞`. -/
theorem infNorm_le_mul_of_abs_le_mul_abs {n : ℕ}
    (ΔA A : Fin n → Fin n → ℝ) {η : ℝ} (hη : 0 ≤ η)
    (hΔ : ∀ i j, |ΔA i j| ≤ η * |A i j|) :
    infNorm ΔA ≤ η * infNorm A := by
  apply infNorm_le_of_row_sum_le
  · intro i
    calc ∑ j : Fin n, |ΔA i j|
        ≤ ∑ j : Fin n, η * |A i j| :=
          Finset.sum_le_sum (fun j _ => hΔ i j)
      _ = η * ∑ j : Fin n, |A i j| := (Finset.mul_sum ..).symm
      _ ≤ η * infNorm A :=
          mul_le_mul_of_nonneg_left (row_sum_le_infNorm A i) hη
  · exact mul_nonneg hη (infNorm_nonneg A)

/-- A diagonal matrix with entries of modulus at most `ρ ≥ 0` has
    ∞-norm at most `ρ`. -/
theorem infNorm_diagonal_le {n : ℕ} (J : Fin n → Fin n → ℝ) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hdiag : ∀ i j, i ≠ j → J i j = 0)
    (hlam : ∀ i, |J i i| ≤ ρ) : infNorm J ≤ ρ := by
  apply infNorm_le_of_row_sum_le
  · intro i
    have hsingle : ∑ j : Fin n, |J i j| = |J i i| := by
      refine Finset.sum_eq_single i (fun b _ hb => ?_) (fun h => ?_)
      · rw [hdiag i b (Ne.symm hb)]; exact abs_zero
      · exact absurd (Finset.mem_univ i) h
    rw [hsingle]; exact hlam i
  · exact hρ0

/-- **Discharged `t = 1` construction (real-diagonalizable case).**

    If `A` is explicitly diagonalized over ℝ — `X⁻¹AX = J` with `J` diagonal
    and `|J i i| ≤ ρ < 1` — then the perturbation-absorbing similarity of
    Theorem 18.1's proof exists with `S = X` and NO scaling construction:
    for `|ΔA| ≤ η|A|`,
      `‖X⁻¹(A+ΔA)X‖∞ ≤ ‖J‖∞ + κ∞(X)·η·‖A‖∞ ≤ ρ + η·κ∞(X)·‖A‖∞ < 1`
    under the `t = 1` Higham–Knight condition `4·η·κ∞(X)·‖A‖∞ < 1 − ρ`.

    This PROVES `similarity_absorbs` (no assumption) for this class, covering
    e.g. symmetric matrices and any real matrix with real eigenvalues and a
    full real eigenbasis.  Here `ρ` is any bound on the eigenvalue moduli
    (the printed theorem uses `ρ(A)` itself, which is the sharpest choice).
    The general case (complex spectrum / defective `A`, `t > 1`) still
    requires the Jordan δ-scaling over ℂ and remains an open obligation. -/
def JordanFormSpec.ofRealDiagonal (n : ℕ) (hn : 0 < n)
    (A X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv)
    (hsim : matMul n X_inv (matMul n A X) = J)
    (hdiag : ∀ i j, i ≠ j → J i j = 0)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hlam : ∀ i, |J i i| ≤ ρ) :
    JordanFormSpec n hn A X X_inv where
  inv_right := hXr
  spectral_radius := ρ
  hr_nonneg := hρ0
  hr_lt_one := hρ1
  max_block_size := 1
  ht_pos := one_pos
  similarity_absorbs := by
    intro η hη hcond
    -- The t = 1 condition: 4·η·κ∞(X)·‖A‖∞ < 1 − ρ.
    have hcond' : 4 * (η * (infNorm X * infNorm X_inv) * infNorm A) < 1 - ρ := by
      have := hcond
      simpa [mul_assoc, Nat.cast_one] using this
    set K : ℝ := η * (infNorm X * infNorm X_inv) * infNorm A with hK
    have hK0 : 0 ≤ K := by
      apply mul_nonneg (mul_nonneg hη _) (infNorm_nonneg A)
      exact mul_nonneg (infNorm_nonneg X) (infNorm_nonneg X_inv)
    have hKlt : K < 1 - ρ := by linarith
    refine ⟨X, X_inv, ρ + K, hXr, by linarith, by linarith, ?_⟩
    intro ΔA hΔ
    -- X⁻¹(A+ΔA)X = J + X⁻¹ΔA X, entrywise.
    have hsplit : matMul n X_inv (matMul n (fun i j => A i j + ΔA i j) X) =
        fun i j => J i j + matMul n X_inv (matMul n ΔA X) i j := by
      rw [matMul_add_left n A ΔA X, matMul_add_right n X_inv
        (matMul n A X) (matMul n ΔA X), hsim]
    rw [hsplit]
    -- ‖X⁻¹ΔA X‖∞ ≤ κ∞(X)·η·‖A‖∞
    have hΔnorm : infNorm ΔA ≤ η * infNorm A :=
      infNorm_le_mul_of_abs_le_mul_abs ΔA A hη hΔ
    have h1 : infNorm (matMul n ΔA X) ≤ infNorm ΔA * infNorm X :=
      infNorm_matMul_le hn ΔA X
    have h2 : infNorm (matMul n X_inv (matMul n ΔA X)) ≤
        infNorm X_inv * (infNorm ΔA * infNorm X) :=
      (infNorm_matMul_le hn X_inv (matMul n ΔA X)).trans
        (mul_le_mul_of_nonneg_left h1 (infNorm_nonneg X_inv))
    have h3 : infNorm X_inv * (infNorm ΔA * infNorm X) ≤
        infNorm X_inv * ((η * infNorm A) * infNorm X) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hΔnorm (infNorm_nonneg X))
        (infNorm_nonneg X_inv)
    have hEq : infNorm X_inv * ((η * infNorm A) * infNorm X) = K := by
      rw [hK]; ring
    calc infNorm (fun i j => J i j + matMul n X_inv (matMul n ΔA X) i j)
        ≤ infNorm J + infNorm (matMul n X_inv (matMul n ΔA X)) :=
          infNorm_add_le J _
      _ ≤ ρ + K := by
          have hJn : infNorm J ≤ ρ := infNorm_diagonal_le J hρ0 hdiag hlam
          have := h2.trans h3
          rw [hEq] at this
          linarith

/-- **Axiom-free real-diagonalizable case of Theorem 18.1** (limit form,
    abstract error model): if `X⁻¹AX = J` is diagonal with `|J i i| ≤ ρ < 1`
    and the `t = 1` Higham–Knight condition `4·c·κ∞(X)·‖A‖∞ < 1 − ρ` holds,
    then any computed-power sequence with per-step budget `c` satisfies
    `‖v_m‖∞ → 0`.  No `similarity_absorbs` assumption: the construction is
    discharged by `JordanFormSpec.ofRealDiagonal`. -/
theorem higham_18_1_real_diagonalizable_tendsto (n : ℕ) (hn : 0 < n)
    (A X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv)
    (hsim : matMul n X_inv (matMul n A X) = J)
    (hdiag : ∀ i j, i ≠ j → J i j = 0)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hlam : ∀ i, |J i i| ≤ ρ)
    (v : ℕ → (Fin n → ℝ)) (c : ℝ) (hc : 0 ≤ c)
    (hComp : ComputedMatPowVec n A v c)
    (hCond : 4 * c * (infNorm X * infNorm X_inv) * infNorm A < 1 - ρ) :
    Filter.Tendsto (fun m => infNormVec (v m)) Filter.atTop (nhds 0) :=
  higham_knight_18_2_diagonalizable n hn A X X_inv
    (JordanFormSpec.ofRealDiagonal n hn A X X_inv J hXr hsim hdiag ρ hρ0 hρ1 hlam)
    rfl v c hc hComp hCond

/-- **Axiom-free real-diagonalizable case of Theorem 18.1 for the actual
    floating-point iteration**: with `X⁻¹AX = J` diagonal, `|J i i| ≤ ρ < 1`,
    and `4·γ_{n+2}·κ∞(X)·‖A‖∞ < 1 − ρ`, the computed vectors
    `fl(Aᵐ v₀)` (repeated `fl_matVec`) satisfy `‖fl(Aᵐ v₀)‖∞ → 0`.
    Fully end-to-end: concrete algorithm, concrete rounding model,
    no assumed construction. -/
theorem higham_18_1_real_diagonalizable_fl_tendsto (fp : FPModel)
    (n : ℕ) (hn : 0 < n)
    (A X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv)
    (hsim : matMul n X_inv (matMul n A X) = J)
    (hdiag : ∀ i j, i ≠ j → J i j = 0)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hlam : ∀ i, |J i i| ≤ ρ)
    (v0 : Fin n → ℝ) (hval : gammaValid fp (n + 2))
    (hCond : 4 * gamma fp (n + 2) * (infNorm X * infNorm X_inv) *
      infNorm A < 1 - ρ) :
    Filter.Tendsto
      (fun m => infNormVec (fl_matPowVecSeq fp n A v0 m))
      Filter.atTop (nhds 0) :=
  higham_18_1_real_diagonalizable_tendsto n hn A X X_inv J hXr hsim hdiag
    ρ hρ0 hρ1 hlam (fl_matPowVecSeq fp n A v0) (gamma fp (n + 2))
    (gamma_nonneg fp hval)
    (computedMatPowVec_fl_matVec_gamma_add_two fp n A v0 hval) hCond

-- ============================================================
-- §18.1  Exact arithmetic: eq (18.4), real-diagonalizable case
-- ============================================================

/-- Powers of a diagonal matrix are diagonal with powered entries. -/
theorem matPow_diagonal (n : ℕ) (J : Fin n → Fin n → ℝ)
    (hdiag : ∀ i j, i ≠ j → J i j = 0) (k : ℕ) :
    ∀ i j, matPow n J k i j = if i = j then (J i i) ^ k else 0 := by
  induction k with
  | zero =>
    intro i j
    show idMatrix n i j = _
    unfold idMatrix
    simp [pow_zero]
  | succ k ih =>
    intro i j
    show matMul n J (matPow n J k) i j = _
    unfold matMul
    rw [Finset.sum_eq_single i
      (fun l _ hl => by rw [hdiag i l (Ne.symm hl), zero_mul])
      (fun h => absurd (Finset.mem_univ i) h)]
    rw [ih i j]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos hij, pow_succ]; ring
    · rw [if_neg hij, if_neg hij, mul_zero]

/-- Similarity transport of matrix powers: if `X⁻¹AX = J` with two-sided
    inverse data, then `Aᵏ = X Jᵏ X⁻¹`. -/
theorem matPow_similarity (n : ℕ)
    (A X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n A X) = J) (k : ℕ) :
    matPow n A k = matMul n X (matMul n (matPow n J k) X_inv) := by
  have hXXinv : matMul n X X_inv = idMatrix n := by ext a b; exact hXr a b
  have hXinvX : matMul n X_inv X = idMatrix n := by ext a b; exact hXl a b
  have hA : A = matMul n X (matMul n J X_inv) := by
    calc A = matMul n (matMul n X X_inv)
              (matMul n A (matMul n X X_inv)) := by
            rw [hXXinv, matMul_id_left, matMul_id_right]
      _ = matMul n X (matMul n (matMul n X_inv (matMul n A X)) X_inv) := by
            simp only [matMul_assoc]
      _ = matMul n X (matMul n J X_inv) := by rw [hsim]
  induction k with
  | zero =>
    show idMatrix n = _
    have : matMul n (matPow n J 0) X_inv = X_inv := by
      show matMul n (idMatrix n) X_inv = X_inv
      exact matMul_id_left n X_inv
    rw [this, hXXinv]
  | succ k ih =>
    rw [matPow_succ n A k, ih, matPow_succ n J k]
    nth_rewrite 1 [hA]
    simp only [matMul_assoc]
    congr 1
    congr 1
    rw [← matMul_assoc, hXinvX, matMul_id_left]

/-- **Eq (18.4), upper bound, real-diagonalizable ∞-norm case**
    (Higham 2nd ed., §18.1, p. 343): if `X⁻¹AX = J` is diagonal with
    `|J i i| ≤ ρ`, then `‖Aᵏ‖∞ ≤ κ∞(X) · ρᵏ`.

    Honest scope: the printed (18.4) is stated for every p-norm and complex
    diagonalizable `A`; this closes the `p = ∞`, real-spectrum subcase. -/
theorem higham_eq_18_4_upper_real_diagonalizable (n : ℕ) (hn : 0 < n)
    (A X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n A X) = J)
    (hdiag : ∀ i j, i ≠ j → J i j = 0)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hlam : ∀ i, |J i i| ≤ ρ) (k : ℕ) :
    infNorm (matPow n A k) ≤ (infNorm X * infNorm X_inv) * ρ ^ k := by
  rw [matPow_similarity n A X X_inv J hXr hXl hsim k]
  have hJk : infNorm (matPow n J k) ≤ ρ ^ k := by
    refine infNorm_diagonal_le _ (pow_nonneg hρ0 k)
      (fun i j hij => by rw [matPow_diagonal n J hdiag k i j, if_neg hij])
      (fun i => ?_)
    rw [matPow_diagonal n J hdiag k i i, if_pos rfl]
    calc |J i i ^ k| = |J i i| ^ k := abs_pow _ _
      _ ≤ ρ ^ k := pow_le_pow_left₀ (abs_nonneg _) (hlam i) k
  calc infNorm (matMul n X (matMul n (matPow n J k) X_inv))
      ≤ infNorm X * infNorm (matMul n (matPow n J k) X_inv) :=
        infNorm_matMul_le hn _ _
    _ ≤ infNorm X * (infNorm (matPow n J k) * infNorm X_inv) :=
        mul_le_mul_of_nonneg_left (infNorm_matMul_le hn _ _)
          (infNorm_nonneg X)
    _ ≤ infNorm X * (ρ ^ k * infNorm X_inv) := by
        apply mul_le_mul_of_nonneg_left _ (infNorm_nonneg X)
        exact mul_le_mul_of_nonneg_right hJk (infNorm_nonneg X_inv)
    _ = (infNorm X * infNorm X_inv) * ρ ^ k := by ring

/-- **Eq (18.4), lower bound, real-diagonalizable ∞-norm case**
    (Higham 2nd ed., §18.1, p. 343): every eigenvalue modulus power is a
    lower bound, `|J j j|ᵏ ≤ ‖Aᵏ‖∞`; taking the dominant `j` gives the
    printed `ρ(A)ᵏ ≤ ‖Aᵏ‖_p` for `p = ∞` and real spectrum. -/
theorem higham_eq_18_4_lower_real_diagonalizable (n : ℕ) (hn : 0 < n)
    (A X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n A X) = J)
    (hdiag : ∀ i j, i ≠ j → J i j = 0)
    (j : Fin n) (k : ℕ) :
    |J j j| ^ k ≤ infNorm (matPow n A k) := by
  have hXXinv : matMul n X X_inv = idMatrix n := by ext a b; exact hXr a b
  -- Eigencolumn: x := column j of X, so A·X = X·J gives (Aᵏx)ᵢ = (J j j)ᵏ xᵢ.
  set x : Fin n → ℝ := fun i => X i j with hxdef
  have hAX : matMul n A X = matMul n X J := by
    have h := congrArg (matMul n X) hsim
    rwa [← matMul_assoc, hXXinv, matMul_id_left] at h
  -- one-step eigen action
  have hstep : ∀ i, matMulVec n A x i = J j j * x i := by
    intro i
    have h1 : matMulVec n A x i = matMul n A X i j := by
      unfold matMulVec matMul; rfl
    have h2 : matMul n X J i j = J j j * x i := by
      unfold matMul
      rw [Finset.sum_eq_single j
        (fun l _ hl => by rw [hdiag l j hl, mul_zero])
        (fun h => absurd (Finset.mem_univ j) h)]
      rw [hxdef]; ring
    rw [h1, hAX, h2]
  -- k-step eigen action
  have hact : ∀ k, ∀ i, matMulVec n (matPow n A k) x i = (J j j) ^ k * x i := by
    intro k
    induction k with
    | zero =>
      intro i
      show matMulVec n (idMatrix n) x i = _
      unfold matMulVec idMatrix
      simp [Finset.sum_ite_eq, pow_zero]
    | succ k ih =>
      intro i
      have h1 : matMulVec n (matPow n A (k + 1)) x i =
          matMulVec n A (matMulVec n (matPow n A k) x) i := by
        rw [matPow_succ n A k]
        exact matMulVec_matMul n A (matPow n A k) x i
      have h2 : matMulVec n A (matMulVec n (matPow n A k) x) i =
          matMulVec n A (fun l => (J j j) ^ k * x l) i := by
        have hfun : matMulVec n (matPow n A k) x =
            (fun l => (J j j) ^ k * x l) := funext ih
        rw [hfun]
      have h3 : matMulVec n A (fun l => (J j j) ^ k * x l) i =
          (J j j) ^ k * matMulVec n A x i := by
        unfold matMulVec
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun l _ => by ring)
      rw [h1, h2, h3, hstep i, pow_succ]; ring
  -- x has a nonzero entry (X is invertible)
  have hone : ∑ l : Fin n, X_inv j l * X l j = 1 := by
    have := hXl j j
    simpa using this
  have hxne : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    have : ∑ l : Fin n, X_inv j l * X l j = 0 :=
      Finset.sum_eq_zero (fun l _ => by
        have hxl : X l j = 0 := h l
        rw [hxl, mul_zero])
    rw [this] at hone
    exact one_ne_zero hone.symm
  have hxpos : 0 < infNormVec x := by
    obtain ⟨i₁, hi₁⟩ := hxne
    calc (0:ℝ) < |x i₁| := abs_pos.mpr hi₁
      _ ≤ infNormVec x := abs_le_infNormVec x i₁
  -- sup-attaining index and the norm chain
  obtain ⟨i₀, hi₀⟩ := infNormVec_exists_abs_eq hn x
  have hchain : |J j j| ^ k * infNormVec x ≤
      infNorm (matPow n A k) * infNormVec x := by
    calc |J j j| ^ k * infNormVec x
        = |J j j| ^ k * |x i₀| := by rw [hi₀]
      _ = |(J j j) ^ k * x i₀| := by rw [abs_mul, abs_pow]
      _ = |matMulVec n (matPow n A k) x i₀| := by rw [hact k i₀]
      _ ≤ infNormVec (matMulVec n (matPow n A k) x) :=
          abs_le_infNormVec _ i₀
      _ ≤ infNorm (matPow n A k) * infNormVec x :=
          infNormVec_matMulVec_le hn _ _
  exact le_of_mul_le_mul_right hchain hxpos

-- ============================================================
-- §18.2  Eq (18.12): weighted (Collatz–Wielandt) certificate form
-- ============================================================

/-- Weighted power bound: if `w > 0` satisfies `|A|·w ≤ θ·w` componentwise
    (a Collatz–Wielandt certificate, so `ρ(|A|) ≤ θ`), then
    `(|A|ᵐ·u)ᵢ ≤ M·θᵐ·wᵢ` for any `|u| ≤ M·w`. -/
theorem matPow_abs_weighted_bound (n : ℕ) (A : Fin n → Fin n → ℝ)
    (w : Fin n → ℝ) (θ : ℝ) (hθ0 : 0 ≤ θ)
    (hAw : ∀ i, ∑ j : Fin n, |A i j| * w j ≤ θ * w i)
    (u : Fin n → ℝ) (M : ℝ) (hM0 : 0 ≤ M)
    (hu : ∀ j, u j ≤ M * w j) (hu0 : ∀ j, 0 ≤ u j) (m : ℕ) :
    ∀ i, matMulVec n (matPow n (absMatrix n A) m) u i ≤ M * θ ^ m * w i := by
  induction m with
  | zero =>
    intro i
    have hid : matMulVec n (matPow n (absMatrix n A) 0) u i = u i := by
      show matMulVec n (idMatrix n) u i = u i
      unfold matMulVec idMatrix
      simp [Finset.sum_ite_eq]
    rw [hid, pow_zero, mul_one]
    exact hu i
  | succ m ih =>
    intro i
    have hsplit : matMulVec n (matPow n (absMatrix n A) (m + 1)) u i =
        ∑ j : Fin n, |A i j| *
          matMulVec n (matPow n (absMatrix n A) m) u j := by
      rw [matPow_succ n (absMatrix n A) m]
      rw [matMulVec_matMul n (absMatrix n A) (matPow n (absMatrix n A) m) u i]
      unfold matMulVec absMatrix
      rfl
    have hnn : ∀ j, 0 ≤ matMulVec n (matPow n (absMatrix n A) m) u j := by
      intro j
      unfold matMulVec
      apply Finset.sum_nonneg
      intro l _
      exact mul_nonneg (matPow_nonneg n (absMatrix n A)
        (fun a b => abs_nonneg (A a b)) m j l) (hu0 l)
    rw [hsplit]
    calc ∑ j : Fin n, |A i j| *
          matMulVec n (matPow n (absMatrix n A) m) u j
        ≤ ∑ j : Fin n, |A i j| * (M * θ ^ m * w j) := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_left (ih j) (abs_nonneg _)
      _ = M * θ ^ m * ∑ j : Fin n, |A i j| * w j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ => by ring)
      _ ≤ M * θ ^ m * (θ * w i) :=
          mul_le_mul_of_nonneg_left (hAw i)
            (mul_nonneg hM0 (pow_nonneg hθ0 m))
      _ = M * θ ^ (m + 1) * w i := by rw [pow_succ]; ring

/-- **Eq (18.12), Collatz–Wielandt certificate form** (Higham 2nd ed., §18.2,
    p. 347): if a positive weight vector `w` certifies `|A|·w ≤ θ·w`
    (equivalently `ρ(|A|) ≤ θ` — the certificate exists for every
    `θ > ρ(|A|)` by Perron–Frobenius, which is not needed here) and
    `(1+c)·θ < 1`, then every computed-power sequence with per-step
    componentwise budget `c` satisfies `‖v_m‖∞ → 0`.

    This is strictly sharper than the `‖A‖∞`-surrogate
    `matPow_convergence_bound` (take `w ≡ 1`, `θ = ‖A‖∞`) and renders the
    printed sufficient condition `ρ(|A|) < 1/(1+γ_{n+2})` up to the
    certificate/spectral-radius equivalence; the literal `ρ(|A|)` statement
    remains open pending nonneg-matrix spectral-radius theory. -/
theorem matPow_convergence_weighted (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (w : Fin n → ℝ) (θ : ℝ) (hθ0 : 0 ≤ θ)
    (hAw : ∀ i, ∑ j : Fin n, |A i j| * w j ≤ θ * w i)
    (v : ℕ → (Fin n → ℝ)) (c : ℝ) (hc : 0 ≤ c)
    (hComp : ComputedMatPowVec n A v c)
    (M : ℝ) (hM0 : 0 ≤ M) (hv0 : ∀ j, |v 0 j| ≤ M * w j)
    (hq : (1 + c) * θ < 1) :
    Filter.Tendsto (fun m => infNormVec (v m)) Filter.atTop (nhds 0) := by
  have hq0 : 0 ≤ (1 + c) * θ := mul_nonneg (by linarith) hθ0
  -- componentwise: |v m i| ≤ M·((1+c)θ)ᵐ·w i
  have hbound : ∀ m i, |v m i| ≤ M * ((1 + c) * θ) ^ m * w i := by
    intro m i
    have h1 := matPow_componentwise_bound n A v c hc hComp m i
    have h2 := matPow_abs_weighted_bound n A w θ hθ0 hAw
      (absVec n (v 0)) M hM0
      (fun j => by
        have : absVec n (v 0) j = |v 0 j| := rfl
        rw [this]; exact hv0 j)
      (fun j => abs_nonneg _) m i
    calc |v m i|
        ≤ (1 + c) ^ m *
          matMulVec n (matPow n (absMatrix n A) m) (absVec n (v 0)) i := h1
      _ ≤ (1 + c) ^ m * (M * θ ^ m * w i) :=
          mul_le_mul_of_nonneg_left h2 (pow_nonneg (by linarith) m)
      _ = M * ((1 + c) * θ) ^ m * w i := by rw [mul_pow]; ring
  -- normwise: ‖v m‖∞ ≤ (M·‖w‖∞)·((1+c)θ)ᵐ, then squeeze
  have hnorm : ∀ m, infNormVec (v m) ≤
      M * infNormVec w * ((1 + c) * θ) ^ m := by
    intro m
    apply infNormVec_le_of_abs_le
    · intro i
      calc |v m i| ≤ M * ((1 + c) * θ) ^ m * w i := hbound m i
        _ ≤ M * ((1 + c) * θ) ^ m * infNormVec w := by
            apply mul_le_mul_of_nonneg_left _
              (mul_nonneg hM0 (pow_nonneg hq0 m))
            calc w i ≤ |w i| := le_abs_self _
              _ ≤ infNormVec w := abs_le_infNormVec w i
        _ = M * infNormVec w * ((1 + c) * θ) ^ m := by ring
    · exact mul_nonneg (mul_nonneg hM0 (infNormVec_nonneg w))
        (pow_nonneg hq0 m)
  have hpow : Filter.Tendsto (fun m : ℕ => ((1 + c) * θ) ^ m)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq
  have htop : Filter.Tendsto
      (fun m => M * infNormVec w * ((1 + c) * θ) ^ m)
      Filter.atTop (nhds 0) := by
    simpa using hpow.const_mul (M * infNormVec w)
  exact squeeze_zero (fun m => infNormVec_nonneg _) hnorm htop

/-- **Eq (18.12), certificate form, for the actual floating-point iteration**
    (Higham 2nd ed., §18.2, p. 347): with a Collatz–Wielandt certificate
    `|A|·w ≤ θ·w`, `w > 0`, and `(1+γ_{n+2})·θ < 1` — the printed
    `ρ(|A|) < 1/(1+γ_{n+2})` up to the certificate equivalence — the
    computed vectors `fl(Aᵐ v₀)` satisfy `‖fl(Aᵐ v₀)‖∞ → 0`. -/
theorem matPow_convergence_weighted_fl (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (w : Fin n → ℝ) (θ : ℝ) (hθ0 : 0 ≤ θ)
    (hAw : ∀ i, ∑ j : Fin n, |A i j| * w j ≤ θ * w i)
    (v0 : Fin n → ℝ) (hval : gammaValid fp (n + 2))
    (M : ℝ) (hM0 : 0 ≤ M) (hv0 : ∀ j, |v0 j| ≤ M * w j)
    (hq : (1 + gamma fp (n + 2)) * θ < 1) :
    Filter.Tendsto
      (fun m => infNormVec (fl_matPowVecSeq fp n A v0 m))
      Filter.atTop (nhds 0) :=
  matPow_convergence_weighted n A w θ hθ0 hAw
    (fl_matPowVecSeq fp n A v0) (gamma fp (n + 2))
    (gamma_nonneg fp hval)
    (computedMatPowVec_fl_matVec_gamma_add_two fp n A v0 hval)
    M hM0 hv0 hq

end NumStability
