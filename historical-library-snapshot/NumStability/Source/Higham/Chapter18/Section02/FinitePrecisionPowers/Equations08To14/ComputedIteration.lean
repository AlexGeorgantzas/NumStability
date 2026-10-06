import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.MatrixPowers.ComputedIteration.Model
import NumStability.Analysis.LinearOperators.MatrixPowers.ExactNormBounds.Real
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# Source.Higham.Chapter18.Section02.FinitePrecisionPowers.Equations08To14.ComputedIteration

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

-- Algorithms/MatrixPowers.lean
--
-- Higham Chapter 18: Error analysis of matrix powers.
--
-- Covers §18.2 (finite precision bounds for computed A^m via repeated
-- matrix-vector products) and the similarity-based convergence engine
-- underlying Theorem 18.1 (Higham–Knight).













namespace NumStability

open scoped BigOperators

-- ============================================================
-- §18.2  Backward error model for computed matrix powers
-- ============================================================


























-- ============================================================
-- §18.2  Concrete floating-point realization of (18.10)–(18.11)
-- ============================================================






































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






















































































-- ============================================================
-- §18.2  Limit form of the convergence conclusion
-- ============================================================
























-- ============================================================
-- §18.2  End-to-end conditional forms with the limit conclusion
-- ============================================================






























































-- ============================================================
-- §18.2  Discharging `similarity_absorbs`: real-diagonalizable case (t = 1)
-- ============================================================


































































































































































-- ============================================================
-- §18.1  Exact arithmetic: eq (18.4), real-diagonalizable case
-- ============================================================












































































































































































-- ============================================================
-- §18.2  Eq (18.12): weighted (Collatz–Wielandt) certificate form
-- ============================================================


















































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
