-- Algorithms/MatrixPowersJordan.lean
--
-- Higham Chapter 18: Error analysis of matrix powers — the defective
-- real-spectrum case of Theorem 18.1 (Higham–Knight).
--
-- Discharges `JordanFormSpec.similarity_absorbs` for real Jordan-form data
-- with block size t ≥ 2 via the δ-scaling construction of the book's proof
-- (Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §18.2,
-- pp. 347–348): S = X·D with D = diag(p_i), p_i = β^(run length at i),
-- β = (1−ρ)(t−1)/t, together with the (1+1/m)^m < e < 4 optimisation that
-- turns the printed condition 4t·η·κ∞(X)·‖A‖∞ < (1−ρ)^t into a per-step
-- contraction ‖S⁻¹(A+ΔA)S‖∞ ≤ q < 1.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import NumStability.Algorithms.MatrixPowers
namespace NumStability

open scoped BigOperators

-- ============================================================
-- Scalar preliminaries: the (1 + 1/m)^m < e < 4 optimisation
-- ============================================================

/-- **The Euler-bound step of Theorem 18.1's proof** (Higham, Accuracy and
    Stability of Numerical Algorithms, 2nd ed., §18.2, Theorem 18.1 proof,
    pp. 347–348): `(1 + 1/m)^m < 4` for `m ≥ 1`, via
    `(1 + 1/m)^m ≤ e < 4`.  Pure real analysis; no matrix content. -/
theorem one_add_one_div_pow_lt_four (m : ℕ) (hm : 1 ≤ m) :
    (1 + 1 / (m : ℝ)) ^ m < 4 := by
  have hM0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hinv0 : (0 : ℝ) < 1 / (m : ℝ) := by
    apply div_pos one_pos hM0
  have h1 : (1 : ℝ) + 1 / (m : ℝ) ≤ Real.exp (1 / (m : ℝ)) := by
    have h := Real.add_one_le_exp (1 / (m : ℝ))
    linarith
  have h2 : (1 + 1 / (m : ℝ)) ^ m ≤ Real.exp (1 / (m : ℝ)) ^ m :=
    pow_le_pow_left₀ (by linarith) h1 m
  have h3 : Real.exp (1 / (m : ℝ)) ^ m = Real.exp ((m : ℝ) * (1 / (m : ℝ))) :=
    (Real.exp_nat_mul _ m).symm
  have h4 : (m : ℝ) * (1 / (m : ℝ)) = 1 := by
    rw [mul_one_div, div_self hM0.ne']
  have h5 : Real.exp 1 < 4 :=
    lt_trans Real.exp_one_lt_d9 (by norm_num)
  calc (1 + 1 / (m : ℝ)) ^ m
      ≤ Real.exp (1 / (m : ℝ)) ^ m := h2
    _ = Real.exp ((m : ℝ) * (1 / (m : ℝ))) := h3
    _ = Real.exp 1 := by rw [h4]
    _ < 4 := h5

/-- **The `4t` inequality of Theorem 18.1's proof** (Higham, Accuracy and
    Stability of Numerical Algorithms, 2nd ed., §18.2, Theorem 18.1 proof,
    pp. 347–348): `t^t ≤ 4·t·(t−1)^(t−1)` over ℝ for `t ≥ 2`, equivalent
    to `(1 + 1/(t−1))^(t−1) < 4`.  Pure real analysis. -/
theorem pow_self_le_four_mul (t : ℕ) (ht2 : 2 ≤ t) :
    ((t : ℝ)) ^ t ≤ 4 * (t : ℝ) * ((t : ℝ) - 1) ^ (t - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
  have hm1 : 1 ≤ m := by omega
  have hM0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  rw [hcast, Nat.add_sub_cancel]
  have hsub : (m : ℝ) + 1 - 1 = (m : ℝ) := by ring
  rw [hsub]
  -- goal: (M+1)^(m+1) ≤ 4 * (M+1) * M^m
  have h4 := one_add_one_div_pow_lt_four m hm1
  have heq : (1 : ℝ) + 1 / (m : ℝ) = ((m : ℝ) + 1) / (m : ℝ) := by
    field_simp
  rw [heq, div_pow] at h4
  have hMm : (0 : ℝ) < (m : ℝ) ^ m := pow_pos hM0 m
  rw [div_lt_iff₀ hMm] at h4
  -- h4 : (M+1)^m < 4 * M^m
  calc ((m : ℝ) + 1) ^ (m + 1)
      = ((m : ℝ) + 1) * ((m : ℝ) + 1) ^ m := by rw [pow_succ]; ring
    _ ≤ ((m : ℝ) + 1) * (4 * (m : ℝ) ^ m) :=
        mul_le_mul_of_nonneg_left h4.le (by linarith)
    _ = 4 * ((m : ℝ) + 1) * (m : ℝ) ^ m := by ring

-- ============================================================
-- The scaling margin β = (1−ρ)(t−1)/t of the δ-scaling construction
-- ============================================================

/-- The geometric decay ratio `β = (1−ρ)(t−1)/t` of the diagonal δ-scaling
    in Theorem 18.1's proof (Higham, 2nd ed., §18.2, pp. 347–348): the book's
    `D(δ) = diag(1, δ, …, δ^{nᵢ−1})` with `δ = 1−ρ−ε` and `ε = (1−ρ)/t`.
    For `0 ≤ ρ < 1` and `t ≥ 2` we have `0 < β < 1`. -/
noncomputable def jordanBeta (ρ : ℝ) (t : ℕ) : ℝ :=
  (1 - ρ) * ((t : ℝ) - 1) / (t : ℝ)

/-- `β > 0` when `ρ < 1` and `t ≥ 2`. -/
theorem jordanBeta_pos (ρ : ℝ) (t : ℕ) (hρ1 : ρ < 1) (ht2 : 2 ≤ t) :
    0 < jordanBeta ρ t := by
  have hT : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht2
  unfold jordanBeta
  apply div_pos (mul_pos (by linarith) (by linarith)) (by linarith)

/-- `β < 1` when `0 ≤ ρ` and `t ≥ 2`. -/
theorem jordanBeta_lt_one (ρ : ℝ) (t : ℕ) (hρ0 : 0 ≤ ρ) (ht2 : 2 ≤ t) :
    jordanBeta ρ t < 1 := by
  have hT : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht2
  have h1 : 0 ≤ ρ * ((t : ℝ) - 1) := mul_nonneg hρ0 (by linarith)
  unfold jordanBeta
  rw [div_lt_one (by linarith)]
  nlinarith [h1]

/-- The exact budget split `ρ + β = 1 − ε` with `ε = (1−ρ)/t`
    (eq (18.14)-adjacent bookkeeping in Theorem 18.1's proof). -/
theorem jordanBeta_add_eq (ρ : ℝ) (t : ℕ) (ht2 : 2 ≤ t) :
    ρ + jordanBeta ρ t = 1 - (1 - ρ) / (t : ℝ) := by
  have hT : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht2
  have hTne : (t : ℝ) ≠ 0 := by linarith
  unfold jordanBeta
  field_simp
  ring

/-- **The scalar core of condition (18.13)** (Higham, Accuracy and Stability
    of Numerical Algorithms, 2nd ed., §18.2, Theorem 18.1 proof, pp. 347–348):
    from `4·t·K < (1−ρ)^t` deduce `K < ε·β^(t−1)` where `ε = (1−ρ)/t` and
    `β = (1−ρ)(t−1)/t`, using `t^t ≤ 4·t·(t−1)^(t−1)`. -/
theorem higham_scaling_margin (t : ℕ) (ht2 : 2 ≤ t) (ρ K : ℝ)
    (hρ1 : ρ < 1) (hK0 : 0 ≤ K)
    (hcond : 4 * (t : ℝ) * K < (1 - ρ) ^ t) :
    K < (1 - ρ) / (t : ℝ) * jordanBeta ρ t ^ (t - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
  have hm1 : 1 ≤ m := by omega
  have hM0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hs0 : (0 : ℝ) < 1 - ρ := by linarith
  have hT0 : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  have hβ : jordanBeta ρ (m + 1) = (1 - ρ) * (m : ℝ) / ((m : ℝ) + 1) := by
    unfold jordanBeta
    rw [hcast]
    ring
  rw [Nat.add_sub_cancel, hβ, hcast]
  rw [hcast] at hcond
  have hkey : (1 - ρ) / ((m : ℝ) + 1) * ((1 - ρ) * (m : ℝ) / ((m : ℝ) + 1)) ^ m
      = (1 - ρ) ^ (m + 1) * (m : ℝ) ^ m / ((m : ℝ) + 1) ^ (m + 1) := by
    rw [div_pow, mul_pow, div_mul_div_comm, ← pow_succ']
    congr 1
    ring
  rw [hkey, lt_div_iff₀ (pow_pos hT0 (m + 1))]
  -- goal: K * (M+1)^(m+1) < (1-ρ)^(m+1) * M^m
  have hps := pow_self_le_four_mul (m + 1) (by omega)
  rw [hcast, Nat.add_sub_cancel] at hps
  have hsub : (m : ℝ) + 1 - 1 = (m : ℝ) := by ring
  rw [hsub] at hps
  calc K * ((m : ℝ) + 1) ^ (m + 1)
      ≤ K * (4 * ((m : ℝ) + 1) * (m : ℝ) ^ m) :=
        mul_le_mul_of_nonneg_left hps hK0
    _ = (4 * ((m : ℝ) + 1) * K) * (m : ℝ) ^ m := by ring
    _ < (1 - ρ) ^ (m + 1) * (m : ℝ) ^ m :=
        mul_lt_mul_of_pos_right hcond (pow_pos hM0 m)

-- ============================================================
-- Diagonal scaling matrices: inverse, entries, norms
-- ============================================================

/-- Pointwise-inverse diagonal pair: `diag(p) · diag(q) = I` when
    `p i · q i = 1` for all `i`. -/
theorem diagMatrix_isRightInverse (n : ℕ) (p q : Fin n → ℝ)
    (hpq : ∀ i, p i * q i = 1) :
    IsRightInverse n (diagMatrix p) (diagMatrix q) := by
  intro i j
  show matMul n (diagMatrix p) (diagMatrix q) i j = if i = j then 1 else 0
  rw [matMul_diagMatrix_left p (diagMatrix q) i j]
  unfold diagMatrix
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, if_pos rfl, hpq i]
  · rw [if_neg hij, if_neg hij, mul_zero]

/-- Entrywise formula for the two-sided diagonal conjugation:
    `(diag(q) · J · diag(p))_{ij} = q_i · J_{ij} · p_j`. -/
theorem diagMatrix_conj_entry {n : ℕ} (J : Fin n → Fin n → ℝ)
    (p q : Fin n → ℝ) (i j : Fin n) :
    matMul n (diagMatrix q) (matMul n J (diagMatrix p)) i j
      = q i * J i j * p j := by
  rw [matMul_diagMatrix_left q (matMul n J (diagMatrix p)) i j,
    matMul_diagMatrix_right J p i j, ← mul_assoc]

/-- ∞-norm bound for a diagonal matrix from an entrywise bound. -/
theorem infNorm_diagMatrix_le {n : ℕ} (p : Fin n → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hp : ∀ i, |p i| ≤ c) : infNorm (diagMatrix p) ≤ c := by
  apply infNorm_diagonal_le (diagMatrix p) hc
  · intro i j hij
    simp [diagMatrix, hij]
  · intro i
    have h : diagMatrix p i i = p i := by simp [diagMatrix]
    rw [h]
    exact hp i

-- ============================================================
-- The scaled bidiagonal row-sum bound ‖D⁻¹ J D‖∞ ≤ ρ + β
-- ============================================================

/-- **Row sums of the scaled Jordan matrix** (Higham, 2nd ed., §18.2,
    Theorem 18.1 proof, pp. 347–348): with `p` a scaling vector satisfying
    the run-step law `p_j = β·p_i` across nonzero superdiagonal entries, each
    row sum of `|D⁻¹ J D|` (entries `(p_i)⁻¹ J_{ij} p_j`) is at most `ρ + β`. -/
theorem jordan_conj_row_sum_le (n : ℕ) (J : Fin n → Fin n → ℝ)
    (p : Fin n → ℝ) (ρ β : ℝ) (hβ0 : 0 ≤ β)
    (hshape : ∀ i j : Fin n, (j : ℕ) ≠ (i : ℕ) → (j : ℕ) ≠ (i : ℕ) + 1 → J i j = 0)
    (hdiagbd : ∀ i, |J i i| ≤ ρ)
    (hsup : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → |J i j| ≤ 1)
    (hp0 : ∀ i, 0 < p i)
    (hpstep : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → J i j ≠ 0 → p j = β * p i)
    (i : Fin n) :
    ∑ j : Fin n, |(p i)⁻¹ * J i j * p j| ≤ ρ + β := by
  have hpne : p i ≠ 0 := (hp0 i).ne'
  have hdiagentry : (p i)⁻¹ * J i i * p i = J i i := by
    rw [mul_comm ((p i)⁻¹) (J i i), mul_assoc, inv_mul_cancel₀ hpne, mul_one]
  by_cases hi : (i : ℕ) + 1 < n
  · -- A successor index exists: at most two nonzero entries in row i.
    have hii' : i ≠ (⟨(i : ℕ) + 1, hi⟩ : Fin n) := by
      intro h
      have h1 : (i : ℕ) = (i : ℕ) + 1 := congrArg Fin.val h
      omega
    have hzero : ∀ j : Fin n, j ≠ i → j ≠ (⟨(i : ℕ) + 1, hi⟩ : Fin n) →
        J i j = 0 := by
      intro j hj1 hj2
      apply hshape i j
      · exact fun h => hj1 (Fin.eq_of_val_eq h)
      · exact fun h => hj2 (Fin.eq_of_val_eq h)
    have hsub : ∑ j ∈ ({i, ⟨(i : ℕ) + 1, hi⟩} : Finset (Fin n)),
          |(p i)⁻¹ * J i j * p j|
        = ∑ j : Fin n, |(p i)⁻¹ * J i j * p j| := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
      rw [hzero j hj.1 hj.2, mul_zero, zero_mul, abs_zero]
    rw [← hsub, Finset.sum_pair hii']
    have hd : |(p i)⁻¹ * J i i * p i| ≤ ρ := by
      rw [hdiagentry]
      exact hdiagbd i
    have hs : |(p i)⁻¹ * J i (⟨(i : ℕ) + 1, hi⟩ : Fin n) *
        p (⟨(i : ℕ) + 1, hi⟩ : Fin n)| ≤ β := by
      by_cases hJ : J i (⟨(i : ℕ) + 1, hi⟩ : Fin n) = 0
      · rw [hJ, mul_zero, zero_mul, abs_zero]
        exact hβ0
      · have hstep := hpstep i (⟨(i : ℕ) + 1, hi⟩ : Fin n) rfl hJ
        have hentry : (p i)⁻¹ * J i (⟨(i : ℕ) + 1, hi⟩ : Fin n) *
            p (⟨(i : ℕ) + 1, hi⟩ : Fin n)
            = β * J i (⟨(i : ℕ) + 1, hi⟩ : Fin n) := by
          rw [hstep]
          have hre : (p i)⁻¹ * J i (⟨(i : ℕ) + 1, hi⟩ : Fin n) * (β * p i)
              = β * J i (⟨(i : ℕ) + 1, hi⟩ : Fin n) * ((p i)⁻¹ * p i) := by
            ring
          rw [hre, inv_mul_cancel₀ hpne, mul_one]
        rw [hentry, abs_mul, abs_of_nonneg hβ0]
        have hJb := hsup i (⟨(i : ℕ) + 1, hi⟩ : Fin n) rfl
        calc β * |J i (⟨(i : ℕ) + 1, hi⟩ : Fin n)|
            ≤ β * 1 := mul_le_mul_of_nonneg_left hJb hβ0
          _ = β := mul_one β
    exact add_le_add hd hs
  · -- Last row: only the diagonal entry survives.
    have hzero : ∀ j : Fin n, j ≠ i → J i j = 0 := by
      intro j hj
      apply hshape i j
      · exact fun h => hj (Fin.eq_of_val_eq h)
      · intro h
        have hlt := j.isLt
        omega
    have hsingle : ∑ j : Fin n, |(p i)⁻¹ * J i j * p j|
        = |(p i)⁻¹ * J i i * p i| := by
      apply Finset.sum_eq_single i
      · intro j _ hj
        rw [hzero j hj, mul_zero, zero_mul, abs_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [hsingle, hdiagentry]
    have h1 := hdiagbd i
    linarith

/-- **The contraction bound ‖D⁻¹ J D‖∞ ≤ ρ + β** for the δ-scaled Jordan
    matrix (Higham, 2nd ed., §18.2, Theorem 18.1 proof, pp. 347–348). -/
theorem infNorm_jordan_conj_le (n : ℕ) (J : Fin n → Fin n → ℝ)
    (p : Fin n → ℝ) (ρ β : ℝ) (hρ0 : 0 ≤ ρ) (hβ0 : 0 ≤ β)
    (hshape : ∀ i j : Fin n, (j : ℕ) ≠ (i : ℕ) → (j : ℕ) ≠ (i : ℕ) + 1 → J i j = 0)
    (hdiagbd : ∀ i, |J i i| ≤ ρ)
    (hsup : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → |J i j| ≤ 1)
    (hp0 : ∀ i, 0 < p i)
    (hpstep : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → J i j ≠ 0 → p j = β * p i) :
    infNorm (matMul n (diagMatrix fun a => (p a)⁻¹) (matMul n J (diagMatrix p)))
      ≤ ρ + β := by
  apply infNorm_le_of_row_sum_le
  · intro i
    calc ∑ j : Fin n, |matMul n (diagMatrix fun a => (p a)⁻¹)
          (matMul n J (diagMatrix p)) i j|
        = ∑ j : Fin n, |(p i)⁻¹ * J i j * p j| := by
          apply Finset.sum_congr rfl
          intro j _
          simp only [diagMatrix_conj_entry]
      _ ≤ ρ + β := jordan_conj_row_sum_le n J p ρ β hβ0 hshape hdiagbd hsup
          hp0 hpstep i
  · exact add_nonneg hρ0 hβ0

-- ============================================================
-- Run lengths of superdiagonal 1-chains and the scaling vector
-- ============================================================

/-- Length of the run of consecutive nonzero superdiagonal entries of `J`
    ending at position `k`: `r 0 = 0` and `r (k+1) = r k + 1` if the
    superdiagonal entry `J_{k,k+1}` is nonzero (and `k+1 < n`), else `0`.
    A maximal Jordan block size of `t` corresponds to `r k ≤ t − 1` for
    all `k`. -/
noncomputable def jordanRunLength (n : ℕ) (J : Fin n → Fin n → ℝ) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
      if h : k + 1 < n then
        if J ⟨k, Nat.lt_of_succ_lt h⟩ ⟨k + 1, h⟩ ≠ 0 then
          jordanRunLength n J k + 1
        else 0
      else 0

/-- Step law of the run length across a nonzero superdiagonal entry. -/
theorem jordanRunLength_succ (n : ℕ) (J : Fin n → Fin n → ℝ) (k : ℕ)
    (h : k + 1 < n) (hJ : J ⟨k, Nat.lt_of_succ_lt h⟩ ⟨k + 1, h⟩ ≠ 0) :
    jordanRunLength n J (k + 1) = jordanRunLength n J k + 1 := by
  simp only [jordanRunLength, dif_pos h, if_pos hJ]

/-- **Existence of the δ-scaling vector** (Higham, Accuracy and Stability of
    Numerical Algorithms, 2nd ed., §18.2, Theorem 18.1 proof, pp. 347–348):
    when every run of consecutive nonzero superdiagonal entries of `J` has
    length at most `t − 1` (max Jordan block size ≤ `t`, encoded via
    `jordanRunLength`), the vector `p_i = β^(run length at i)` satisfies
    `β^(t−1) ≤ p ≤ 1`, `p > 0`, and the run-step law `p_j = β·p_i` across
    nonzero superdiagonal entries.  Real-spectrum Jordan data;
    complex/defective-over-ℂ case not covered. -/
theorem exists_jordan_scaling_vector (n : ℕ) (J : Fin n → Fin n → ℝ)
    (t : ℕ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hrun : ∀ k, jordanRunLength n J k ≤ t - 1) :
    ∃ p : Fin n → ℝ,
      (∀ i, 0 < p i) ∧ (∀ i, β ^ (t - 1) ≤ p i) ∧ (∀ i, p i ≤ 1) ∧
      (∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → J i j ≠ 0 → p j = β * p i) := by
  refine ⟨fun i => β ^ jordanRunLength n J (i : ℕ), ?_, ?_, ?_, ?_⟩
  · intro i
    exact pow_pos hβ0 _
  · intro i
    exact pow_le_pow_of_le_one hβ0.le hβ1 (hrun (i : ℕ))
  · intro i
    exact pow_le_one₀ hβ0.le hβ1
  · intro i j hji hJ
    have hlt : (i : ℕ) + 1 < n := by
      have hjn := j.isLt
      omega
    have hieq : (⟨(i : ℕ), Nat.lt_of_succ_lt hlt⟩ : Fin n) = i :=
      Fin.eq_of_val_eq rfl
    have hjeq : (⟨(i : ℕ) + 1, hlt⟩ : Fin n) = j :=
      Fin.eq_of_val_eq hji.symm
    have hJ' : J ⟨(i : ℕ), Nat.lt_of_succ_lt hlt⟩ ⟨(i : ℕ) + 1, hlt⟩ ≠ 0 := by
      rw [hieq, hjeq]
      exact hJ
    show β ^ jordanRunLength n J ((j : ℕ)) = β * β ^ jordanRunLength n J ((i : ℕ))
    rw [hji, jordanRunLength_succ n J (i : ℕ) hlt hJ', pow_succ, mul_comm]

-- ============================================================
-- Theorem 18.1: discharged t ≥ 2 construction (real Jordan data)
-- ============================================================

/-- **Discharged `t ≥ 2` construction (real-spectrum Jordan case)** of
    Theorem 18.1 (Higham, Accuracy and Stability of Numerical Algorithms,
    2nd ed., §18.2, Theorem 18.1 proof, pp. 347–348).

    Given real Jordan-form-like data `X⁻¹AX = J` — `J` upper bidiagonal with
    `|J_{ii}| ≤ ρ < 1`, superdiagonal entries of modulus ≤ 1, all other
    entries zero — and a scaling vector `p` with `β^(t−1) ≤ p ≤ 1` obeying
    the run-step law `p_j = β·p_i` across nonzero superdiagonal entries
    (`β = (1−ρ)(t−1)/t`; built from a block-size bound by
    `exists_jordan_scaling_vector`), the similarity `S = X·D`, `D = diag(p)`,
    PROVES `similarity_absorbs`: whenever `4t·η·κ∞(X)·‖A‖∞ < (1−ρ)^t`,

      ‖S⁻¹(A+ΔA)S‖∞ ≤ ‖D⁻¹JD‖∞ + ‖D⁻¹‖‖X⁻¹‖‖ΔA‖‖X‖‖D‖
                    ≤ (ρ + β) + β^(1−t)·η·κ∞(X)·‖A‖∞ < 1

    for all `|ΔA| ≤ η|A|`, using `ρ + β = 1 − ε` and the `t^t ≤ 4t(t−1)^(t−1)`
    (i.e. `(1+1/m)^m < e < 4`) optimisation.  Honest scope: real-spectrum
    Jordan data only; the complex/defective-over-ℂ case is not covered. -/
def JordanFormSpec.ofRealJordan (n : ℕ) (hn : 0 < n)
    (A X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv)
    (hsim : matMul n X_inv (matMul n A X) = J)
    (hshape : ∀ i j : Fin n, (j : ℕ) ≠ (i : ℕ) → (j : ℕ) ≠ (i : ℕ) + 1 → J i j = 0)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hdiagbd : ∀ i, |J i i| ≤ ρ)
    (hsup : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → |J i j| ≤ 1)
    (t : ℕ) (ht2 : 2 ≤ t)
    (p : Fin n → ℝ)
    (hp0 : ∀ i, 0 < p i)
    (hp1 : ∀ i, jordanBeta ρ t ^ (t - 1) ≤ p i)
    (hp2 : ∀ i, p i ≤ 1)
    (hpstep : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → J i j ≠ 0 →
      p j = jordanBeta ρ t * p i) :
    JordanFormSpec n hn A X X_inv where
  inv_right := hXr
  spectral_radius := ρ
  hr_nonneg := hρ0
  hr_lt_one := hρ1
  max_block_size := t
  ht_pos := by omega
  similarity_absorbs := by
    intro η hη hcond
    have hβpos : 0 < jordanBeta ρ t := jordanBeta_pos ρ t hρ1 ht2
    have hβt : 0 < jordanBeta ρ t ^ (t - 1) := pow_pos hβpos _
    -- The perturbation budget K = η·κ∞(X)·‖A‖∞ and the scalar margin.
    set K := η * (infNorm X * infNorm X_inv) * infNorm A with hKdef
    have hK0 : 0 ≤ K := by
      rw [hKdef]
      exact mul_nonneg (mul_nonneg hη
        (mul_nonneg (infNorm_nonneg X) (infNorm_nonneg X_inv)))
        (infNorm_nonneg A)
    have hcond' : 4 * (t : ℝ) * K < (1 - ρ) ^ t := by
      have hre : 4 * (t : ℝ) * K
          = 4 * (t : ℝ) * η * (infNorm X * infNorm X_inv) * infNorm A := by
        rw [hKdef]; ring
      rw [hre]
      exact hcond
    have hKlt : K < (1 - ρ) / (t : ℝ) * jordanBeta ρ t ^ (t - 1) :=
      higham_scaling_margin t ht2 ρ K hρ1 hK0 hcond'
    -- The diagonal scaling D = diag(p) and its inverse.
    have hDr : IsRightInverse n (diagMatrix p) (diagMatrix fun a => (p a)⁻¹) :=
      diagMatrix_isRightInverse n p (fun a => (p a)⁻¹)
        (fun a => mul_inv_cancel₀ (hp0 a).ne')
    have hXX : matMul n X X_inv = idMatrix n := by
      ext a b; exact hXr a b
    have hDD : matMul n (diagMatrix p) (diagMatrix fun a => (p a)⁻¹)
        = idMatrix n := by
      ext a b; exact hDr a b
    -- S = X·D, S⁻¹ = D⁻¹·X⁻¹ is a right-inverse pair.
    have hSS : matMul n (matMul n X (diagMatrix p))
        (matMul n (diagMatrix fun a => (p a)⁻¹) X_inv) = idMatrix n := by
      rw [matMul_assoc n X (diagMatrix p)
            (matMul n (diagMatrix fun a => (p a)⁻¹) X_inv),
          ← matMul_assoc n (diagMatrix p) (diagMatrix fun a => (p a)⁻¹) X_inv,
          hDD, matMul_id_left, hXX]
    have hSr : IsRightInverse n (matMul n X (diagMatrix p))
        (matMul n (diagMatrix fun a => (p a)⁻¹) X_inv) := by
      intro a b
      exact congrFun (congrFun hSS a) b
    -- Norm bounds for D, D⁻¹ and the scaled Jordan part.
    have hDn : infNorm (diagMatrix p) ≤ 1 :=
      infNorm_diagMatrix_le p zero_le_one (fun a => by
        rw [abs_of_pos (hp0 a)]
        exact hp2 a)
    have hDin : infNorm (diagMatrix fun a => (p a)⁻¹)
        ≤ (jordanBeta ρ t ^ (t - 1))⁻¹ :=
      infNorm_diagMatrix_le _ (inv_nonneg.mpr hβt.le) (fun a => by
        show |(p a)⁻¹| ≤ (jordanBeta ρ t ^ (t - 1))⁻¹
        rw [abs_of_pos (inv_pos.mpr (hp0 a))]
        exact inv_anti₀ hβt (hp1 a))
    have hJconj : infNorm (matMul n (diagMatrix fun a => (p a)⁻¹)
          (matMul n J (diagMatrix p))) ≤ ρ + jordanBeta ρ t :=
      infNorm_jordan_conj_le n J p ρ (jordanBeta ρ t) hρ0 hβpos.le
        hshape hdiagbd hsup hp0 hpstep
    -- The Jordan part of the conjugated similarity.
    have hterm1 : matMul n (matMul n (diagMatrix fun a => (p a)⁻¹) X_inv)
          (matMul n A (matMul n X (diagMatrix p)))
        = matMul n (diagMatrix fun a => (p a)⁻¹) (matMul n J (diagMatrix p)) := by
      rw [matMul_assoc n (diagMatrix fun a => (p a)⁻¹) X_inv
            (matMul n A (matMul n X (diagMatrix p))),
          ← matMul_assoc n A X (diagMatrix p),
          ← matMul_assoc n X_inv (matMul n A X) (diagMatrix p),
          hsim]
    -- q = (ρ + β) + β^(1−t)·K, with 0 ≤ q < 1.
    have hq0 : 0 ≤ ρ + jordanBeta ρ t + (jordanBeta ρ t ^ (t - 1))⁻¹ * K := by
      have h1 : 0 ≤ (jordanBeta ρ t ^ (t - 1))⁻¹ * K :=
        mul_nonneg (inv_nonneg.mpr hβt.le) hK0
      linarith [hβpos.le]
    have hq1 : ρ + jordanBeta ρ t + (jordanBeta ρ t ^ (t - 1))⁻¹ * K < 1 := by
      have hsum1 : ρ + jordanBeta ρ t = 1 - (1 - ρ) / (t : ℝ) :=
        jordanBeta_add_eq ρ t ht2
      have hlt2 : (jordanBeta ρ t ^ (t - 1))⁻¹ * K
          < (jordanBeta ρ t ^ (t - 1))⁻¹ *
            ((1 - ρ) / (t : ℝ) * jordanBeta ρ t ^ (t - 1)) :=
        mul_lt_mul_of_pos_left hKlt (inv_pos.mpr hβt)
      have heq3 : (jordanBeta ρ t ^ (t - 1))⁻¹ *
            ((1 - ρ) / (t : ℝ) * jordanBeta ρ t ^ (t - 1))
          = (1 - ρ) / (t : ℝ) := by
        rw [mul_comm ((1 - ρ) / (t : ℝ)) (jordanBeta ρ t ^ (t - 1)),
          ← mul_assoc, inv_mul_cancel₀ hβt.ne', one_mul]
      rw [heq3] at hlt2
      rw [hsum1]
      linarith
    refine ⟨matMul n X (diagMatrix p),
      matMul n (diagMatrix fun a => (p a)⁻¹) X_inv,
      ρ + jordanBeta ρ t + (jordanBeta ρ t ^ (t - 1))⁻¹ * K,
      hSr, hq0, hq1, ?_⟩
    intro ΔA hΔ
    -- S⁻¹(A+ΔA)S = D⁻¹JD + S⁻¹·ΔA·S, entrywise.
    have hsplit : matMul n (matMul n (diagMatrix fun a => (p a)⁻¹) X_inv)
          (matMul n (fun i j => A i j + ΔA i j) (matMul n X (diagMatrix p)))
        = fun i j =>
            matMul n (diagMatrix fun a => (p a)⁻¹)
              (matMul n J (diagMatrix p)) i j +
            matMul n (matMul n (diagMatrix fun a => (p a)⁻¹) X_inv)
              (matMul n ΔA (matMul n X (diagMatrix p))) i j := by
      rw [matMul_add_left n A ΔA (matMul n X (diagMatrix p)),
          matMul_add_right n (matMul n (diagMatrix fun a => (p a)⁻¹) X_inv)
            (matMul n A (matMul n X (diagMatrix p)))
            (matMul n ΔA (matMul n X (diagMatrix p))),
          hterm1]
    rw [hsplit]
    -- ‖S⁻¹·ΔA·S‖∞ ≤ β^(1−t)·η·κ∞(X)·‖A‖∞ = β^(1−t)·K.
    have hΔn : infNorm ΔA ≤ η * infNorm A :=
      infNorm_le_mul_of_abs_le_mul_abs ΔA A hη hΔ
    have hXD : infNorm (matMul n X (diagMatrix p)) ≤ infNorm X := by
      calc infNorm (matMul n X (diagMatrix p))
          ≤ infNorm X * infNorm (diagMatrix p) := infNorm_matMul_le hn X _
        _ ≤ infNorm X * 1 := mul_le_mul_of_nonneg_left hDn (infNorm_nonneg X)
        _ = infNorm X := mul_one _
    have hDX : infNorm (matMul n (diagMatrix fun a => (p a)⁻¹) X_inv)
        ≤ (jordanBeta ρ t ^ (t - 1))⁻¹ * infNorm X_inv := by
      calc infNorm (matMul n (diagMatrix fun a => (p a)⁻¹) X_inv)
          ≤ infNorm (diagMatrix fun a => (p a)⁻¹) * infNorm X_inv :=
            infNorm_matMul_le hn _ X_inv
        _ ≤ (jordanBeta ρ t ^ (t - 1))⁻¹ * infNorm X_inv :=
            mul_le_mul_of_nonneg_right hDin (infNorm_nonneg X_inv)
    have hMid : infNorm (matMul n ΔA (matMul n X (diagMatrix p)))
        ≤ η * infNorm A * infNorm X := by
      calc infNorm (matMul n ΔA (matMul n X (diagMatrix p)))
          ≤ infNorm ΔA * infNorm (matMul n X (diagMatrix p)) :=
            infNorm_matMul_le hn ΔA _
        _ ≤ η * infNorm A * infNorm X :=
            mul_le_mul hΔn hXD (infNorm_nonneg _)
              (mul_nonneg hη (infNorm_nonneg A))
    have hE : infNorm (matMul n (matMul n (diagMatrix fun a => (p a)⁻¹) X_inv)
          (matMul n ΔA (matMul n X (diagMatrix p))))
        ≤ (jordanBeta ρ t ^ (t - 1))⁻¹ * K := by
      have h1 : infNorm (matMul n (matMul n (diagMatrix fun a => (p a)⁻¹) X_inv)
            (matMul n ΔA (matMul n X (diagMatrix p))))
          ≤ ((jordanBeta ρ t ^ (t - 1))⁻¹ * infNorm X_inv) *
            (η * infNorm A * infNorm X) := by
        calc infNorm (matMul n (matMul n (diagMatrix fun a => (p a)⁻¹) X_inv)
              (matMul n ΔA (matMul n X (diagMatrix p))))
            ≤ infNorm (matMul n (diagMatrix fun a => (p a)⁻¹) X_inv) *
              infNorm (matMul n ΔA (matMul n X (diagMatrix p))) :=
              infNorm_matMul_le hn _ _
          _ ≤ ((jordanBeta ρ t ^ (t - 1))⁻¹ * infNorm X_inv) *
              (η * infNorm A * infNorm X) :=
              mul_le_mul hDX hMid (infNorm_nonneg _)
                (mul_nonneg (inv_nonneg.mpr hβt.le) (infNorm_nonneg X_inv))
      have h2 : ((jordanBeta ρ t ^ (t - 1))⁻¹ * infNorm X_inv) *
            (η * infNorm A * infNorm X)
          = (jordanBeta ρ t ^ (t - 1))⁻¹ * K := by
        rw [hKdef]; ring
      rw [h2] at h1
      exact h1
    calc infNorm (fun i j =>
          matMul n (diagMatrix fun a => (p a)⁻¹)
            (matMul n J (diagMatrix p)) i j +
          matMul n (matMul n (diagMatrix fun a => (p a)⁻¹) X_inv)
            (matMul n ΔA (matMul n X (diagMatrix p))) i j)
        ≤ infNorm (matMul n (diagMatrix fun a => (p a)⁻¹)
            (matMul n J (diagMatrix p))) +
          infNorm (matMul n (matMul n (diagMatrix fun a => (p a)⁻¹) X_inv)
            (matMul n ΔA (matMul n X (diagMatrix p)))) :=
          infNorm_add_le _ _
      _ ≤ ρ + jordanBeta ρ t + (jordanBeta ρ t ^ (t - 1))⁻¹ * K :=
          add_le_add hJconj hE

-- ============================================================
-- Theorem 18.1: axiom-free end-to-end forms (real Jordan data)
-- ============================================================

/-- **Axiom-free real-spectrum Jordan case of Theorem 18.1** (limit form,
    abstract error model) — Higham, Accuracy and Stability of Numerical
    Algorithms, 2nd ed., §18.2, Theorem 18.1 (pp. 347–348).

    If `X⁻¹AX = J` is upper bidiagonal with `|J_{ii}| ≤ ρ < 1`, superdiagonal
    entries of modulus ≤ 1, every run of consecutive nonzero superdiagonal
    entries of length ≤ `t − 1` (max Jordan block size ≤ `t`, via
    `jordanRunLength`), and the Higham–Knight condition (18.13)
    `4t·c·κ∞(X)·‖A‖∞ < (1−ρ)^t` holds, then any computed-power sequence with
    per-step componentwise budget `c` satisfies `‖v_m‖∞ → 0`.

    No `similarity_absorbs` assumption: `t = 1` dispatches to the diagonal
    construction (`JordanFormSpec.ofRealDiagonal`) and `t ≥ 2` to the
    δ-scaling construction (`JordanFormSpec.ofRealJordan` with the scaling
    vector from `exists_jordan_scaling_vector`).  Honest scope: real-spectrum
    Jordan data; the complex/defective-over-ℂ case is not covered. -/
theorem higham_18_1_real_jordan_tendsto (n : ℕ) (hn : 0 < n)
    (A X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv)
    (hsim : matMul n X_inv (matMul n A X) = J)
    (hshape : ∀ i j : Fin n, (j : ℕ) ≠ (i : ℕ) → (j : ℕ) ≠ (i : ℕ) + 1 → J i j = 0)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hdiagbd : ∀ i, |J i i| ≤ ρ)
    (hsup : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → |J i j| ≤ 1)
    (t : ℕ) (ht1 : 1 ≤ t)
    (hrun : ∀ k, jordanRunLength n J k ≤ t - 1)
    (v : ℕ → (Fin n → ℝ)) (c : ℝ) (hc : 0 ≤ c)
    (hComp : ComputedMatPowVec n A v c)
    (hCond : 4 * (t : ℝ) * c * (infNorm X * infNorm X_inv) * infNorm A
      < (1 - ρ) ^ t) :
    Filter.Tendsto (fun m => infNormVec (v m)) Filter.atTop (nhds 0) := by
  rcases Nat.lt_or_ge t 2 with ht | ht2
  · -- t = 1: the run bound forces J diagonal; use the diagonal construction.
    have ht1' : t = 1 := by omega
    subst ht1'
    have hdiag : ∀ i j : Fin n, i ≠ j → J i j = 0 := by
      intro i j hij
      by_cases hj : (j : ℕ) = (i : ℕ) + 1
      · by_contra hJ
        have hlt : (i : ℕ) + 1 < n := by
          have hjn := j.isLt
          omega
        have hieq : (⟨(i : ℕ), Nat.lt_of_succ_lt hlt⟩ : Fin n) = i :=
          Fin.eq_of_val_eq rfl
        have hjeq : (⟨(i : ℕ) + 1, hlt⟩ : Fin n) = j :=
          Fin.eq_of_val_eq hj.symm
        have hJ' : J ⟨(i : ℕ), Nat.lt_of_succ_lt hlt⟩
            ⟨(i : ℕ) + 1, hlt⟩ ≠ 0 := by
          rw [hieq, hjeq]
          exact hJ
        have hstep := jordanRunLength_succ n J (i : ℕ) hlt hJ'
        have hbound := hrun ((i : ℕ) + 1)
        omega
      · apply hshape i j _ hj
        exact fun h => hij (Fin.eq_of_val_eq h.symm)
    have hCond' : 4 * c * (infNorm X * infNorm X_inv) * infNorm A < 1 - ρ := by
      have h := hCond
      rw [pow_one, Nat.cast_one] at h
      have hre : 4 * (1 : ℝ) * c * (infNorm X * infNorm X_inv) * infNorm A
          = 4 * c * (infNorm X * infNorm X_inv) * infNorm A := by ring
      rw [hre] at h
      exact h
    exact higham_18_1_real_diagonalizable_tendsto n hn A X X_inv J hXr hsim
      hdiag ρ hρ0 hρ1 hdiagbd v c hc hComp hCond'
  · -- t ≥ 2: build the scaling vector and the δ-scaled Jordan spec.
    have hβpos : 0 < jordanBeta ρ t := jordanBeta_pos ρ t hρ1 ht2
    have hβlt : jordanBeta ρ t < 1 := jordanBeta_lt_one ρ t hρ0 ht2
    obtain ⟨p, hp0, hp1, hp2, hpstep⟩ :=
      exists_jordan_scaling_vector n J t (jordanBeta ρ t) hβpos hβlt.le hrun
    obtain ⟨C, q, hC, hq0, hq1, hbound⟩ :=
      higham_knight_18_1 n hn A X X_inv
        (JordanFormSpec.ofRealJordan n hn A X X_inv J hXr hsim hshape
          ρ hρ0 hρ1 hdiagbd hsup t ht2 p hp0 hp1 hp2 hpstep)
        v c hc hComp hCond
    exact computedMatPow_tendsto_zero_of_geometric n v C q hq0 hq1 hbound

/-- **Axiom-free real-spectrum Jordan case of Theorem 18.1 for the actual
    floating-point iteration** — Higham, Accuracy and Stability of Numerical
    Algorithms, 2nd ed., §18.2, Theorem 18.1 (pp. 347–348).

    With `X⁻¹AX = J` upper bidiagonal (`|J_{ii}| ≤ ρ < 1`, superdiagonal
    of modulus ≤ 1, runs of nonzero superdiagonal entries ≤ `t − 1`) and the
    printed condition `4t·γ_{n+2}·κ∞(X)·‖A‖∞ < (1−ρ)^t`, the computed vectors
    `fl(Aᵐ v₀)` (repeated `fl_matVec`) satisfy `‖fl(Aᵐ v₀)‖∞ → 0`.
    Fully end-to-end: concrete algorithm, concrete rounding model, no assumed
    construction.  Honest scope: real-spectrum Jordan data;
    complex/defective-over-ℂ case not covered. -/
theorem higham_18_1_real_jordan_fl_tendsto (fp : FPModel) (n : ℕ) (hn : 0 < n)
    (A X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv)
    (hsim : matMul n X_inv (matMul n A X) = J)
    (hshape : ∀ i j : Fin n, (j : ℕ) ≠ (i : ℕ) → (j : ℕ) ≠ (i : ℕ) + 1 → J i j = 0)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hdiagbd : ∀ i, |J i i| ≤ ρ)
    (hsup : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → |J i j| ≤ 1)
    (t : ℕ) (ht1 : 1 ≤ t)
    (hrun : ∀ k, jordanRunLength n J k ≤ t - 1)
    (v0 : Fin n → ℝ) (hval : gammaValid fp (n + 2))
    (hCond : 4 * (t : ℝ) * gamma fp (n + 2) *
      (infNorm X * infNorm X_inv) * infNorm A < (1 - ρ) ^ t) :
    Filter.Tendsto
      (fun m => infNormVec (fl_matPowVecSeq fp n A v0 m))
      Filter.atTop (nhds 0) :=
  higham_18_1_real_jordan_tendsto n hn A X X_inv J hXr hsim hshape
    ρ hρ0 hρ1 hdiagbd hsup t ht1 hrun (fl_matPowVecSeq fp n A v0)
    (gamma fp (n + 2)) (gamma_nonneg fp hval)
    (computedMatPowVec_fl_matVec_gamma_add_two fp n A v0 hval) hCond

-- ============================================================
-- §18.1  Exact arithmetic: eq (18.5) alternative form, real Jordan case
-- ============================================================

/-- **Eq (18.5), alternative form (p. 344, unnumbered display), real-Jordan
    ∞-norm case** (Higham, Accuracy and Stability of Numerical Algorithms,
    2nd ed., §18.1): for real bidiagonal Jordan data `X⁻¹AX = J` with
    `|J_{ii}| ≤ ρ`, superdiagonal moduli ≤ 1, and a `β`-scaling vector `p`
    with `βˢ ≤ p ≤ 1` obeying the run-step law, the exact powers satisfy

      `‖Aᵏ‖∞ ≤ κ∞(X) · (βˢ)⁻¹ · (ρ + β)ᵏ`

    where `(βˢ)⁻¹` bounds `κ∞(D)` for `D = diag(p)` (in the Jordan
    application `s = t − 1` and `β` plays the role of the printed
    δ-margin, cf. `jordanBeta`).  Honest scope: the printed display covers
    all p-norms and complex data; this closes the `p = ∞`, real-spectrum
    form. -/
theorem higham_eq_18_5_alt_real_jordan (n : ℕ) (hn : 0 < n)
    (A X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n A X) = J)
    (hshape : ∀ i j : Fin n, (j : ℕ) ≠ (i : ℕ) → (j : ℕ) ≠ (i : ℕ) + 1 → J i j = 0)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hdiagbd : ∀ i, |J i i| ≤ ρ)
    (hsup : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → |J i j| ≤ 1)
    (β : ℝ) (hβ0 : 0 < β) (s : ℕ)
    (p : Fin n → ℝ)
    (hp1 : ∀ i, β ^ s ≤ p i) (hp2 : ∀ i, p i ≤ 1)
    (hpstep : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → J i j ≠ 0 → p j = β * p i)
    (k : ℕ) :
    infNorm (matPow n A k) ≤
      (infNorm X * infNorm X_inv) * (β ^ s)⁻¹ * (ρ + β) ^ k := by
  have hβs : (0:ℝ) < β ^ s := pow_pos hβ0 s
  have hp0 : ∀ i, 0 < p i := fun i => lt_of_lt_of_le hβs (hp1 i)
  set D := diagMatrix p with hD
  set Dinv := diagMatrix (fun a => (p a)⁻¹) with hDinv
  set S := matMul n X D with hS
  set Sinv := matMul n Dinv X_inv with hSinv
  have hDr : IsRightInverse n D Dinv :=
    diagMatrix_isRightInverse n p _ (fun a => mul_inv_cancel₀ (hp0 a).ne')
  have hDl : IsRightInverse n Dinv D :=
    diagMatrix_isRightInverse n _ p (fun a => inv_mul_cancel₀ (hp0 a).ne')
  have hXX : matMul n X X_inv = idMatrix n := by ext a b; exact hXr a b
  have hXX' : matMul n X_inv X = idMatrix n := by ext a b; exact hXl a b
  have hDD : matMul n D Dinv = idMatrix n := by ext a b; exact hDr a b
  have hDD' : matMul n Dinv D = idMatrix n := by ext a b; exact hDl a b
  have hSr : IsRightInverse n S Sinv := by
    intro a b
    have h : matMul n S Sinv = idMatrix n := by
      rw [hS, hSinv, matMul_assoc n X D (matMul n Dinv X_inv),
        ← matMul_assoc n D Dinv X_inv, hDD, matMul_id_left, hXX]
    exact congrFun (congrFun h a) b
  have hSl : IsRightInverse n Sinv S := by
    intro a b
    have h : matMul n Sinv S = idMatrix n := by
      rw [hSinv, hS, matMul_assoc n Dinv X_inv (matMul n X D),
        ← matMul_assoc n X_inv X D, hXX', matMul_id_left, hDD']
    exact congrFun (congrFun h a) b
  set J' := matMul n Dinv (matMul n J D) with hJ'
  have hsim' : matMul n Sinv (matMul n A S) = J' := by
    rw [hSinv, hS, hJ']
    have h1 : matMul n X_inv (matMul n A (matMul n X D))
        = matMul n (matMul n X_inv (matMul n A X)) D := by
      simp only [← matMul_assoc]
    rw [matMul_assoc n Dinv X_inv (matMul n A (matMul n X D)), h1, hsim]
  have htrans := matPow_similarity n A S Sinv J' hSr hSl hsim' k
  have hJ'norm : infNorm J' ≤ ρ + β := by
    rw [hJ', hDinv, hD]
    exact infNorm_jordan_conj_le n J p ρ β hρ0 hβ0.le hshape hdiagbd hsup
      hp0 hpstep
  have hJ'k : infNorm (matPow n J' k) ≤ (ρ + β) ^ k :=
    calc infNorm (matPow n J' k) ≤ infNorm J' ^ k := infNorm_matPow_le hn J' k
      _ ≤ (ρ + β) ^ k := pow_le_pow_left₀ (infNorm_nonneg J') hJ'norm k
  have hDnorm : infNorm D ≤ 1 := by
    rw [hD]
    exact infNorm_diagMatrix_le p zero_le_one
      (fun i => by rw [abs_of_pos (hp0 i)]; exact hp2 i)
  have hDinvnorm : infNorm Dinv ≤ (β ^ s)⁻¹ := by
    rw [hDinv]
    apply infNorm_diagMatrix_le _ (inv_nonneg.mpr hβs.le)
    intro i
    rw [abs_of_pos (inv_pos.mpr (hp0 i))]
    exact inv_anti₀ hβs (hp1 i)
  have hSnorm : infNorm S ≤ infNorm X := by
    calc infNorm S ≤ infNorm X * infNorm D := by
          rw [hS]; exact infNorm_matMul_le hn X D
      _ ≤ infNorm X * 1 := mul_le_mul_of_nonneg_left hDnorm (infNorm_nonneg X)
      _ = infNorm X := mul_one _
  have hSinvnorm : infNorm Sinv ≤ (β ^ s)⁻¹ * infNorm X_inv := by
    calc infNorm Sinv ≤ infNorm Dinv * infNorm X_inv := by
          rw [hSinv]; exact infNorm_matMul_le hn _ _
      _ ≤ (β ^ s)⁻¹ * infNorm X_inv :=
          mul_le_mul_of_nonneg_right hDinvnorm (infNorm_nonneg X_inv)
  rw [htrans]
  calc infNorm (matMul n S (matMul n (matPow n J' k) Sinv))
      ≤ infNorm S * infNorm (matMul n (matPow n J' k) Sinv) :=
        infNorm_matMul_le hn _ _
    _ ≤ infNorm S * (infNorm (matPow n J' k) * infNorm Sinv) :=
        mul_le_mul_of_nonneg_left (infNorm_matMul_le hn _ _)
          (infNorm_nonneg S)
    _ ≤ infNorm X * ((ρ + β) ^ k * ((β ^ s)⁻¹ * infNorm X_inv)) := by
        apply mul_le_mul hSnorm _
          (mul_nonneg (infNorm_nonneg _) (infNorm_nonneg _))
          (infNorm_nonneg X)
        exact mul_le_mul hJ'k hSinvnorm (infNorm_nonneg Sinv)
          (pow_nonneg (add_nonneg hρ0 hβ0.le) k)
    _ = (infNorm X * infNorm X_inv) * (β ^ s)⁻¹ * (ρ + β) ^ k := by ring

end NumStability
