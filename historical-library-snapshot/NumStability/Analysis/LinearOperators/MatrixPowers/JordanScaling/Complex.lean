import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Analysis.LinearOperators.MatrixPowers.ExactNormBounds.Complex
import NumStability.Analysis.LinearOperators.MatrixPowers.JordanScaling.RealJordan
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Basic
import NumStability.Analysis.VectorNorms.Basic

/-!
# Analysis.LinearOperators.MatrixPowers.JordanScaling.Complex

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

-- Algorithms/MatrixPowersComplex.lean
--
-- Higham Chapter 18: Error analysis of matrix powers — the GENERAL
-- (complex-spectrum, possibly defective) case of Theorem 18.1
-- (Higham–Knight) for a REAL input matrix `A` with COMPLEX Jordan-form
-- similarity data (Higham, Accuracy and Stability of Numerical Algorithms,
-- 2nd ed., §18.2, Theorem 18.1, pp. 347–348).
--
-- The computed iteration `v_{k+1} = fl(A v_k)` is real (a floating-point
-- object), matching the book's computational setting; the Jordan data
-- `X⁻¹ A X = J` lives over ℂ, which is the full generality of the printed
-- statement for real `A`.  The δ-scaling construction of the book's proof
-- is transported verbatim from the real-spectrum case
-- (`MatrixPowersJordan.lean`): the moduli arguments are identical because
-- `‖·‖` on ℂ is multiplicative and satisfies the triangle inequality.
--
-- Complex matrix infrastructure is REUSED from the canonical semantic API
-- (source traceability):
--   `CVec`                              — Analysis/VectorNorms/Basic.lean
--   `CMatrix`                           — Analysis/MatrixNorms/Basic.lean
--   `complexVecInfNorm` (+ nonneg / coord_le / le_of_coord_le)
--                                      — Analysis/VectorNorms/Basic.lean
--   `complexMatrixInfNorm` (+ nonneg / row_sum_le / le_of_row_sum_le)
--                                      — Analysis/MatrixNorms/Basic.lean («cInfNorm»:
--                                        max row sum of entry norms)
--   `complexMatrixMul`, `complexMatrixMul_assoc`
--                                      — Analysis/MatrixNorms/Basic.lean
--   `complexMatrixVecMul`, `complexMatrixVecMul_mul`
--                                      — Analysis/MatrixNorms/Basic.lean
--   `IsComplexMatrixRightInverse`      — Analysis/MatrixNorms/Basic.lean
-- Scalar margin lemmas are REUSED from `MatrixPowersJordan.lean`
-- (`jordanBeta`, `jordanBeta_pos`, `jordanBeta_lt_one`, `jordanBeta_add_eq`,
-- `higham_scaling_margin`) and the run-length machinery from the same file
-- (`jordanRunLength`, `exists_jordan_scaling_vector`) via a norm-matrix
-- wrapper.  Only what is missing over ℂ is defined here.












namespace NumStability

open scoped BigOperators

-- ============================================================
-- Missing pieces of the complex ∞-norm lemma suite
-- (complexMatrixInfNorm = the max-row-sum «cInfNorm»; the definition and
--  the nonneg / row_sum_le / le_of_row_sum_le lemmas are reused from
--  Analysis/MatrixNorms/Basic.lean)
-- ============================================================
























































































-- ============================================================
-- Real-cast bridges: embedding ℝ-vectors and ℝ-matrices into ℂ
-- preserves the ∞-norms (via ‖(x : ℂ)‖ = ‖x‖ = |x|)
-- ============================================================



















































-- ============================================================
-- Entrywise addition distributes over complexMatrixMul
-- ============================================================





















-- ============================================================
-- §18.2  Complex similarity-based convergence engine (eq 18.14)
-- for a REAL computed-power sequence, embedded into ℂ
-- ============================================================





































































































































-- ============================================================
-- Complex diagonal scaling matrices
-- ============================================================

/-- Diagonal complex matrix with prescribed diagonal `d`. -/
noncomputable def cDiagMatrix {n : ℕ} (d : Fin n → ℂ) : CMatrix n n :=
  fun i j => if i = j then d i else 0

/-- Action of a complex diagonal matrix on a vector. -/
theorem cDiagMatrix_vecMul {n : ℕ} (d : Fin n → ℂ) (x : CVec n) :
    complexMatrixVecMul (cDiagMatrix d) x = fun i => d i * x i := by
  funext i
  unfold complexMatrixVecMul cDiagMatrix
  simp [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ]

/-- Entrywise formula for the two-sided diagonal conjugation over ℂ:
    `(diag(q) · J · diag(p))_{ij} = q_i · J_{ij} · p_j`. -/
theorem cDiagMatrix_conj_entry {n : ℕ} (J : CMatrix n n)
    (p q : Fin n → ℂ) (i j : Fin n) :
    complexMatrixMul (cDiagMatrix q) (complexMatrixMul J (cDiagMatrix p)) i j
      = q i * J i j * p j := by
  have hleft : ∀ (M : CMatrix n n) (a : Fin n) (b : Fin n),
      complexMatrixMul (cDiagMatrix q) M a b = q a * M a b := by
    intro M a b
    unfold complexMatrixMul cDiagMatrix
    simp [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ]
  have hright : ∀ (a : Fin n) (b : Fin n),
      complexMatrixMul J (cDiagMatrix p) a b = J a b * p b := by
    intro a b
    unfold complexMatrixMul cDiagMatrix
    simp [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ]
  rw [hleft, hright]
  ring

/-- ∞-norm bound for a complex diagonal matrix from an entrywise bound. -/
theorem complexMatrixInfNorm_cDiagMatrix_le {n : ℕ} (d : Fin n → ℂ) {c : ℝ}
    (hc : 0 ≤ c) (hd : ∀ i, ‖d i‖ ≤ c) :
    complexMatrixInfNorm (cDiagMatrix d) ≤ c := by
  apply complexMatrixInfNorm_diagonal_le _ hc
  · intro i j hij
    show (if i = j then d i else 0) = 0
    rw [if_neg hij]
  · intro i
    show ‖if i = i then d i else 0‖ ≤ c
    rw [if_pos rfl]
    exact hd i

-- ============================================================
-- The scaled bidiagonal row-sum bound ‖D⁻¹ J D‖∞ ≤ ρ + β over ℂ
-- ============================================================

/-- **Row sums of the scaled complex Jordan matrix** (Higham, 2nd ed., §18.2,
    Theorem 18.1 proof, pp. 347–348, moduli argument over ℂ): with `p` a real
    positive scaling vector satisfying the run-step law `p_j = β·p_i` across
    nonzero superdiagonal entries, each row sum of `|D⁻¹ J D|` (entries
    `(p_i)⁻¹ J_{ij} p_j`) is at most `ρ + β`.  Identical to the real proof
    with `|·|` replaced by `‖·‖` on ℂ. -/
theorem cJordan_conj_row_sum_le (n : ℕ) (J : CMatrix n n)
    (p : Fin n → ℝ) (ρ β : ℝ) (hβ0 : 0 ≤ β)
    (hshape : ∀ i j : Fin n, (j : ℕ) ≠ (i : ℕ) → (j : ℕ) ≠ (i : ℕ) + 1 →
      J i j = 0)
    (hdiagbd : ∀ i, ‖J i i‖ ≤ ρ)
    (hsup : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → ‖J i j‖ ≤ 1)
    (hp0 : ∀ i, 0 < p i)
    (hpstep : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → J i j ≠ 0 →
      p j = β * p i)
    (i : Fin n) :
    ∑ j : Fin n, ‖(((p i)⁻¹ : ℝ) : ℂ) * J i j * ((p j : ℝ) : ℂ)‖ ≤ ρ + β := by
  have hpne : p i ≠ 0 := (hp0 i).ne'
  have hpc : (((p i)⁻¹ : ℝ) : ℂ) * ((p i : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ hpne, Complex.ofReal_one]
  have hdiagentry : (((p i)⁻¹ : ℝ) : ℂ) * J i i * ((p i : ℝ) : ℂ) = J i i := by
    calc (((p i)⁻¹ : ℝ) : ℂ) * J i i * ((p i : ℝ) : ℂ)
        = J i i * ((((p i)⁻¹ : ℝ) : ℂ) * ((p i : ℝ) : ℂ)) := by ring
      _ = J i i := by rw [hpc, mul_one]
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
          ‖(((p i)⁻¹ : ℝ) : ℂ) * J i j * ((p j : ℝ) : ℂ)‖
        = ∑ j : Fin n, ‖(((p i)⁻¹ : ℝ) : ℂ) * J i j * ((p j : ℝ) : ℂ)‖ := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
      rw [hzero j hj.1 hj.2, mul_zero, zero_mul, norm_zero]
    rw [← hsub, Finset.sum_pair hii']
    have hd : ‖(((p i)⁻¹ : ℝ) : ℂ) * J i i * ((p i : ℝ) : ℂ)‖ ≤ ρ := by
      rw [hdiagentry]
      exact hdiagbd i
    have hs : ‖(((p i)⁻¹ : ℝ) : ℂ) * J i (⟨(i : ℕ) + 1, hi⟩ : Fin n) *
        ((p (⟨(i : ℕ) + 1, hi⟩ : Fin n) : ℝ) : ℂ)‖ ≤ β := by
      by_cases hJ : J i (⟨(i : ℕ) + 1, hi⟩ : Fin n) = 0
      · rw [hJ, mul_zero, zero_mul, norm_zero]
        exact hβ0
      · have hstep := hpstep i (⟨(i : ℕ) + 1, hi⟩ : Fin n) rfl hJ
        have hentry : (((p i)⁻¹ : ℝ) : ℂ) *
            J i (⟨(i : ℕ) + 1, hi⟩ : Fin n) *
            ((p (⟨(i : ℕ) + 1, hi⟩ : Fin n) : ℝ) : ℂ)
            = ((β : ℝ) : ℂ) * J i (⟨(i : ℕ) + 1, hi⟩ : Fin n) := by
          rw [hstep, Complex.ofReal_mul]
          calc (((p i)⁻¹ : ℝ) : ℂ) * J i (⟨(i : ℕ) + 1, hi⟩ : Fin n) *
                (((β : ℝ) : ℂ) * ((p i : ℝ) : ℂ))
              = ((β : ℝ) : ℂ) * J i (⟨(i : ℕ) + 1, hi⟩ : Fin n) *
                ((((p i)⁻¹ : ℝ) : ℂ) * ((p i : ℝ) : ℂ)) := by ring
            _ = ((β : ℝ) : ℂ) * J i (⟨(i : ℕ) + 1, hi⟩ : Fin n) := by
                rw [hpc, mul_one]
        rw [hentry, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hβ0]
        have hJb := hsup i (⟨(i : ℕ) + 1, hi⟩ : Fin n) rfl
        calc β * ‖J i (⟨(i : ℕ) + 1, hi⟩ : Fin n)‖
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
    have hsingle : ∑ j : Fin n, ‖(((p i)⁻¹ : ℝ) : ℂ) * J i j * ((p j : ℝ) : ℂ)‖
        = ‖(((p i)⁻¹ : ℝ) : ℂ) * J i i * ((p i : ℝ) : ℂ)‖ := by
      apply Finset.sum_eq_single i
      · intro j _ hj
        rw [hzero j hj, mul_zero, zero_mul, norm_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [hsingle, hdiagentry]
    have h1 := hdiagbd i
    linarith

/-- **The contraction bound ‖D⁻¹ J D‖∞ ≤ ρ + β** for the δ-scaled complex
    Jordan matrix (Higham, 2nd ed., §18.2, Theorem 18.1 proof,
    pp. 347–348). -/
theorem complexMatrixInfNorm_cJordan_conj_le (n : ℕ) (J : CMatrix n n)
    (p : Fin n → ℝ) (ρ β : ℝ) (hρ0 : 0 ≤ ρ) (hβ0 : 0 ≤ β)
    (hshape : ∀ i j : Fin n, (j : ℕ) ≠ (i : ℕ) → (j : ℕ) ≠ (i : ℕ) + 1 →
      J i j = 0)
    (hdiagbd : ∀ i, ‖J i i‖ ≤ ρ)
    (hsup : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → ‖J i j‖ ≤ 1)
    (hp0 : ∀ i, 0 < p i)
    (hpstep : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → J i j ≠ 0 →
      p j = β * p i) :
    complexMatrixInfNorm (complexMatrixMul
        (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ))
        (complexMatrixMul J (cDiagMatrix fun a => ((p a : ℝ) : ℂ))))
      ≤ ρ + β := by
  apply complexMatrixInfNorm_le_of_row_sum_le (add_nonneg hρ0 hβ0)
  intro i
  calc ∑ j : Fin n, ‖complexMatrixMul
        (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ))
        (complexMatrixMul J (cDiagMatrix fun a => ((p a : ℝ) : ℂ))) i j‖
      = ∑ j : Fin n, ‖(((p i)⁻¹ : ℝ) : ℂ) * J i j * ((p j : ℝ) : ℂ)‖ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [cDiagMatrix_conj_entry]
    _ ≤ ρ + β := cJordan_conj_row_sum_le n J p ρ β hβ0 hshape hdiagbd hsup
        hp0 hpstep i

-- ============================================================
-- Run lengths of superdiagonal chains for a ℂ-entry Jordan matrix
-- ============================================================

/-- Length of the run of consecutive nonzero superdiagonal entries of the
    complex matrix `J` ending at position `k`, encoded by reusing the real
    run-length function on the entry-norm matrix (`J i j ≠ 0 ↔ ‖J i j‖ ≠ 0`).
    A maximal Jordan block size of `t` corresponds to
    `cJordanRunLength n J k ≤ t − 1` for all `k`. -/
noncomputable def cJordanRunLength (n : ℕ) (J : CMatrix n n) : ℕ → ℕ :=
  jordanRunLength n (fun i j => ‖J i j‖)

/-- Step law of the complex run length across a nonzero superdiagonal
    entry. -/
theorem cJordanRunLength_succ (n : ℕ) (J : CMatrix n n) (k : ℕ)
    (h : k + 1 < n) (hJ : J ⟨k, Nat.lt_of_succ_lt h⟩ ⟨k + 1, h⟩ ≠ 0) :
    cJordanRunLength n J (k + 1) = cJordanRunLength n J k + 1 := by
  unfold cJordanRunLength
  exact jordanRunLength_succ n (fun i j => ‖J i j‖) k h
    (norm_ne_zero_iff.mpr hJ)

/-- **Existence of the δ-scaling vector for complex Jordan data** (Higham,
    Accuracy and Stability of Numerical Algorithms, 2nd ed., §18.2,
    Theorem 18.1 proof, pp. 347–348): when every run of consecutive nonzero
    superdiagonal entries of the complex `J` has length at most `t − 1`
    (max Jordan block size ≤ `t`, via `cJordanRunLength`), the REAL positive
    vector `p_i = β^(run length at i)` satisfies `β^(t−1) ≤ p ≤ 1` and the
    run-step law `p_j = β·p_i` across nonzero superdiagonal entries.
    Obtained from the real-spectrum `exists_jordan_scaling_vector` applied
    to the entry-norm matrix. -/
theorem exists_cJordan_scaling_vector (n : ℕ) (J : CMatrix n n)
    (t : ℕ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hrun : ∀ k, cJordanRunLength n J k ≤ t - 1) :
    ∃ p : Fin n → ℝ,
      (∀ i, 0 < p i) ∧ (∀ i, β ^ (t - 1) ≤ p i) ∧ (∀ i, p i ≤ 1) ∧
      (∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → J i j ≠ 0 → p j = β * p i) := by
  obtain ⟨p, hp0, hp1, hp2, hpstep⟩ :=
    exists_jordan_scaling_vector n (fun i j => ‖J i j‖) t β hβ0 hβ1 hrun
  exact ⟨p, hp0, hp1, hp2, fun i j hji hJ =>
    hpstep i j hji (norm_ne_zero_iff.mpr hJ)⟩

-- ============================================================
-- Theorem 18.1: the absorbing similarity over ℂ (all t ≥ 1)
-- ============================================================

/-- **The perturbation-absorbing complex similarity of Theorem 18.1's proof**
    (Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §18.2,
    Theorem 18.1, pp. 347–348), complex Jordan data, all `1 ≤ t`.

    Given complex Jordan-form-like data for the real matrix `A` —
    `X·X⁻¹ = I` over ℂ, `X⁻¹ Â X = J` with `Â i j = ((A i j : ℝ) : ℂ)`,
    `J` upper bidiagonal with `‖J_{ii}‖ ≤ ρ < 1`, superdiagonal moduli ≤ 1,
    all other entries zero, and every run of consecutive nonzero
    superdiagonal entries of length ≤ `t − 1` — and the Higham–Knight
    condition (18.13)

      `4t·η·κ∞(X)·‖A‖∞ < (1−ρ)^t`,  `κ∞(X) = ‖X‖∞·‖X⁻¹‖∞` over ℂ,

    there exists a complex similarity `S` (namely `S = X·D` with
    `D = diag(p)`, `p` the real δ-scaling vector; `S = X` when `t = 1`)
    and `q < 1` absorbing every admissible real perturbation:
    `‖S⁻¹(Â+ΔÂ)S‖∞ ≤ q` whenever `|ΔA| ≤ η|A|` componentwise.

    PROVED from the Jordan data (no assumed contraction/absorption
    hypothesis): `t = 1` dispatches to the diagonal argument, `t ≥ 2` to the
    δ-scaling construction with the `t^t ≤ 4t(t−1)^(t−1)` (i.e.
    `(1+1/m)^m < e < 4`) optimisation, reusing `higham_scaling_margin`. -/
theorem complex_jordan_similarity_absorbs (n : ℕ)
    (A : Fin n → Fin n → ℝ) (X X_inv J : CMatrix n n)
    (hXr : IsComplexMatrixRightInverse X X_inv)
    (hsim : complexMatrixMul X_inv (complexMatrixMul
      (fun i j => ((A i j : ℝ) : ℂ)) X) = J)
    (hshape : ∀ i j : Fin n, (j : ℕ) ≠ (i : ℕ) → (j : ℕ) ≠ (i : ℕ) + 1 →
      J i j = 0)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hdiagbd : ∀ i, ‖J i i‖ ≤ ρ)
    (hsup : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → ‖J i j‖ ≤ 1)
    (t : ℕ) (ht1 : 1 ≤ t)
    (hrun : ∀ k, cJordanRunLength n J k ≤ t - 1)
    (η : ℝ) (hη : 0 ≤ η)
    (hcond : 4 * (t : ℝ) * η *
      (complexMatrixInfNorm X * complexMatrixInfNorm X_inv) * infNorm A
      < (1 - ρ) ^ t) :
    ∃ S S_inv : CMatrix n n, ∃ q : ℝ,
      IsComplexMatrixRightInverse S S_inv ∧ 0 ≤ q ∧ q < 1 ∧
      (∀ ΔA : Fin n → Fin n → ℝ,
        (∀ i j, |ΔA i j| ≤ η * |A i j|) →
        complexMatrixInfNorm (complexMatrixMul S_inv (complexMatrixMul
          (fun i j => ((A i j + ΔA i j : ℝ) : ℂ)) S)) ≤ q) := by
  rcases Nat.lt_or_ge t 2 with ht | ht2
  · -- t = 1: the run bound forces J diagonal; S = X directly.
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
        have hstep := cJordanRunLength_succ n J (i : ℕ) hlt hJ'
        have hbound := hrun ((i : ℕ) + 1)
        omega
      · apply hshape i j _ hj
        exact fun h => hij (Fin.eq_of_val_eq h.symm)
    set K : ℝ := η * (complexMatrixInfNorm X * complexMatrixInfNorm X_inv) *
      infNorm A with hK
    have hK0 : 0 ≤ K := by
      rw [hK]
      exact mul_nonneg (mul_nonneg hη
        (mul_nonneg (complexMatrixInfNorm_nonneg X)
          (complexMatrixInfNorm_nonneg X_inv)))
        (infNorm_nonneg A)
    have hcond' : 4 * K < 1 - ρ := by
      have h := hcond
      rw [pow_one, Nat.cast_one] at h
      have hre : 4 * (1 : ℝ) * η *
          (complexMatrixInfNorm X * complexMatrixInfNorm X_inv) * infNorm A
          = 4 * K := by
        rw [hK]; ring
      rw [hre] at h
      exact h
    have hKlt : K < 1 - ρ := by linarith
    refine ⟨X, X_inv, ρ + K, hXr, by linarith, by linarith, ?_⟩
    intro ΔA hΔ
    -- X⁻¹(Â+ΔÂ)X = J + X⁻¹ΔÂX, entrywise.
    have hofReal : (fun i j => ((A i j + ΔA i j : ℝ) : ℂ))
        = (fun i j => ((A i j : ℝ) : ℂ) + ((ΔA i j : ℝ) : ℂ)) := by
      funext i j
      exact Complex.ofReal_add _ _
    have hsplit : complexMatrixMul X_inv (complexMatrixMul
          (fun i j => ((A i j + ΔA i j : ℝ) : ℂ)) X)
        = fun i j => J i j + complexMatrixMul X_inv (complexMatrixMul
            (fun i j => ((ΔA i j : ℝ) : ℂ)) X) i j := by
      rw [hofReal, complexMatrixMul_add_left, complexMatrixMul_add_right,
        hsim]
    rw [hsplit]
    have hΔn : complexMatrixInfNorm (fun i j => ((ΔA i j : ℝ) : ℂ)) ≤
        η * infNorm A :=
      complexMatrixInfNorm_ofReal_le_mul ΔA A hη hΔ
    have hE : complexMatrixInfNorm (complexMatrixMul X_inv (complexMatrixMul
          (fun i j => ((ΔA i j : ℝ) : ℂ)) X)) ≤ K := by
      calc complexMatrixInfNorm (complexMatrixMul X_inv (complexMatrixMul
            (fun i j => ((ΔA i j : ℝ) : ℂ)) X))
          ≤ complexMatrixInfNorm X_inv * complexMatrixInfNorm
              (complexMatrixMul (fun i j => ((ΔA i j : ℝ) : ℂ)) X) :=
            complexMatrixInfNorm_mul_le _ _
        _ ≤ complexMatrixInfNorm X_inv *
              (complexMatrixInfNorm (fun i j => ((ΔA i j : ℝ) : ℂ)) *
                complexMatrixInfNorm X) :=
            mul_le_mul_of_nonneg_left (complexMatrixInfNorm_mul_le _ _)
              (complexMatrixInfNorm_nonneg X_inv)
        _ ≤ complexMatrixInfNorm X_inv *
              ((η * infNorm A) * complexMatrixInfNorm X) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hΔn (complexMatrixInfNorm_nonneg X))
              (complexMatrixInfNorm_nonneg X_inv)
        _ = K := by rw [hK]; ring
    calc complexMatrixInfNorm (fun i j => J i j +
          complexMatrixMul X_inv (complexMatrixMul
            (fun i j => ((ΔA i j : ℝ) : ℂ)) X) i j)
        ≤ complexMatrixInfNorm J + complexMatrixInfNorm
            (complexMatrixMul X_inv (complexMatrixMul
              (fun i j => ((ΔA i j : ℝ) : ℂ)) X)) :=
          complexMatrixInfNorm_add_le _ _
      _ ≤ ρ + K := add_le_add
          (complexMatrixInfNorm_diagonal_le J hρ0 hdiag hdiagbd) hE
  · -- t ≥ 2: δ-scaling construction S = X·D, D = diag(p).
    have hβpos : 0 < jordanBeta ρ t := jordanBeta_pos ρ t hρ1 ht2
    have hβlt : jordanBeta ρ t < 1 := jordanBeta_lt_one ρ t hρ0 ht2
    obtain ⟨p, hp0, hp1, hp2, hpstep⟩ :=
      exists_cJordan_scaling_vector n J t (jordanBeta ρ t) hβpos hβlt.le hrun
    have hβt : 0 < jordanBeta ρ t ^ (t - 1) := pow_pos hβpos _
    set K : ℝ := η * (complexMatrixInfNorm X * complexMatrixInfNorm X_inv) *
      infNorm A with hKdef
    have hK0 : 0 ≤ K := by
      rw [hKdef]
      exact mul_nonneg (mul_nonneg hη
        (mul_nonneg (complexMatrixInfNorm_nonneg X)
          (complexMatrixInfNorm_nonneg X_inv)))
        (infNorm_nonneg A)
    have hcond' : 4 * (t : ℝ) * K < (1 - ρ) ^ t := by
      have hre : 4 * (t : ℝ) * K
          = 4 * (t : ℝ) * η *
            (complexMatrixInfNorm X * complexMatrixInfNorm X_inv) *
            infNorm A := by
        rw [hKdef]; ring
      rw [hre]
      exact hcond
    have hKlt : K < (1 - ρ) / (t : ℝ) * jordanBeta ρ t ^ (t - 1) :=
      higham_scaling_margin t ht2 ρ K hρ1 hK0 hcond'
    -- The right-inverse pair S = X·D, S⁻¹ = D⁻¹·X⁻¹ (vector action).
    have hSr : IsComplexMatrixRightInverse
        (complexMatrixMul X (cDiagMatrix fun a => ((p a : ℝ) : ℂ)))
        (complexMatrixMul (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ))
          X_inv) := by
      intro x
      rw [complexMatrixVecMul_mul, complexMatrixVecMul_mul]
      have hDD : complexMatrixVecMul (cDiagMatrix fun a => ((p a : ℝ) : ℂ))
          (complexMatrixVecMul (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ))
            (complexMatrixVecMul X_inv x)) = complexMatrixVecMul X_inv x := by
        rw [cDiagMatrix_vecMul, cDiagMatrix_vecMul]
        funext i
        show ((p i : ℝ) : ℂ) * ((((p i)⁻¹ : ℝ) : ℂ) *
          complexMatrixVecMul X_inv x i) = complexMatrixVecMul X_inv x i
        rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (hp0 i).ne',
          Complex.ofReal_one, one_mul]
      rw [hDD]
      exact hXr x
    -- Norm bounds for D and D⁻¹.
    have hDn : complexMatrixInfNorm
        (cDiagMatrix fun a => ((p a : ℝ) : ℂ)) ≤ 1 :=
      complexMatrixInfNorm_cDiagMatrix_le _ zero_le_one (fun a => by
        show ‖((p a : ℝ) : ℂ)‖ ≤ 1
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hp0 a)]
        exact hp2 a)
    have hDin : complexMatrixInfNorm
        (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ))
        ≤ (jordanBeta ρ t ^ (t - 1))⁻¹ :=
      complexMatrixInfNorm_cDiagMatrix_le _ (inv_nonneg.mpr hβt.le)
        (fun a => by
          show ‖(((p a)⁻¹ : ℝ) : ℂ)‖ ≤ (jordanBeta ρ t ^ (t - 1))⁻¹
          rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr (hp0 a))]
          exact inv_anti₀ hβt (hp1 a))
    -- The scaled Jordan contraction.
    have hJconj : complexMatrixInfNorm (complexMatrixMul
          (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ))
          (complexMatrixMul J (cDiagMatrix fun a => ((p a : ℝ) : ℂ))))
        ≤ ρ + jordanBeta ρ t :=
      complexMatrixInfNorm_cJordan_conj_le n J p ρ (jordanBeta ρ t) hρ0
        hβpos.le hshape hdiagbd hsup hp0 hpstep
    -- The Jordan part of the conjugated similarity: S⁻¹ Â S = D⁻¹ J D.
    have hterm1 : complexMatrixMul
          (complexMatrixMul (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ)) X_inv)
          (complexMatrixMul (fun i j => ((A i j : ℝ) : ℂ))
            (complexMatrixMul X (cDiagMatrix fun a => ((p a : ℝ) : ℂ))))
        = complexMatrixMul (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ))
            (complexMatrixMul J (cDiagMatrix fun a => ((p a : ℝ) : ℂ))) := by
      rw [complexMatrixMul_assoc
            (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ)) X_inv
            (complexMatrixMul (fun i j => ((A i j : ℝ) : ℂ))
              (complexMatrixMul X (cDiagMatrix fun a => ((p a : ℝ) : ℂ)))),
          ← complexMatrixMul_assoc (fun i j => ((A i j : ℝ) : ℂ)) X
            (cDiagMatrix fun a => ((p a : ℝ) : ℂ)),
          ← complexMatrixMul_assoc X_inv
            (complexMatrixMul (fun i j => ((A i j : ℝ) : ℂ)) X)
            (cDiagMatrix fun a => ((p a : ℝ) : ℂ)),
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
    refine ⟨complexMatrixMul X (cDiagMatrix fun a => ((p a : ℝ) : ℂ)),
      complexMatrixMul (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ)) X_inv,
      ρ + jordanBeta ρ t + (jordanBeta ρ t ^ (t - 1))⁻¹ * K,
      hSr, hq0, hq1, ?_⟩
    intro ΔA hΔ
    -- S⁻¹(Â+ΔÂ)S = D⁻¹JD + S⁻¹·ΔÂ·S, entrywise.
    have hofReal : (fun i j => ((A i j + ΔA i j : ℝ) : ℂ))
        = (fun i j => ((A i j : ℝ) : ℂ) + ((ΔA i j : ℝ) : ℂ)) := by
      funext i j
      exact Complex.ofReal_add _ _
    have hsplit : complexMatrixMul
          (complexMatrixMul (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ)) X_inv)
          (complexMatrixMul (fun i j => ((A i j + ΔA i j : ℝ) : ℂ))
            (complexMatrixMul X (cDiagMatrix fun a => ((p a : ℝ) : ℂ))))
        = fun i j =>
            complexMatrixMul (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ))
              (complexMatrixMul J
                (cDiagMatrix fun a => ((p a : ℝ) : ℂ))) i j +
            complexMatrixMul
              (complexMatrixMul (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ))
                X_inv)
              (complexMatrixMul (fun i j => ((ΔA i j : ℝ) : ℂ))
                (complexMatrixMul X
                  (cDiagMatrix fun a => ((p a : ℝ) : ℂ)))) i j := by
      rw [hofReal, complexMatrixMul_add_left, complexMatrixMul_add_right,
        hterm1]
    rw [hsplit]
    -- ‖S⁻¹·ΔÂ·S‖∞ ≤ β^(1−t)·η·κ∞(X)·‖A‖∞ = β^(1−t)·K.
    have hΔn : complexMatrixInfNorm (fun i j => ((ΔA i j : ℝ) : ℂ)) ≤
        η * infNorm A :=
      complexMatrixInfNorm_ofReal_le_mul ΔA A hη hΔ
    have hXD : complexMatrixInfNorm (complexMatrixMul X
          (cDiagMatrix fun a => ((p a : ℝ) : ℂ)))
        ≤ complexMatrixInfNorm X := by
      calc complexMatrixInfNorm (complexMatrixMul X
            (cDiagMatrix fun a => ((p a : ℝ) : ℂ)))
          ≤ complexMatrixInfNorm X * complexMatrixInfNorm
              (cDiagMatrix fun a => ((p a : ℝ) : ℂ)) :=
            complexMatrixInfNorm_mul_le _ _
        _ ≤ complexMatrixInfNorm X * 1 :=
            mul_le_mul_of_nonneg_left hDn (complexMatrixInfNorm_nonneg X)
        _ = complexMatrixInfNorm X := mul_one _
    have hDX : complexMatrixInfNorm (complexMatrixMul
          (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ)) X_inv)
        ≤ (jordanBeta ρ t ^ (t - 1))⁻¹ * complexMatrixInfNorm X_inv := by
      calc complexMatrixInfNorm (complexMatrixMul
            (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ)) X_inv)
          ≤ complexMatrixInfNorm
              (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ)) *
            complexMatrixInfNorm X_inv :=
            complexMatrixInfNorm_mul_le _ _
        _ ≤ (jordanBeta ρ t ^ (t - 1))⁻¹ * complexMatrixInfNorm X_inv :=
            mul_le_mul_of_nonneg_right hDin
              (complexMatrixInfNorm_nonneg X_inv)
    have hMid : complexMatrixInfNorm (complexMatrixMul
          (fun i j => ((ΔA i j : ℝ) : ℂ))
          (complexMatrixMul X (cDiagMatrix fun a => ((p a : ℝ) : ℂ))))
        ≤ η * infNorm A * complexMatrixInfNorm X := by
      calc complexMatrixInfNorm (complexMatrixMul
            (fun i j => ((ΔA i j : ℝ) : ℂ))
            (complexMatrixMul X (cDiagMatrix fun a => ((p a : ℝ) : ℂ))))
          ≤ complexMatrixInfNorm (fun i j => ((ΔA i j : ℝ) : ℂ)) *
            complexMatrixInfNorm (complexMatrixMul X
              (cDiagMatrix fun a => ((p a : ℝ) : ℂ))) :=
            complexMatrixInfNorm_mul_le _ _
        _ ≤ η * infNorm A * complexMatrixInfNorm X :=
            mul_le_mul hΔn hXD (complexMatrixInfNorm_nonneg _)
              (mul_nonneg hη (infNorm_nonneg A))
    have hE : complexMatrixInfNorm (complexMatrixMul
          (complexMatrixMul (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ)) X_inv)
          (complexMatrixMul (fun i j => ((ΔA i j : ℝ) : ℂ))
            (complexMatrixMul X (cDiagMatrix fun a => ((p a : ℝ) : ℂ)))))
        ≤ (jordanBeta ρ t ^ (t - 1))⁻¹ * K := by
      have h1 : complexMatrixInfNorm (complexMatrixMul
            (complexMatrixMul (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ))
              X_inv)
            (complexMatrixMul (fun i j => ((ΔA i j : ℝ) : ℂ))
              (complexMatrixMul X (cDiagMatrix fun a => ((p a : ℝ) : ℂ)))))
          ≤ ((jordanBeta ρ t ^ (t - 1))⁻¹ * complexMatrixInfNorm X_inv) *
            (η * infNorm A * complexMatrixInfNorm X) := by
        calc complexMatrixInfNorm (complexMatrixMul
              (complexMatrixMul (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ))
                X_inv)
              (complexMatrixMul (fun i j => ((ΔA i j : ℝ) : ℂ))
                (complexMatrixMul X
                  (cDiagMatrix fun a => ((p a : ℝ) : ℂ)))))
            ≤ complexMatrixInfNorm (complexMatrixMul
                (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ)) X_inv) *
              complexMatrixInfNorm (complexMatrixMul
                (fun i j => ((ΔA i j : ℝ) : ℂ))
                (complexMatrixMul X
                  (cDiagMatrix fun a => ((p a : ℝ) : ℂ)))) :=
              complexMatrixInfNorm_mul_le _ _
          _ ≤ ((jordanBeta ρ t ^ (t - 1))⁻¹ * complexMatrixInfNorm X_inv) *
              (η * infNorm A * complexMatrixInfNorm X) :=
              mul_le_mul hDX hMid (complexMatrixInfNorm_nonneg _)
                (mul_nonneg (inv_nonneg.mpr hβt.le)
                  (complexMatrixInfNorm_nonneg X_inv))
      have h2 : ((jordanBeta ρ t ^ (t - 1))⁻¹ * complexMatrixInfNorm X_inv) *
            (η * infNorm A * complexMatrixInfNorm X)
          = (jordanBeta ρ t ^ (t - 1))⁻¹ * K := by
        rw [hKdef]; ring
      rw [h2] at h1
      exact h1
    calc complexMatrixInfNorm (fun i j =>
          complexMatrixMul (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ))
            (complexMatrixMul J (cDiagMatrix fun a => ((p a : ℝ) : ℂ))) i j +
          complexMatrixMul
            (complexMatrixMul (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ))
              X_inv)
            (complexMatrixMul (fun i j => ((ΔA i j : ℝ) : ℂ))
              (complexMatrixMul X
                (cDiagMatrix fun a => ((p a : ℝ) : ℂ)))) i j)
        ≤ complexMatrixInfNorm (complexMatrixMul
            (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ))
            (complexMatrixMul J (cDiagMatrix fun a => ((p a : ℝ) : ℂ)))) +
          complexMatrixInfNorm (complexMatrixMul
            (complexMatrixMul (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ))
              X_inv)
            (complexMatrixMul (fun i j => ((ΔA i j : ℝ) : ℂ))
              (complexMatrixMul X
                (cDiagMatrix fun a => ((p a : ℝ) : ℂ))))) :=
          complexMatrixInfNorm_add_le _ _
      _ ≤ ρ + jordanBeta ρ t + (jordanBeta ρ t ^ (t - 1))⁻¹ * K :=
          add_le_add hJconj hE

-- ============================================================
-- Theorem 18.1: axiom-free end-to-end forms (complex Jordan data)
-- ============================================================


































































































end NumStability
