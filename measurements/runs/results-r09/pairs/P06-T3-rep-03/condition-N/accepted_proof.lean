import HighamBench.P06Definitions

namespace HighamBench

open scoped BigOperators
open Asymptotics

private lemma p06_perturbed_product_decomposition
    {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (u : ℝ) (omega : Omega) (k : ℕ) :
    p06PerturbedHouseholderProduct P DeltaP u omega k =
      p06HouseholderProduct P k +
        p06FirstOrderHouseholderProduct P DeltaP u omega k +
          p06HigherOrderHouseholderProduct P DeltaP u omega k := by
  induction k with
  | zero =>
      simp [p06PerturbedHouseholderProduct, p06HouseholderProduct,
        p06FirstOrderHouseholderProduct, p06HigherOrderHouseholderProduct]
  | succ k ih =>
      simp only [p06PerturbedHouseholderProduct, p06HouseholderProduct,
        p06FirstOrderHouseholderProduct, p06HigherOrderHouseholderProduct]
      rw [ih]
      noncomm_ring

private lemma p06_matrix_const_mul_bigO
    {m : ℕ} (C : Matrix (Fin m) (Fin m) ℝ)
    (A : ℝ → Matrix (Fin m) (Fin m) ℝ) (scale : ℝ → ℝ)
    (hA : p06MatrixFamilyIsBigOAtZero A scale) :
    p06MatrixFamilyIsBigOAtZero (fun u ↦ C * A u) scale := by
  intro i j
  simpa only [Matrix.mul_apply] using
    (IsBigO.sum (s := Finset.univ)
      (fun k _ ↦ (hA k j).const_mul_left (C i k)))

private lemma p06_matrix_mul_const_bigO
    {m : ℕ} (A : ℝ → Matrix (Fin m) (Fin m) ℝ)
    (C : Matrix (Fin m) (Fin m) ℝ) (scale : ℝ → ℝ)
    (hA : p06MatrixFamilyIsBigOAtZero A scale) :
    p06MatrixFamilyIsBigOAtZero (fun u ↦ A u * C) scale := by
  intro i j
  simpa only [Matrix.mul_apply, mul_comm] using
    (IsBigO.sum (s := Finset.univ)
      (fun k _ ↦ (hA i k).const_mul_left (C k j)))

private lemma p06_matrix_mul_bigO
    {m : ℕ} (A B : ℝ → Matrix (Fin m) (Fin m) ℝ)
    (scaleA scaleB : ℝ → ℝ)
    (hA : p06MatrixFamilyIsBigOAtZero A scaleA)
    (hB : p06MatrixFamilyIsBigOAtZero B scaleB) :
    p06MatrixFamilyIsBigOAtZero
      (fun u ↦ A u * B u) (fun u ↦ scaleA u * scaleB u) := by
  intro i j
  simpa only [Matrix.mul_apply] using
    (IsBigO.sum (s := Finset.univ)
      (fun k _ ↦ (hA i k).mul (hB k j)))

private lemma p06_matrix_add_bigO
    {m : ℕ} (A B : ℝ → Matrix (Fin m) (Fin m) ℝ)
    (scale : ℝ → ℝ)
    (hA : p06MatrixFamilyIsBigOAtZero A scale)
    (hB : p06MatrixFamilyIsBigOAtZero B scale) :
    p06MatrixFamilyIsBigOAtZero (fun u ↦ A u + B u) scale := by
  intro i j
  exact (hA i j).add (hB i j)

private lemma p06_square_isBigO_linear :
    (fun u : ℝ ↦ u ^ 2) =O[nhds 0] (fun u : ℝ ↦ u) := by
  rw [isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) zero_lt_one] with u hu
  have hu' : |u| < 1 := by
    simpa [Real.dist_eq] using hu
  calc
    ‖u ^ 2‖ = |u| * |u| := by simp [pow_two, abs_mul]
    _ ≤ 1 * |u| := mul_le_mul_of_nonneg_right hu'.le (abs_nonneg u)
    _ = 1 * ‖u‖ := by simp

private lemma p06_first_and_higher_order_bigO
    {Omega : Type*} {m r : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (omega : Omega)
    (hDelta : ∀ j, j < r →
      p06MatrixFamilyIsBigOAtZero
        (fun u ↦ DeltaP u j omega) (fun u ↦ u)) :
    ∀ k, k ≤ r →
      p06MatrixFamilyIsBigOAtZero
          (fun u ↦ p06FirstOrderHouseholderProduct P DeltaP u omega k)
          (fun u ↦ u) ∧
        p06MatrixSecondOrderAtZero
          (fun u ↦ p06HigherOrderHouseholderProduct P DeltaP u omega k) := by
  intro k hk
  induction k with
  | zero =>
      constructor
      · intro i j
        simpa [p06FirstOrderHouseholderProduct] using
          (isBigO_zero (fun u : ℝ ↦ u) (nhds 0) :
            (fun _ : ℝ ↦ (0 : ℝ)) =O[nhds 0] (fun u : ℝ ↦ u))
      · intro i j
        simpa [p06HigherOrderHouseholderProduct] using
          (isBigO_zero (fun u : ℝ ↦ u ^ 2) (nhds 0) :
            (fun _ : ℝ ↦ (0 : ℝ)) =O[nhds 0] (fun u : ℝ ↦ u ^ 2))
  | succ k ih =>
      have hk' : k ≤ r := le_trans (Nat.le_succ k) hk
      rcases ih hk' with ⟨hfirst, hhigher⟩
      have hdelta := hDelta k (Nat.lt_of_succ_le hk)
      constructor
      · simpa only [p06FirstOrderHouseholderProduct] using
          p06_matrix_add_bigO
            (fun u ↦ P k *
              p06FirstOrderHouseholderProduct P DeltaP u omega k)
            (fun u ↦ DeltaP u k omega * p06HouseholderProduct P k)
            (fun u ↦ u)
            (p06_matrix_const_mul_bigO (P k)
              (fun u ↦ p06FirstOrderHouseholderProduct P DeltaP u omega k)
              (fun u ↦ u) hfirst)
            (p06_matrix_mul_const_bigO (fun u ↦ DeltaP u k omega)
              (p06HouseholderProduct P k) (fun u ↦ u) hdelta)
      · have hhigherLinear :
            p06MatrixFamilyIsBigOAtZero
              (fun u ↦ p06HigherOrderHouseholderProduct P DeltaP u omega k)
              (fun u ↦ u) :=
          fun i j ↦ (hhigher i j).trans p06_square_isBigO_linear
        have h₁ := p06_matrix_const_mul_bigO (P k)
          (fun u ↦ p06HigherOrderHouseholderProduct P DeltaP u omega k)
          (fun u ↦ u ^ 2) hhigher
        have h₂ := p06_matrix_mul_bigO
          (fun u ↦ DeltaP u k omega)
          (fun u ↦ p06FirstOrderHouseholderProduct P DeltaP u omega k)
          (fun u ↦ u) (fun u ↦ u) hdelta hfirst
        have h₃ := p06_matrix_mul_bigO
          (fun u ↦ DeltaP u k omega)
          (fun u ↦ p06HigherOrderHouseholderProduct P DeltaP u omega k)
          (fun u ↦ u) (fun u ↦ u) hdelta hhigherLinear
        have h₂' : p06MatrixFamilyIsBigOAtZero
            (fun u ↦ DeltaP u k omega *
              p06FirstOrderHouseholderProduct P DeltaP u omega k)
            (fun u ↦ u ^ 2) := by
          simpa only [pow_two] using h₂
        have h₃' : p06MatrixFamilyIsBigOAtZero
            (fun u ↦ DeltaP u k omega *
              p06HigherOrderHouseholderProduct P DeltaP u omega k)
            (fun u ↦ u ^ 2) := by
          simpa only [pow_two] using h₃
        simpa only [p06HigherOrderHouseholderProduct] using
          p06_matrix_add_bigO
            (fun u ↦ P k *
                p06HigherOrderHouseholderProduct P DeltaP u omega k +
              DeltaP u k omega *
                p06FirstOrderHouseholderProduct P DeltaP u omega k)
            (fun u ↦ DeltaP u k omega *
              p06HigherOrderHouseholderProduct P DeltaP u omega k)
            (fun u ↦ u ^ 2)
            (p06_matrix_add_bigO _ _ (fun u ↦ u ^ 2) h₁ h₂') h₃'

private lemma p06_householder_sequence_symmetric
    {m : ℕ} (v : ℕ → Fin m → ℝ) (j : ℕ) :
    Matrix.transpose (p06HouseholderSequenceMatrix v j) =
      p06HouseholderSequenceMatrix v j := by
  ext i k
  simp [p06HouseholderSequenceMatrix, p06HouseholderMatrix,
    p06FiniteId, eq_comm, mul_comm]

private lemma p06_householder_product_inverse_identities
    {m r : ℕ} (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (hSymm : ∀ j, Matrix.transpose (P j) = P j)
    (hInv : ∀ j, j < r → P j * P j = 1) :
    ∀ k, k ≤ r →
      p06HouseholderProduct P k *
          Matrix.transpose (p06HouseholderProduct P k) = 1 ∧
        Matrix.transpose (p06HouseholderProduct P k) *
          p06HouseholderProduct P k = 1 := by
  intro k hk
  induction k with
  | zero => simp [p06HouseholderProduct]
  | succ k ih =>
      have hk' : k ≤ r := le_trans (Nat.le_succ k) hk
      rcases ih hk' with ⟨ih₁, ih₂⟩
      have hPk := hInv k (Nat.lt_of_succ_le hk)
      simp only [p06HouseholderProduct, Matrix.transpose_mul, hSymm k]
      constructor
      · calc
          (P k * p06HouseholderProduct P k) *
              (Matrix.transpose (p06HouseholderProduct P k) * P k) =
              P k *
                (p06HouseholderProduct P k *
                  Matrix.transpose (p06HouseholderProduct P k)) * P k := by
                    noncomm_ring
          _ = 1 := by
            rw [ih₁]
            simpa only [mul_one] using hPk
      · calc
          (Matrix.transpose (p06HouseholderProduct P k) * P k) *
              (P k * p06HouseholderProduct P k) =
              Matrix.transpose (p06HouseholderProduct P k) *
                (P k * P k) * p06HouseholderProduct P k := by
                    noncomm_ring
          _ = 1 := by
            rw [hPk]
            simpa only [mul_one] using ih₂

private lemma p06_transformed_sum_eq_transpose_mul_first_order
    {Omega : Type*} {m r : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (hSymm : ∀ j, Matrix.transpose (P j) = P j)
    (hInv : ∀ j, j < r → P j * P j = 1)
    (u : ℝ) (omega : Omega) :
    ∀ k, k ≤ r →
      p06TransformedHouseholderInsertionSum P DeltaP u omega k =
        Matrix.transpose (p06HouseholderProduct P k) *
          p06FirstOrderHouseholderProduct P DeltaP u omega k := by
  intro k hk
  induction k with
  | zero =>
      simp [p06TransformedHouseholderInsertionSum,
        p06HouseholderProduct, p06FirstOrderHouseholderProduct]
  | succ k ih =>
      have hk' : k ≤ r := le_trans (Nat.le_succ k) hk
      have hPk := hInv k (Nat.lt_of_succ_le hk)
      change (∑ j ∈ Finset.range (k + 1),
        p06TransformedHouseholderInsertion P DeltaP u omega j) = _
      rw [Finset.sum_range_succ]
      change p06TransformedHouseholderInsertionSum P DeltaP u omega k +
        p06TransformedHouseholderInsertion P DeltaP u omega k = _
      rw [ih hk']
      simp only [p06TransformedHouseholderInsertion,
        p06FirstOrderHouseholderProduct, p06HouseholderProduct,
        Matrix.transpose_mul, hSymm k]
      calc
        Matrix.transpose (p06HouseholderProduct P k) *
              p06FirstOrderHouseholderProduct P DeltaP u omega k +
            Matrix.transpose (p06HouseholderProduct P k) * P k *
              DeltaP u k omega * p06HouseholderProduct P k =
            Matrix.transpose (p06HouseholderProduct P k) *
                (P k * P k) *
                  p06FirstOrderHouseholderProduct P DeltaP u omega k +
              Matrix.transpose (p06HouseholderProduct P k) * P k *
                DeltaP u k omega * p06HouseholderProduct P k := by
                  rw [hPk]
                  simp
        _ = Matrix.transpose (p06HouseholderProduct P k) * P k *
              (P k *
                  p06FirstOrderHouseholderProduct P DeltaP u omega k +
                DeltaP u k omega * p06HouseholderProduct P k) := by
                  noncomm_ring

theorem p06_t3_householder_product_first_order_expansion
    {Omega : Type*} [MeasurableSpace Omega] {m r : ℕ}
    (model : P06Model15 Omega)
    (run : P06HouseholderApplicationFamily Omega m r model)
    (c5 : ℕ) (lambda : ℝ) (_hc5 : 0 < c5) (_hlambda : 0 < lambda)
    (hlocal : P06Lemma42VectorAssumption run c5 lambda) :
    ∃ (unfactoredRemainder factoredRemainder :
        ℝ → Omega → Matrix (Fin m) (Fin m) ℝ),
      (∀ omega, omega ∈ hlocal.localEvent →
        p06MatrixSecondOrderAtZero
          (fun u ↦ unfactoredRemainder u omega)) ∧
      (∀ omega, omega ∈ hlocal.localEvent →
        p06MatrixSecondOrderAtZero
          (fun u ↦ factoredRemainder u omega)) ∧
      (∀ u omega,
        run.computed u omega =
          p06ApplicationExactState run +
            p06MatVec
              (p06ApplicationFirstOrderMatrix run u omega +
                unfactoredRemainder u omega)
              run.b) ∧
      (∀ u omega,
        run.computed u omega =
            p06ApplicationExactState run +
            p06MatVec
              (Matrix.transpose (p06ApplicationQ run) *
                (p06ApplicationFSum run u omega +
                  factoredRemainder u omega))
              run.b) ∧
      ∀ u omega (j : Fin r),
        p06ApplicationF run u omega j =
          Matrix.transpose
              (p06HouseholderProduct
                (p06HouseholderSequenceMatrix run.householderVector)
                (j.val + 1)) *
            run.localPerturbation u j.val omega *
              p06HouseholderProduct
                (p06HouseholderSequenceMatrix run.householderVector) j.val := by
  -- PROOF_START P06-T3-H001
  let P := p06HouseholderSequenceMatrix run.householderVector
  let R : ℝ → Omega → Matrix (Fin m) (Fin m) ℝ :=
    fun u omega ↦
      p06HigherOrderHouseholderProduct P run.localPerturbation u omega r
  refine ⟨R, fun u omega ↦ p06ApplicationQ run * R u omega,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro omega homega
    exact (p06_first_and_higher_order_bigO P run.localPerturbation omega
      (fun j hj ↦ hlocal.local_first_order omega homega j hj)
      r le_rfl).2
  · intro omega homega
    exact p06_matrix_const_mul_bigO (p06ApplicationQ run)
      (fun u ↦ R u omega) (fun u ↦ u ^ 2)
      ((p06_first_and_higher_order_bigO P run.localPerturbation omega
        (fun j hj ↦ hlocal.local_first_order omega homega j hj)
        r le_rfl).2)
  · intro u omega
    rw [run.computed_product,
      p06_perturbed_product_decomposition P run.localPerturbation u omega r]
    ext i
    simp [p06ApplicationExactState, p06ApplicationFirstOrderMatrix,
      p06MatVec, R, P, add_mul, Finset.sum_add_distrib]
    <;> abel
  · intro u omega
    have hSymm : ∀ j, Matrix.transpose (P j) = P j := by
      intro j
      exact p06_householder_sequence_symmetric run.householderVector j
    have hInv : ∀ j, j < r → P j * P j = 1 := by
      intro j hj
      exact run.householder_involutory j hj
    have horth := p06_householder_product_inverse_identities
      P hSymm hInv r le_rfl
    have hsum := p06_transformed_sum_eq_transpose_mul_first_order
      P run.localPerturbation hSymm hInv u omega r le_rfl
    have hmatrix :
        Matrix.transpose (p06ApplicationQ run) *
            (p06ApplicationFSum run u omega +
              p06ApplicationQ run * R u omega) =
          p06ApplicationFirstOrderMatrix run u omega + R u omega := by
      simp only [p06ApplicationQ, Matrix.transpose_transpose,
        p06ApplicationFSum, p06ApplicationFirstOrderMatrix]
      change p06HouseholderProduct P r *
          (p06TransformedHouseholderInsertionSum
              P run.localPerturbation u omega r +
            Matrix.transpose (p06HouseholderProduct P r) * R u omega) =
        p06FirstOrderHouseholderProduct
            P run.localPerturbation u omega r + R u omega
      rw [hsum]
      calc
        p06HouseholderProduct P r *
            (Matrix.transpose (p06HouseholderProduct P r) *
                p06FirstOrderHouseholderProduct
                  P run.localPerturbation u omega r +
              Matrix.transpose (p06HouseholderProduct P r) * R u omega) =
            (p06HouseholderProduct P r *
                Matrix.transpose (p06HouseholderProduct P r)) *
                  p06FirstOrderHouseholderProduct
                    P run.localPerturbation u omega r +
              (p06HouseholderProduct P r *
                Matrix.transpose (p06HouseholderProduct P r)) * R u omega := by
                  noncomm_ring
        _ = p06FirstOrderHouseholderProduct
              P run.localPerturbation u omega r + R u omega := by
                rw [horth.1]
                simp
    rw [hmatrix, run.computed_product,
      p06_perturbed_product_decomposition P run.localPerturbation u omega r]
    ext i
    simp [p06ApplicationExactState, p06ApplicationFirstOrderMatrix,
      p06MatVec, R, P,
      add_mul, Finset.sum_add_distrib]
    <;> abel
  · intro u omega j
    rfl

end HighamBench
