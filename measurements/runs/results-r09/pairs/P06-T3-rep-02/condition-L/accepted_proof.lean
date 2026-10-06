import HighamBench.P06Definitions

namespace HighamBench

open scoped BigOperators

private theorem p06_matrixFamilyIsBigO_add {m : ℕ}
    {A B : ℝ → Matrix (Fin m) (Fin m) ℝ} {s : ℝ → ℝ}
    (hA : p06MatrixFamilyIsBigOAtZero A s)
    (hB : p06MatrixFamilyIsBigOAtZero B s) :
    p06MatrixFamilyIsBigOAtZero (fun u ↦ A u + B u) s := by
  intro i j
  simpa using (hA i j).add (hB i j)

private theorem p06_matrixFamilyIsBigO_mul {m : ℕ}
    {A B : ℝ → Matrix (Fin m) (Fin m) ℝ} {s t : ℝ → ℝ}
    (hA : p06MatrixFamilyIsBigOAtZero A s)
    (hB : p06MatrixFamilyIsBigOAtZero B t) :
    p06MatrixFamilyIsBigOAtZero
      (fun u ↦ A u * B u) (fun u ↦ s u * t u) := by
  intro i j
  simp only [Matrix.mul_apply]
  apply Asymptotics.IsBigO.sum
  intro k _hk
  exact (hA i k).mul (hB k j)

private theorem p06_matrixFamilyIsBigO_fixedLeft {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ)
    {B : ℝ → Matrix (Fin m) (Fin m) ℝ} {s : ℝ → ℝ}
    (hB : p06MatrixFamilyIsBigOAtZero B s) :
    p06MatrixFamilyIsBigOAtZero (fun u ↦ A * B u) s := by
  intro i j
  simp only [Matrix.mul_apply]
  apply Asymptotics.IsBigO.sum
  intro k _hk
  exact (hB k j).const_mul_left (A i k)

private theorem p06_matrixFamilyIsBigO_fixedRight {m : ℕ}
    {A : ℝ → Matrix (Fin m) (Fin m) ℝ} {s : ℝ → ℝ}
    (B : Matrix (Fin m) (Fin m) ℝ)
    (hA : p06MatrixFamilyIsBigOAtZero A s) :
    p06MatrixFamilyIsBigOAtZero (fun u ↦ A u * B) s := by
  intro i j
  simp only [Matrix.mul_apply]
  apply Asymptotics.IsBigO.sum
  intro k _hk
  simpa only [mul_comm] using (hA i k).const_mul_left (B k j)

private theorem p06_matrixFamilyIsBigO_linear_to_one {m : ℕ}
    {A : ℝ → Matrix (Fin m) (Fin m) ℝ}
    (hA : p06MatrixFamilyIsBigOAtZero A (fun u ↦ u)) :
    p06MatrixFamilyIsBigOAtZero A (fun _ ↦ (1 : ℝ)) := by
  intro i j
  exact (hA i j).trans (by
    simpa only [id_eq] using
      (Filter.tendsto_id.isBigO_one ℝ :
        (fun u : ℝ ↦ u) =O[nhds 0] (fun _ ↦ (1 : ℝ))))

private theorem p06_perturbed_product_decomposition
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
      rw [p06PerturbedHouseholderProduct, p06HouseholderProduct,
        p06FirstOrderHouseholderProduct, p06HigherOrderHouseholderProduct, ih]
      noncomm_ring

private theorem p06_first_and_higher_order
    {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (omega : Omega) (r : ℕ)
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
        simp only [p06FirstOrderHouseholderProduct]
        exact Asymptotics.isBigO_zero (fun u : ℝ ↦ u) (nhds 0)
      · intro i j
        simp only [p06HigherOrderHouseholderProduct]
        exact Asymptotics.isBigO_zero (fun u : ℝ ↦ u ^ 2) (nhds 0)
  | succ k ih =>
      have hkr : k ≤ r := Nat.le_trans (Nat.le_succ k) hk
      obtain ⟨hFirst, hHigher⟩ := ih hkr
      have hD := hDelta k (lt_of_lt_of_le (Nat.lt_succ_self k) hk)
      constructor
      · simp only [p06FirstOrderHouseholderProduct]
        exact p06_matrixFamilyIsBigO_add
          (p06_matrixFamilyIsBigO_fixedLeft (P k) hFirst)
          (p06_matrixFamilyIsBigO_fixedRight (p06HouseholderProduct P k) hD)
      · simp only [p06HigherOrderHouseholderProduct]
        apply p06_matrixFamilyIsBigO_add
        · exact p06_matrixFamilyIsBigO_add
            (p06_matrixFamilyIsBigO_fixedLeft (P k) hHigher)
            (by
              simpa only [pow_two] using
                p06_matrixFamilyIsBigO_mul hD hFirst)
        · have hD_one := p06_matrixFamilyIsBigO_linear_to_one hD
          simpa only [one_mul] using
            p06_matrixFamilyIsBigO_mul hD_one hHigher

private theorem p06_householderSequenceMatrix_transpose {m : ℕ}
    (v : ℕ → Fin m → ℝ) (j : ℕ) :
    Matrix.transpose (p06HouseholderSequenceMatrix v j) =
      p06HouseholderSequenceMatrix v j := by
  ext i k
  simp [p06HouseholderSequenceMatrix, p06HouseholderMatrix,
    p06FiniteId, eq_comm, mul_comm]

private theorem p06_householderProduct_mul_transpose {m r : ℕ}
    (v : ℕ → Fin m → ℝ)
    (hinv : ∀ j, j < r →
      p06HouseholderSequenceMatrix v j *
        p06HouseholderSequenceMatrix v j = 1) :
    ∀ k, k ≤ r →
      p06HouseholderProduct (p06HouseholderSequenceMatrix v) k *
        Matrix.transpose
          (p06HouseholderProduct (p06HouseholderSequenceMatrix v) k) = 1 := by
  intro k hk
  induction k with
  | zero => simp [p06HouseholderProduct]
  | succ k ih =>
      have hkr : k ≤ r := Nat.le_trans (Nat.le_succ k) hk
      have hstep : k < r := lt_of_lt_of_le (Nat.lt_succ_self k) hk
      rw [p06HouseholderProduct, Matrix.transpose_mul,
        p06_householderSequenceMatrix_transpose]
      calc
        (p06HouseholderSequenceMatrix v k *
              p06HouseholderProduct (p06HouseholderSequenceMatrix v) k) *
            (Matrix.transpose
                (p06HouseholderProduct (p06HouseholderSequenceMatrix v) k) *
              p06HouseholderSequenceMatrix v k) =
            p06HouseholderSequenceMatrix v k *
              (p06HouseholderProduct (p06HouseholderSequenceMatrix v) k *
                Matrix.transpose
                  (p06HouseholderProduct (p06HouseholderSequenceMatrix v) k)) *
              p06HouseholderSequenceMatrix v k := by noncomm_ring
        _ = p06HouseholderSequenceMatrix v k * 1 *
              p06HouseholderSequenceMatrix v k := by rw [ih hkr]
        _ = 1 := by simpa using hinv k hstep

private theorem p06_firstOrderProduct_factorization
    {Omega : Type*} {m r : ℕ}
    (v : ℕ → Fin m → ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (hinv : ∀ j, j < r →
      p06HouseholderSequenceMatrix v j *
        p06HouseholderSequenceMatrix v j = 1)
    (u : ℝ) (omega : Omega) :
    ∀ k, k ≤ r →
      p06FirstOrderHouseholderProduct
          (p06HouseholderSequenceMatrix v) DeltaP u omega k =
        p06HouseholderProduct (p06HouseholderSequenceMatrix v) k *
          p06TransformedHouseholderInsertionSum
            (p06HouseholderSequenceMatrix v) DeltaP u omega k := by
  intro k hk
  induction k with
  | zero =>
      simp [p06FirstOrderHouseholderProduct, p06HouseholderProduct,
        p06TransformedHouseholderInsertionSum]
  | succ k ih =>
      have hkr : k ≤ r := Nat.le_trans (Nat.le_succ k) hk
      have horth := p06_householderProduct_mul_transpose v hinv (k + 1) hk
      have horth' :
          (p06HouseholderSequenceMatrix v k *
              p06HouseholderProduct (p06HouseholderSequenceMatrix v) k) *
            Matrix.transpose
              (p06HouseholderSequenceMatrix v k *
                p06HouseholderProduct (p06HouseholderSequenceMatrix v) k) = 1 := by
        simpa only [p06HouseholderProduct] using horth
      rw [p06FirstOrderHouseholderProduct, ih hkr]
      simp only [p06TransformedHouseholderInsertionSum,
        Finset.sum_range_succ, p06TransformedHouseholderInsertion,
        p06HouseholderProduct]
      have hcancel :
          (p06HouseholderSequenceMatrix v k *
              p06HouseholderProduct (p06HouseholderSequenceMatrix v) k) *
                (Matrix.transpose
                    (p06HouseholderSequenceMatrix v k *
                      p06HouseholderProduct
                        (p06HouseholderSequenceMatrix v) k) *
                  DeltaP u k omega *
                    p06HouseholderProduct
                      (p06HouseholderSequenceMatrix v) k) =
            DeltaP u k omega *
              p06HouseholderProduct (p06HouseholderSequenceMatrix v) k := by
        calc
          _ = ((p06HouseholderSequenceMatrix v k *
                  p06HouseholderProduct (p06HouseholderSequenceMatrix v) k) *
                Matrix.transpose
                  (p06HouseholderSequenceMatrix v k *
                    p06HouseholderProduct
                      (p06HouseholderSequenceMatrix v) k)) *
              (DeltaP u k omega *
                p06HouseholderProduct
                  (p06HouseholderSequenceMatrix v) k) := by noncomm_ring
          _ = _ := by rw [horth']; simp
      rw [mul_add, hcancel]
      simp only [mul_assoc]

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
  let unfactoredRemainder :
      ℝ → Omega → Matrix (Fin m) (Fin m) ℝ :=
    fun u omega ↦
      p06HigherOrderHouseholderProduct
        (p06HouseholderSequenceMatrix run.householderVector)
        run.localPerturbation u omega r
  let factoredRemainder :
      ℝ → Omega → Matrix (Fin m) (Fin m) ℝ :=
    fun u omega ↦
      Matrix.transpose
          (p06HouseholderProduct
            (p06HouseholderSequenceMatrix run.householderVector) r) *
        unfactoredRemainder u omega
  have hHigher : ∀ omega, omega ∈ hlocal.localEvent →
      p06MatrixSecondOrderAtZero
        (fun u ↦ unfactoredRemainder u omega) := by
    intro omega homega
    exact (p06_first_and_higher_order
      (p06HouseholderSequenceMatrix run.householderVector)
      run.localPerturbation omega r
      (hlocal.local_first_order omega homega) r (Nat.le_refl r)).2
  have hFactored : ∀ omega, omega ∈ hlocal.localEvent →
      p06MatrixSecondOrderAtZero
        (fun u ↦ factoredRemainder u omega) := by
    intro omega homega
    exact p06_matrixFamilyIsBigO_fixedLeft
      (Matrix.transpose
        (p06HouseholderProduct
          (p06HouseholderSequenceMatrix run.householderVector) r))
      (hHigher omega homega)
  have hUnfactored : ∀ u omega,
      run.computed u omega =
        p06ApplicationExactState run +
          p06MatVec
            (p06ApplicationFirstOrderMatrix run u omega +
              unfactoredRemainder u omega)
            run.b := by
    intro u omega
    rw [run.computed_product,
      p06_perturbed_product_decomposition]
    funext i
    simp only [p06ApplicationExactState,
      p06ApplicationFirstOrderMatrix, p06MatVec, Matrix.add_apply,
      add_mul, Finset.sum_add_distrib, Pi.add_apply,
      unfactoredRemainder]
    abel
  have hOrth := p06_householderProduct_mul_transpose
    run.householderVector run.householder_involutory r (Nat.le_refl r)
  have hFactoredMatrix : ∀ u omega,
      Matrix.transpose (p06ApplicationQ run) *
          (p06ApplicationFSum run u omega +
            factoredRemainder u omega) =
        p06ApplicationFirstOrderMatrix run u omega +
          unfactoredRemainder u omega := by
    intro u omega
    have hFirst := p06_firstOrderProduct_factorization
      run.householderVector run.localPerturbation
      run.householder_involutory u omega r (Nat.le_refl r)
    simp only [p06ApplicationQ, Matrix.transpose_transpose,
      p06ApplicationFSum, p06ApplicationFirstOrderMatrix,
      factoredRemainder]
    calc
      p06HouseholderProduct
            (p06HouseholderSequenceMatrix run.householderVector) r *
          (p06TransformedHouseholderInsertionSum
              (p06HouseholderSequenceMatrix run.householderVector)
              run.localPerturbation u omega r +
            Matrix.transpose
                (p06HouseholderProduct
                  (p06HouseholderSequenceMatrix run.householderVector) r) *
              unfactoredRemainder u omega) =
          p06HouseholderProduct
                (p06HouseholderSequenceMatrix run.householderVector) r *
              p06TransformedHouseholderInsertionSum
                (p06HouseholderSequenceMatrix run.householderVector)
                run.localPerturbation u omega r +
            (p06HouseholderProduct
                (p06HouseholderSequenceMatrix run.householderVector) r *
              Matrix.transpose
                (p06HouseholderProduct
                  (p06HouseholderSequenceMatrix run.householderVector) r)) *
              unfactoredRemainder u omega := by noncomm_ring
      _ = p06HouseholderProduct
                (p06HouseholderSequenceMatrix run.householderVector) r *
              p06TransformedHouseholderInsertionSum
                (p06HouseholderSequenceMatrix run.householderVector)
                run.localPerturbation u omega r +
            unfactoredRemainder u omega := by rw [hOrth]; simp
      _ = p06FirstOrderHouseholderProduct
                (p06HouseholderSequenceMatrix run.householderVector)
                run.localPerturbation u omega r +
            unfactoredRemainder u omega := by rw [hFirst]
  refine ⟨unfactoredRemainder, factoredRemainder,
    hHigher, hFactored, hUnfactored, ?_, ?_⟩
  · intro u omega
    rw [hUnfactored u omega, hFactoredMatrix u omega]
  · intro u omega j
    rfl

end HighamBench
