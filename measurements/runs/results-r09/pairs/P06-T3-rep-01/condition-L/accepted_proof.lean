import HighamBench.P06Definitions

namespace HighamBench

open Filter Asymptotics

private theorem p06_matrixFamily_zero_isBigO {m : ℕ}
    (scale : ℝ → ℝ) :
    p06MatrixFamilyIsBigOAtZero
      (fun _ => (0 : Matrix (Fin m) (Fin m) ℝ)) scale := by
  intro i j
  exact isBigO_zero scale (nhds 0)

private theorem p06_matrixFamily_add_isBigO {m : ℕ}
    {A B : ℝ → Matrix (Fin m) (Fin m) ℝ} {scale : ℝ → ℝ}
    (hA : p06MatrixFamilyIsBigOAtZero A scale)
    (hB : p06MatrixFamilyIsBigOAtZero B scale) :
    p06MatrixFamilyIsBigOAtZero (fun u => A u + B u) scale := by
  intro i j
  simpa using (hA i j).add (hB i j)

private theorem p06_fixed_mul_matrixFamily_isBigO {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ)
    {B : ℝ → Matrix (Fin m) (Fin m) ℝ} {scale : ℝ → ℝ}
    (hB : p06MatrixFamilyIsBigOAtZero B scale) :
    p06MatrixFamilyIsBigOAtZero (fun u => A * B u) scale := by
  intro i j
  simpa only [Matrix.mul_apply] using
    (IsBigO.sum (s := Finset.univ) (fun k _ =>
      (hB k j).const_mul_left (A i k)))

private theorem p06_matrixFamily_mul_fixed_isBigO {m : ℕ}
    {A : ℝ → Matrix (Fin m) (Fin m) ℝ}
    (B : Matrix (Fin m) (Fin m) ℝ) {scale : ℝ → ℝ}
    (hA : p06MatrixFamilyIsBigOAtZero A scale) :
    p06MatrixFamilyIsBigOAtZero (fun u => A u * B) scale := by
  intro i j
  have h := IsBigO.sum (s := Finset.univ) (fun k _ =>
    (hA i k).const_mul_left (B k j))
  simpa only [Matrix.mul_apply, mul_comm] using h

private theorem p06_matrixFamily_mul_isBigO {m : ℕ}
    {A B : ℝ → Matrix (Fin m) (Fin m) ℝ}
    {scaleA scaleB : ℝ → ℝ}
    (hA : p06MatrixFamilyIsBigOAtZero A scaleA)
    (hB : p06MatrixFamilyIsBigOAtZero B scaleB) :
    p06MatrixFamilyIsBigOAtZero
      (fun u => A u * B u) (fun u => scaleA u * scaleB u) := by
  intro i j
  simpa only [Matrix.mul_apply] using
    (IsBigO.sum (s := Finset.univ) (fun k _ => (hA i k).mul (hB k j)))

private theorem p06_matrixFamily_mul_linear_isSecondOrder {m : ℕ}
    {A B : ℝ → Matrix (Fin m) (Fin m) ℝ}
    (hA : p06MatrixFamilyIsBigOAtZero A (fun u => u))
    (hB : p06MatrixFamilyIsBigOAtZero B (fun u => u)) :
    p06MatrixSecondOrderAtZero (fun u => A u * B u) := by
  simpa only [p06MatrixSecondOrderAtZero, pow_two] using
    p06_matrixFamily_mul_isBigO hA hB

private theorem p06_secondOrder_isFirstOrder {m : ℕ}
    {A : ℝ → Matrix (Fin m) (Fin m) ℝ}
    (hA : p06MatrixSecondOrderAtZero A) :
    p06MatrixFamilyIsBigOAtZero A (fun u => u) := by
  intro i j
  apply (hA i j).trans
  simpa using
    (isLittleO_pow_pow (show (1 : ℕ) < 2 by omega)).isBigO

private theorem p06_firstAndHigherOrder_orders
    {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (omega : Omega) (k : ℕ)
    (hDelta : ∀ j, j < k →
      p06MatrixFamilyIsBigOAtZero
        (fun u => DeltaP u j omega) (fun u => u)) :
    p06MatrixFamilyIsBigOAtZero
        (fun u => p06FirstOrderHouseholderProduct P DeltaP u omega k)
        (fun u => u) ∧
      p06MatrixSecondOrderAtZero
        (fun u => p06HigherOrderHouseholderProduct P DeltaP u omega k) := by
  induction k with
  | zero =>
      constructor
      · simpa only [p06FirstOrderHouseholderProduct] using
          (p06_matrixFamily_zero_isBigO (m := m) (fun u : ℝ => u))
      · simpa only [p06HigherOrderHouseholderProduct,
          p06MatrixSecondOrderAtZero] using
          (p06_matrixFamily_zero_isBigO (m := m) (fun u : ℝ => u ^ 2))
  | succ k ih =>
      have hPrev := ih (fun j hj => hDelta j (Nat.lt.step hj))
      have hHere := hDelta k (Nat.lt_succ_self k)
      constructor
      · simpa only [p06FirstOrderHouseholderProduct] using
          p06_matrixFamily_add_isBigO
            (p06_fixed_mul_matrixFamily_isBigO (P k) hPrev.1)
            (p06_matrixFamily_mul_fixed_isBigO
              (p06HouseholderProduct P k) hHere)
      · have h₁ : p06MatrixSecondOrderAtZero
            (fun u => P k *
              p06HigherOrderHouseholderProduct P DeltaP u omega k) :=
          p06_fixed_mul_matrixFamily_isBigO (P k) hPrev.2
        have h₂ : p06MatrixSecondOrderAtZero
            (fun u => DeltaP u k omega *
              p06FirstOrderHouseholderProduct P DeltaP u omega k) :=
          p06_matrixFamily_mul_linear_isSecondOrder hHere hPrev.1
        have h₃ : p06MatrixSecondOrderAtZero
            (fun u => DeltaP u k omega *
              p06HigherOrderHouseholderProduct P DeltaP u omega k) :=
          p06_matrixFamily_mul_linear_isSecondOrder hHere
            (p06_secondOrder_isFirstOrder hPrev.2)
        simpa only [p06HigherOrderHouseholderProduct] using
          p06_matrixFamily_add_isBigO
            (p06_matrixFamily_add_isBigO h₁ h₂) h₃

private theorem p06_perturbedProduct_decomposition
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
      simp only [p06PerturbedHouseholderProduct, p06HouseholderProduct,
        p06FirstOrderHouseholderProduct, p06HigherOrderHouseholderProduct,
        add_zero]
  | succ k ih =>
      rw [p06PerturbedHouseholderProduct, p06HouseholderProduct,
        p06FirstOrderHouseholderProduct, p06HigherOrderHouseholderProduct, ih]
      noncomm_ring

private theorem p06_householderSequenceMatrix_transpose {m : ℕ}
    (v : ℕ → Fin m → ℝ) (j : ℕ) :
    Matrix.transpose (p06HouseholderSequenceMatrix v j) =
      p06HouseholderSequenceMatrix v j := by
  ext i k
  simp only [p06HouseholderSequenceMatrix, p06HouseholderMatrix,
    Matrix.transpose_apply]
  unfold p06FiniteId
  by_cases h : i = k
  · subst k
    rfl
  · have h' : k ≠ i := Ne.symm h
    simp only [h, h', if_false]
    ring

private theorem p06_householderProduct_mul_transpose_eq_one {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (hSymm : ∀ j, Matrix.transpose (P j) = P j)
    (k : ℕ) (hInv : ∀ j, j < k → P j * P j = 1) :
    p06HouseholderProduct P k *
        Matrix.transpose (p06HouseholderProduct P k) = 1 := by
  induction k with
  | zero =>
      simp only [p06HouseholderProduct, Matrix.transpose_one,
        Matrix.mul_one]
  | succ k ih =>
      have ihPrev := ih (fun j hj => hInv j (Nat.lt.step hj))
      rw [p06HouseholderProduct, Matrix.transpose_mul, hSymm k]
      calc
        (P k * p06HouseholderProduct P k) *
              (Matrix.transpose (p06HouseholderProduct P k) * P k) =
            P k *
              (p06HouseholderProduct P k *
                Matrix.transpose (p06HouseholderProduct P k)) * P k := by
                  simp only [mul_assoc]
        _ = P k * P k := by rw [ihPrev, Matrix.mul_one]
        _ = 1 := hInv k (Nat.lt_succ_self k)

private theorem p06_firstOrder_eq_product_mul_transformedSum
    {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (u : ℝ) (omega : Omega) (k : ℕ)
    (hSymm : ∀ j, Matrix.transpose (P j) = P j)
    (hInv : ∀ j, j < k → P j * P j = 1) :
    p06FirstOrderHouseholderProduct P DeltaP u omega k =
      p06HouseholderProduct P k *
        p06TransformedHouseholderInsertionSum P DeltaP u omega k := by
  induction k with
  | zero =>
      simp only [p06FirstOrderHouseholderProduct,
        p06HouseholderProduct, p06TransformedHouseholderInsertionSum,
        Finset.range_zero, Finset.sum_empty, Matrix.mul_zero]
  | succ k ih =>
      have hInvPrev : ∀ j, j < k → P j * P j = 1 :=
        fun j hj => hInv j (Nat.lt.step hj)
      have ihPrev := ih hInvPrev
      have hOrth := p06_householderProduct_mul_transpose_eq_one
        P hSymm (k + 1) hInv
      have hOrth' :
          (P k * p06HouseholderProduct P k) *
              Matrix.transpose (p06HouseholderProduct P (k + 1)) = 1 := by
        simpa only [p06HouseholderProduct] using hOrth
      have hSum :
          p06TransformedHouseholderInsertionSum P DeltaP u omega (k + 1) =
            p06TransformedHouseholderInsertionSum P DeltaP u omega k +
              p06TransformedHouseholderInsertion P DeltaP u omega k := by
        simp only [p06TransformedHouseholderInsertionSum,
          Finset.sum_range_succ]
      rw [p06FirstOrderHouseholderProduct, ihPrev,
        p06HouseholderProduct, hSum,
        p06TransformedHouseholderInsertion]
      rw [Matrix.mul_add]
      rw [mul_assoc
        (Matrix.transpose (p06HouseholderProduct P (k + 1)))
        (DeltaP u k omega) (p06HouseholderProduct P k)]
      rw [← mul_assoc
        (P k * p06HouseholderProduct P k)
        (Matrix.transpose (p06HouseholderProduct P (k + 1)))
        (DeltaP u k omega * p06HouseholderProduct P k)]
      rw [hOrth', Matrix.one_mul]
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
  let P : ℕ → Matrix (Fin m) (Fin m) ℝ :=
    p06HouseholderSequenceMatrix run.householderVector
  let unfactoredRemainder : ℝ → Omega → Matrix (Fin m) (Fin m) ℝ :=
    fun u omega =>
      p06HigherOrderHouseholderProduct
        P run.localPerturbation u omega r
  let factoredRemainder : ℝ → Omega → Matrix (Fin m) (Fin m) ℝ :=
    fun u omega =>
      p06ApplicationQ run * unfactoredRemainder u omega
  have hUnfactoredOrder : ∀ omega, omega ∈ hlocal.localEvent →
      p06MatrixSecondOrderAtZero
        (fun u => unfactoredRemainder u omega) := by
    intro omega homega
    exact (p06_firstAndHigherOrder_orders
      P run.localPerturbation omega r
      (fun j hj => hlocal.local_first_order omega homega j hj)).2
  have hFactoredOrder : ∀ omega, omega ∈ hlocal.localEvent →
      p06MatrixSecondOrderAtZero
        (fun u => factoredRemainder u omega) := by
    intro omega homega
    exact p06_fixed_mul_matrixFamily_isBigO (p06ApplicationQ run)
      (hUnfactoredOrder omega homega)
  have hUnfactored : ∀ u omega,
      run.computed u omega =
        p06ApplicationExactState run +
          p06MatVec
            (p06ApplicationFirstOrderMatrix run u omega +
              unfactoredRemainder u omega)
            run.b := by
    intro u omega
    rw [run.computed_product]
    rw [p06_perturbedProduct_decomposition]
    ext i
    simp only [p06ApplicationExactState,
      p06ApplicationFirstOrderMatrix, p06MatVec, unfactoredRemainder, P,
      Matrix.add_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    abel
  have hFactored : ∀ u omega,
      run.computed u omega =
          p06ApplicationExactState run +
          p06MatVec
            (Matrix.transpose (p06ApplicationQ run) *
              (p06ApplicationFSum run u omega +
                factoredRemainder u omega))
            run.b := by
    intro u omega
    have hSymm : ∀ j, Matrix.transpose (P j) = P j := by
      intro j
      exact p06_householderSequenceMatrix_transpose
        run.householderVector j
    have hFirst := p06_firstOrder_eq_product_mul_transformedSum
      P run.localPerturbation u omega r hSymm
      (fun j hj => run.householder_involutory j hj)
    have hOrth := p06_householderProduct_mul_transpose_eq_one
      P hSymm r (fun j hj => run.householder_involutory j hj)
    have hMatrix :
        p06ApplicationFirstOrderMatrix run u omega +
            unfactoredRemainder u omega =
          Matrix.transpose (p06ApplicationQ run) *
            (p06ApplicationFSum run u omega +
              factoredRemainder u omega) := by
      change
        p06FirstOrderHouseholderProduct P run.localPerturbation u omega r +
            p06HigherOrderHouseholderProduct
              P run.localPerturbation u omega r =
          Matrix.transpose (Matrix.transpose (p06HouseholderProduct P r)) *
            (p06TransformedHouseholderInsertionSum
                P run.localPerturbation u omega r +
              Matrix.transpose (p06HouseholderProduct P r) *
                p06HigherOrderHouseholderProduct
                  P run.localPerturbation u omega r)
      rw [Matrix.transpose_transpose, Matrix.mul_add, hFirst]
      rw [← mul_assoc, hOrth, Matrix.one_mul]
    rw [hUnfactored u omega, hMatrix]
  refine ⟨unfactoredRemainder, factoredRemainder,
    hUnfactoredOrder, hFactoredOrder, hUnfactored, hFactored, ?_⟩
  intro u omega j
  rfl

end HighamBench
