import HighamBench.P06Definitions

namespace HighamBench

open scoped BigOperators

private lemma p06_matrix_bigO_zero {m : ℕ} (f : ℝ → ℝ) :
    p06MatrixFamilyIsBigOAtZero
      (fun _ : ℝ ↦ (0 : Matrix (Fin m) (Fin m) ℝ)) f := by
  intro i j
  simpa using (Asymptotics.isBigO_zero (l := nhds (0 : ℝ)) f)

private lemma p06_matrix_bigO_add {m : ℕ}
    {A B : ℝ → Matrix (Fin m) (Fin m) ℝ} {f : ℝ → ℝ}
    (hA : p06MatrixFamilyIsBigOAtZero A f)
    (hB : p06MatrixFamilyIsBigOAtZero B f) :
    p06MatrixFamilyIsBigOAtZero (fun u ↦ A u + B u) f := by
  intro i j
  exact (hA i j).add (hB i j)

private lemma p06_matrix_bigO_const_mul {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ)
    {B : ℝ → Matrix (Fin m) (Fin m) ℝ} {f : ℝ → ℝ}
    (hB : p06MatrixFamilyIsBigOAtZero B f) :
    p06MatrixFamilyIsBigOAtZero (fun u ↦ A * B u) f := by
  intro i j
  simpa only [Matrix.mul_apply] using
    (Asymptotics.IsBigO.sum (s := Finset.univ)
      (fun k _ ↦ (hB k j).const_mul_left (A i k)))

private lemma p06_matrix_bigO_mul_const {m : ℕ}
    {A : ℝ → Matrix (Fin m) (Fin m) ℝ}
    (B : Matrix (Fin m) (Fin m) ℝ) {f : ℝ → ℝ}
    (hA : p06MatrixFamilyIsBigOAtZero A f) :
    p06MatrixFamilyIsBigOAtZero (fun u ↦ A u * B) f := by
  intro i j
  simpa only [Matrix.mul_apply] using
    (Asymptotics.IsBigO.sum (s := Finset.univ)
      (fun k _ ↦ ((hA i k).const_mul_left (B k j)).congr_left
        (fun u ↦ mul_comm (B k j) (A u i k))))

private lemma p06_matrix_bigO_mul {m : ℕ}
    {A B : ℝ → Matrix (Fin m) (Fin m) ℝ} {f g : ℝ → ℝ}
    (hA : p06MatrixFamilyIsBigOAtZero A f)
    (hB : p06MatrixFamilyIsBigOAtZero B g) :
    p06MatrixFamilyIsBigOAtZero
      (fun u ↦ A u * B u) (fun u ↦ f u * g u) := by
  intro i j
  simpa only [Matrix.mul_apply] using
    (Asymptotics.IsBigO.sum (s := Finset.univ)
      (fun k _ ↦ (hA i k).mul (hB k j)))

private lemma p06_first_order_bigO {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (omega : Omega) (k : ℕ)
    (hDelta : ∀ j, j < k →
      p06MatrixFamilyIsBigOAtZero
        (fun u ↦ DeltaP u j omega) (fun u ↦ u)) :
    p06MatrixFamilyIsBigOAtZero
      (fun u ↦ p06FirstOrderHouseholderProduct P DeltaP u omega k)
      (fun u ↦ u) := by
  induction k with
  | zero =>
      simpa [p06FirstOrderHouseholderProduct] using
        (p06_matrix_bigO_zero (m := m) (fun u : ℝ ↦ u))
  | succ k ih =>
      simp only [p06FirstOrderHouseholderProduct]
      apply p06_matrix_bigO_add
      · exact p06_matrix_bigO_const_mul (P k)
          (ih (fun j hj ↦ hDelta j (Nat.lt_succ_of_lt hj)))
      · exact p06_matrix_bigO_mul_const (p06HouseholderProduct P k)
          (hDelta k (Nat.lt_succ_self k))

private lemma p06_higher_order_bigO {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (omega : Omega) (k : ℕ)
    (hDelta : ∀ j, j < k →
      p06MatrixFamilyIsBigOAtZero
        (fun u ↦ DeltaP u j omega) (fun u ↦ u)) :
    p06MatrixSecondOrderAtZero
      (fun u ↦ p06HigherOrderHouseholderProduct P DeltaP u omega k) := by
  induction k with
  | zero =>
      simpa [p06MatrixSecondOrderAtZero, p06HigherOrderHouseholderProduct] using
        (p06_matrix_bigO_zero (m := m) (fun u : ℝ ↦ u ^ 2))
  | succ k ih =>
      have hDelta' : ∀ j, j < k →
          p06MatrixFamilyIsBigOAtZero
            (fun u ↦ DeltaP u j omega) (fun u ↦ u) :=
        fun j hj ↦ hDelta j (Nat.lt_succ_of_lt hj)
      have hHigher := ih hDelta'
      have hFirst := p06_first_order_bigO P DeltaP omega k hDelta'
      have hSquareLinear :
          (fun u : ℝ ↦ u ^ 2) =O[nhds 0] (fun u : ℝ ↦ u) :=
        by simpa using
          (Asymptotics.isLittleO_pow_pow (by omega : 1 < 2)).isBigO
      have hHigherLinear : p06MatrixFamilyIsBigOAtZero
          (fun u ↦ p06HigherOrderHouseholderProduct P DeltaP u omega k)
          (fun u ↦ u) :=
        fun i j ↦ (hHigher i j).trans hSquareLinear
      simp only [p06MatrixSecondOrderAtZero,
        p06HigherOrderHouseholderProduct]
      apply p06_matrix_bigO_add
      · exact p06_matrix_bigO_add
          (p06_matrix_bigO_const_mul (P k) hHigher)
          (by
            simpa only [pow_two] using
              p06_matrix_bigO_mul
                (hDelta k (Nat.lt_succ_self k)) hFirst)
      · simpa only [pow_two] using
          p06_matrix_bigO_mul
            (hDelta k (Nat.lt_succ_self k)) hHigherLinear

private lemma p06_perturbed_product_expansion {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (u : ℝ) (omega : Omega) (k : ℕ) :
    p06PerturbedHouseholderProduct P DeltaP u omega k =
      p06HouseholderProduct P k +
        p06FirstOrderHouseholderProduct P DeltaP u omega k +
          p06HigherOrderHouseholderProduct P DeltaP u omega k := by
  induction k with
  | zero => simp [p06PerturbedHouseholderProduct, p06HouseholderProduct,
      p06FirstOrderHouseholderProduct, p06HigherOrderHouseholderProduct]
  | succ k ih =>
      simp only [p06PerturbedHouseholderProduct, p06HouseholderProduct,
        p06FirstOrderHouseholderProduct, p06HigherOrderHouseholderProduct, ih]
      noncomm_ring

private lemma p06_householder_sequence_symmetric {m : ℕ}
    (v : ℕ → Fin m → ℝ) (j : ℕ) :
    Matrix.transpose (p06HouseholderSequenceMatrix v j) =
      p06HouseholderSequenceMatrix v j := by
  ext i k
  simp only [Matrix.transpose_apply, p06HouseholderSequenceMatrix,
    p06HouseholderMatrix, p06FiniteId]
  rw [if_congr (eq_comm) rfl rfl]
  ring

private lemma p06_product_mul_transpose {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ) (k : ℕ)
    (hSymm : ∀ j, j < k → Matrix.transpose (P j) = P j)
    (hInv : ∀ j, j < k → P j * P j = 1) :
    p06HouseholderProduct P k *
        Matrix.transpose (p06HouseholderProduct P k) = 1 := by
  induction k with
  | zero => simp [p06HouseholderProduct]
  | succ k ih =>
      have ih' := ih
        (fun j hj ↦ hSymm j (Nat.lt_succ_of_lt hj))
        (fun j hj ↦ hInv j (Nat.lt_succ_of_lt hj))
      rw [p06HouseholderProduct, Matrix.transpose_mul]
      calc
        (P k * p06HouseholderProduct P k) *
              (Matrix.transpose (p06HouseholderProduct P k) *
                Matrix.transpose (P k)) =
            P k *
              (p06HouseholderProduct P k *
                Matrix.transpose (p06HouseholderProduct P k)) *
              Matrix.transpose (P k) := by noncomm_ring
        _ = P k * P k := by
          rw [ih', hSymm k (Nat.lt_succ_self k)]
          simp
        _ = 1 := hInv k (Nat.lt_succ_self k)

private lemma p06_first_order_factorization {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (u : ℝ) (omega : Omega) (k : ℕ)
    (hSymm : ∀ j, j < k → Matrix.transpose (P j) = P j)
    (hInv : ∀ j, j < k → P j * P j = 1) :
    p06HouseholderProduct P k *
        p06TransformedHouseholderInsertionSum P DeltaP u omega k =
      p06FirstOrderHouseholderProduct P DeltaP u omega k := by
  induction k with
  | zero =>
      simp [p06HouseholderProduct,
        p06TransformedHouseholderInsertionSum,
        p06FirstOrderHouseholderProduct]
  | succ k ih =>
      have hSymm' : ∀ j, j < k → Matrix.transpose (P j) = P j :=
        fun j hj ↦ hSymm j (Nat.lt_succ_of_lt hj)
      have hInv' : ∀ j, j < k → P j * P j = 1 :=
        fun j hj ↦ hInv j (Nat.lt_succ_of_lt hj)
      have ih' := ih hSymm' hInv'
      have horth := p06_product_mul_transpose P (k + 1) hSymm hInv
      rw [p06TransformedHouseholderInsertionSum, Finset.sum_range_succ]
      simp only [p06TransformedHouseholderInsertion,
        p06FirstOrderHouseholderProduct]
      calc
        p06HouseholderProduct P (k + 1) *
              (p06TransformedHouseholderInsertionSum P DeltaP u omega k +
                Matrix.transpose (p06HouseholderProduct P (k + 1)) *
                  DeltaP u k omega * p06HouseholderProduct P k) =
            P k *
                (p06HouseholderProduct P k *
                  p06TransformedHouseholderInsertionSum P DeltaP u omega k) +
              (p06HouseholderProduct P (k + 1) *
                Matrix.transpose (p06HouseholderProduct P (k + 1))) *
                  DeltaP u k omega * p06HouseholderProduct P k := by
            rw [p06HouseholderProduct]
            noncomm_ring
        _ = P k *
              p06FirstOrderHouseholderProduct P DeltaP u omega k +
                DeltaP u k omega * p06HouseholderProduct P k := by
            rw [ih', horth]
            simp

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
    fun u omega ↦
      p06HigherOrderHouseholderProduct
        P run.localPerturbation u omega r
  let factoredRemainder : ℝ → Omega → Matrix (Fin m) (Fin m) ℝ :=
    fun u omega ↦
      p06ApplicationQ run * unfactoredRemainder u omega
  have hUnfactoredOrder : ∀ omega, omega ∈ hlocal.localEvent →
      p06MatrixSecondOrderAtZero
        (fun u ↦ unfactoredRemainder u omega) := by
    intro omega homega
    exact p06_higher_order_bigO P run.localPerturbation omega r
      (hlocal.local_first_order omega homega)
  have hFactoredOrder : ∀ omega, omega ∈ hlocal.localEvent →
      p06MatrixSecondOrderAtZero
        (fun u ↦ factoredRemainder u omega) := by
    intro omega homega
    exact p06_matrix_bigO_const_mul (p06ApplicationQ run)
      (hUnfactoredOrder omega homega)
  have hUnfactoredIdentity : ∀ u omega,
      run.computed u omega =
        p06ApplicationExactState run +
          p06MatVec
            (p06ApplicationFirstOrderMatrix run u omega +
              unfactoredRemainder u omega)
            run.b := by
    intro u omega
    rw [run.computed_product]
    rw [p06_perturbed_product_expansion P run.localPerturbation u omega r]
    simp only [p06ApplicationExactState, p06ApplicationFirstOrderMatrix,
      P, unfactoredRemainder]
    funext i
    simp [p06MatVec, Finset.sum_add_distrib, add_mul]
    ring
  have hSymm : ∀ j, j < r → Matrix.transpose (P j) = P j := by
    intro j _hj
    exact p06_householder_sequence_symmetric run.householderVector j
  have hInv : ∀ j, j < r → P j * P j = 1 := by
    intro j hj
    exact run.householder_involutory j hj
  have hOrthogonalProduct :
      p06HouseholderProduct P r *
          Matrix.transpose (p06HouseholderProduct P r) = 1 :=
    p06_product_mul_transpose P r hSymm hInv
  have hFirstOrderFactorization : ∀ u omega,
      p06HouseholderProduct P r *
          p06TransformedHouseholderInsertionSum
            P run.localPerturbation u omega r =
        p06FirstOrderHouseholderProduct
          P run.localPerturbation u omega r := by
    intro u omega
    exact p06_first_order_factorization
      P run.localPerturbation u omega r hSymm hInv
  have hMatrixFactorization : ∀ u omega,
      p06ApplicationFirstOrderMatrix run u omega +
          unfactoredRemainder u omega =
        Matrix.transpose (p06ApplicationQ run) *
          (p06ApplicationFSum run u omega +
            factoredRemainder u omega) := by
    intro u omega
    simp only [p06ApplicationFirstOrderMatrix, p06ApplicationFSum,
      p06ApplicationQ, Matrix.transpose_transpose, factoredRemainder,
      unfactoredRemainder, P]
    rw [Matrix.mul_add, hFirstOrderFactorization u omega]
    rw [← Matrix.mul_assoc, hOrthogonalProduct, Matrix.one_mul]
  have hFactoredIdentity : ∀ u omega,
      run.computed u omega =
        p06ApplicationExactState run +
          p06MatVec
            (Matrix.transpose (p06ApplicationQ run) *
              (p06ApplicationFSum run u omega +
                factoredRemainder u omega))
            run.b := by
    intro u omega
    rw [hUnfactoredIdentity u omega, hMatrixFactorization u omega]
  refine ⟨unfactoredRemainder, factoredRemainder,
    hUnfactoredOrder, hFactoredOrder, hUnfactoredIdentity,
    hFactoredIdentity, ?_⟩
  intro u omega j
  rfl

end HighamBench
