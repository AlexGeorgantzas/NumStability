import HighamBench.P06Definitions

namespace HighamBench

open scoped BigOperators
open Asymptotics

private lemma p06_t3_matVec_add {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) :
    p06MatVec (A + B) x = p06MatVec A x + p06MatVec B x := by
  funext i
  simp only [p06MatVec, Matrix.add_apply, add_mul, Finset.sum_add_distrib,
    Pi.add_apply]

private lemma p06_t3_matrix_bigO_zero {m : ℕ} (g : ℝ → ℝ) :
    p06MatrixFamilyIsBigOAtZero
      (fun _ : ℝ ↦ (0 : Matrix (Fin m) (Fin m) ℝ)) g := by
  intro i j
  simpa using (isBigO_zero g (nhds 0))

private lemma p06_t3_matrix_bigO_add {m : ℕ}
    {A B : ℝ → Matrix (Fin m) (Fin m) ℝ} {g : ℝ → ℝ}
    (hA : p06MatrixFamilyIsBigOAtZero A g)
    (hB : p06MatrixFamilyIsBigOAtZero B g) :
    p06MatrixFamilyIsBigOAtZero (fun u ↦ A u + B u) g := by
  intro i j
  simpa only [Matrix.add_apply] using (hA i j).add (hB i j)

private lemma p06_t3_matrix_bigO_mul {m : ℕ}
    {A B : ℝ → Matrix (Fin m) (Fin m) ℝ} {f g : ℝ → ℝ}
    (hA : p06MatrixFamilyIsBigOAtZero A f)
    (hB : p06MatrixFamilyIsBigOAtZero B g) :
    p06MatrixFamilyIsBigOAtZero
      (fun u ↦ A u * B u) (fun u ↦ f u * g u) := by
  intro i j
  simp only [Matrix.mul_apply]
  apply IsBigO.sum
  intro k _hk
  exact (hA i k).mul (hB k j)

private lemma p06_t3_matrix_bigO_const_mul {m : ℕ}
    (C : Matrix (Fin m) (Fin m) ℝ)
    {A : ℝ → Matrix (Fin m) (Fin m) ℝ} {g : ℝ → ℝ}
    (hA : p06MatrixFamilyIsBigOAtZero A g) :
    p06MatrixFamilyIsBigOAtZero (fun u ↦ C * A u) g := by
  intro i j
  simp only [Matrix.mul_apply]
  apply IsBigO.sum
  intro k _hk
  exact (hA k j).const_mul_left (C i k)

private lemma p06_t3_matrix_bigO_mul_const {m : ℕ}
    {A : ℝ → Matrix (Fin m) (Fin m) ℝ}
    (C : Matrix (Fin m) (Fin m) ℝ) {g : ℝ → ℝ}
    (hA : p06MatrixFamilyIsBigOAtZero A g) :
    p06MatrixFamilyIsBigOAtZero (fun u ↦ A u * C) g := by
  intro i j
  simp only [Matrix.mul_apply]
  apply IsBigO.sum
  intro k _hk
  simpa only [mul_comm] using (hA i k).const_mul_left (C k j)

private lemma p06_t3_perturbed_expansion {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (u : ℝ) (omega : Omega) : ∀ k,
    p06PerturbedHouseholderProduct P DeltaP u omega k =
      p06HouseholderProduct P k +
        p06FirstOrderHouseholderProduct P DeltaP u omega k +
          p06HigherOrderHouseholderProduct P DeltaP u omega k := by
  intro k
  induction k with
  | zero =>
      simp [p06PerturbedHouseholderProduct, p06HouseholderProduct,
        p06FirstOrderHouseholderProduct, p06HigherOrderHouseholderProduct]
  | succ k ih =>
      simp only [p06PerturbedHouseholderProduct, p06HouseholderProduct,
        p06FirstOrderHouseholderProduct, p06HigherOrderHouseholderProduct]
      rw [ih]
      noncomm_ring

private lemma p06_t3_first_order_bigO {Omega : Type*} {m r : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (omega : Omega)
    (hDelta : ∀ j, j < r →
      p06MatrixFamilyIsBigOAtZero (fun u ↦ DeltaP u j omega) (fun u ↦ u)) :
    ∀ k, k ≤ r →
      p06MatrixFamilyIsBigOAtZero
        (fun u ↦ p06FirstOrderHouseholderProduct P DeltaP u omega k)
        (fun u ↦ u) := by
  intro k hk
  induction k with
  | zero =>
      simpa only [p06FirstOrderHouseholderProduct] using
        (p06_t3_matrix_bigO_zero (m := m) (fun u : ℝ ↦ u))
  | succ k ih =>
      have hkr : k < r := lt_of_lt_of_le (Nat.lt_succ_self k) hk
      have ih' := ih (Nat.le_trans (Nat.le_succ k) hk)
      simpa only [p06FirstOrderHouseholderProduct] using
        p06_t3_matrix_bigO_add
          (p06_t3_matrix_bigO_const_mul (P k) ih')
          (p06_t3_matrix_bigO_mul_const
            (p06HouseholderProduct P k) (hDelta k hkr))

private lemma p06_t3_higher_order_bigO {Omega : Type*} {m r : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (omega : Omega)
    (hDelta : ∀ j, j < r →
      p06MatrixFamilyIsBigOAtZero (fun u ↦ DeltaP u j omega) (fun u ↦ u)) :
    ∀ k, k ≤ r →
      p06MatrixSecondOrderAtZero
        (fun u ↦ p06HigherOrderHouseholderProduct P DeltaP u omega k) := by
  have hid_one : (fun u : ℝ ↦ u) =O[nhds 0] (fun _ : ℝ ↦ (1 : ℝ)) :=
    isLittleO_id_one.isBigO
  intro k hk
  induction k with
  | zero =>
      simpa only [p06HigherOrderHouseholderProduct, p06MatrixSecondOrderAtZero] using
        (p06_t3_matrix_bigO_zero (m := m) (fun u : ℝ ↦ u ^ 2))
  | succ k ih =>
      have hkr : k < r := lt_of_lt_of_le (Nat.lt_succ_self k) hk
      have ih' := ih (Nat.le_trans (Nat.le_succ k) hk)
      have hfirst := p06_t3_first_order_bigO P DeltaP omega hDelta k
        (Nat.le_trans (Nat.le_succ k) hk)
      have hquadratic :
          p06MatrixFamilyIsBigOAtZero
            (fun u ↦ DeltaP u k omega *
              p06FirstOrderHouseholderProduct P DeltaP u omega k)
            (fun u ↦ u ^ 2) := by
        have hmul := p06_t3_matrix_bigO_mul (hDelta k hkr) hfirst
        simpa only [pow_two] using hmul
      have hDeltaOne :
          p06MatrixFamilyIsBigOAtZero
            (fun u ↦ DeltaP u k omega) (fun _ : ℝ ↦ (1 : ℝ)) := by
        intro i j
        exact (hDelta k hkr i j).trans hid_one
      have hcubic :
          p06MatrixFamilyIsBigOAtZero
            (fun u ↦ DeltaP u k omega *
              p06HigherOrderHouseholderProduct P DeltaP u omega k)
            (fun u ↦ u ^ 2) := by
        have hmul := p06_t3_matrix_bigO_mul hDeltaOne ih'
        simpa only [one_mul] using hmul
      simpa only [p06HigherOrderHouseholderProduct,
        p06MatrixSecondOrderAtZero] using
        p06_t3_matrix_bigO_add
          (p06_t3_matrix_bigO_add
            (p06_t3_matrix_bigO_const_mul (P k) ih') hquadratic)
          hcubic

private lemma p06_t3_householder_symmetric {m : ℕ} (v : Fin m → ℝ) :
    Matrix.transpose (p06HouseholderMatrix v) = p06HouseholderMatrix v := by
  ext i j
  simp only [Matrix.transpose_apply, p06HouseholderMatrix, p06FiniteId]
  by_cases h : i = j
  · subst j
    simp
  · have h' : j ≠ i := by simpa only [ne_eq, eq_comm] using h
    simp [h, h', mul_comm]

private lemma p06_t3_product_mul_transpose {m r : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (hSymm : ∀ j, Matrix.transpose (P j) = P j)
    (hInv : ∀ j, j < r → P j * P j = 1) :
    ∀ k, k ≤ r →
      p06HouseholderProduct P k *
        Matrix.transpose (p06HouseholderProduct P k) = 1 := by
  intro k hk
  induction k with
  | zero => simp [p06HouseholderProduct]
  | succ k ih =>
      have hkr : k < r := lt_of_lt_of_le (Nat.lt_succ_self k) hk
      have ih' := ih (Nat.le_trans (Nat.le_succ k) hk)
      simp only [p06HouseholderProduct, Matrix.transpose_mul, hSymm k]
      calc
        (P k * p06HouseholderProduct P k) *
              (Matrix.transpose (p06HouseholderProduct P k) * P k) =
            P k * (p06HouseholderProduct P k *
              Matrix.transpose (p06HouseholderProduct P k)) * P k := by
                noncomm_ring
        _ = P k * P k := by rw [ih']; simp
        _ = 1 := hInv k hkr

private lemma p06_t3_first_order_factorization {Omega : Type*} {m r : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (hSymm : ∀ j, Matrix.transpose (P j) = P j)
    (hInv : ∀ j, j < r → P j * P j = 1)
    (u : ℝ) (omega : Omega) : ∀ k, k ≤ r →
    p06HouseholderProduct P k *
        p06TransformedHouseholderInsertionSum P DeltaP u omega k =
      p06FirstOrderHouseholderProduct P DeltaP u omega k := by
  intro k hk
  induction k with
  | zero =>
      simp [p06HouseholderProduct, p06TransformedHouseholderInsertionSum,
        p06FirstOrderHouseholderProduct]
  | succ k ih =>
      have hk' : k ≤ r := Nat.le_trans (Nat.le_succ k) hk
      have ih' := ih hk'
      have horth := p06_t3_product_mul_transpose P hSymm hInv (k + 1) hk
      have hprod : p06HouseholderProduct P (k + 1) =
          P k * p06HouseholderProduct P k := rfl
      have hsum :
          p06TransformedHouseholderInsertionSum P DeltaP u omega (k + 1) =
            p06TransformedHouseholderInsertionSum P DeltaP u omega k +
              p06TransformedHouseholderInsertion P DeltaP u omega k := by
        simp only [p06TransformedHouseholderInsertionSum, Finset.sum_range_succ]
      have hins : p06TransformedHouseholderInsertion P DeltaP u omega k =
          Matrix.transpose (p06HouseholderProduct P (k + 1)) *
            DeltaP u k omega * p06HouseholderProduct P k := rfl
      have hleft :
          p06HouseholderProduct P (k + 1) *
              p06TransformedHouseholderInsertionSum P DeltaP u omega k =
            P k * (p06HouseholderProduct P k *
              p06TransformedHouseholderInsertionSum P DeltaP u omega k) := by
        rw [hprod, Matrix.mul_assoc]
      have hright :
          p06HouseholderProduct P (k + 1) *
              (Matrix.transpose (p06HouseholderProduct P (k + 1)) *
                DeltaP u k omega * p06HouseholderProduct P k) =
            (p06HouseholderProduct P (k + 1) *
                Matrix.transpose (p06HouseholderProduct P (k + 1))) *
              DeltaP u k omega * p06HouseholderProduct P k := by
        noncomm_ring
      rw [hsum, Matrix.mul_add, hins, hleft, hright, ih', horth]
      simp only [Matrix.one_mul]
      rfl

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
    fun u omega ↦ p06HigherOrderHouseholderProduct
      P run.localPerturbation u omega r
  let factoredRemainder : ℝ → Omega → Matrix (Fin m) (Fin m) ℝ :=
    fun u omega ↦ p06ApplicationQ run * unfactoredRemainder u omega
  have hSymm : ∀ j, Matrix.transpose (P j) = P j := by
    intro j
    exact p06_t3_householder_symmetric (run.householderVector j)
  have hInv : ∀ j, j < r → P j * P j = 1 := by
    intro j hj
    exact run.householder_involutory j hj
  refine ⟨unfactoredRemainder, factoredRemainder, ?_, ?_, ?_, ?_, ?_⟩
  · intro omega homega
    exact p06_t3_higher_order_bigO P run.localPerturbation omega
      (hlocal.local_first_order omega homega) r le_rfl
  · intro omega homega
    apply p06_t3_matrix_bigO_const_mul (p06ApplicationQ run)
    exact p06_t3_higher_order_bigO P run.localPerturbation omega
      (hlocal.local_first_order omega homega) r le_rfl
  · intro u omega
    rw [run.computed_product]
    have hexpand := p06_t3_perturbed_expansion
      P run.localPerturbation u omega r
    change p06MatVec
        (p06PerturbedHouseholderProduct P run.localPerturbation u omega r) run.b =
      p06MatVec (p06HouseholderProduct P r) run.b +
        p06MatVec
          (p06FirstOrderHouseholderProduct P run.localPerturbation u omega r +
            unfactoredRemainder u omega) run.b
    rw [hexpand, p06_t3_matVec_add, p06_t3_matVec_add,
      p06_t3_matVec_add]
    dsimp only [unfactoredRemainder]
    abel
  · intro u omega
    have hunfactored :
        run.computed u omega =
          p06ApplicationExactState run +
            p06MatVec
              (p06ApplicationFirstOrderMatrix run u omega +
                unfactoredRemainder u omega) run.b := by
      rw [run.computed_product]
      have hexpand := p06_t3_perturbed_expansion
        P run.localPerturbation u omega r
      change p06MatVec
          (p06PerturbedHouseholderProduct P run.localPerturbation u omega r) run.b =
        p06MatVec (p06HouseholderProduct P r) run.b +
          p06MatVec
            (p06FirstOrderHouseholderProduct P run.localPerturbation u omega r +
              unfactoredRemainder u omega) run.b
      rw [hexpand, p06_t3_matVec_add, p06_t3_matVec_add,
        p06_t3_matVec_add]
      dsimp only [unfactoredRemainder]
      abel
    rw [hunfactored]
    congr 2
    have hfirst := p06_t3_first_order_factorization
      P run.localPerturbation hSymm hInv u omega r le_rfl
    have horth := p06_t3_product_mul_transpose P hSymm hInv r le_rfl
    change
      p06FirstOrderHouseholderProduct P run.localPerturbation u omega r +
          unfactoredRemainder u omega =
        p06HouseholderProduct P r *
          (p06TransformedHouseholderInsertionSum
              P run.localPerturbation u omega r +
            Matrix.transpose (p06HouseholderProduct P r) *
              unfactoredRemainder u omega)
    rw [Matrix.mul_add, hfirst, ← Matrix.mul_assoc, horth, Matrix.one_mul]
  · intro u omega j
    rfl

end HighamBench
