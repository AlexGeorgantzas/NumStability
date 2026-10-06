import HighamBench.P06Definitions

namespace HighamBench

open scoped BigOperators

private lemma p06_matrix_bigO_add {m : ℕ}
    {A B : ℝ → Matrix (Fin m) (Fin m) ℝ} {f : ℝ → ℝ}
    (hA : p06MatrixFamilyIsBigOAtZero A f)
    (hB : p06MatrixFamilyIsBigOAtZero B f) :
    p06MatrixFamilyIsBigOAtZero (fun u ↦ A u + B u) f := by
  intro i j
  simpa only [Matrix.add_apply] using (hA i j).add (hB i j)

private lemma p06_matrix_bigO_const_mul_left {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ)
    {B : ℝ → Matrix (Fin m) (Fin m) ℝ} {f : ℝ → ℝ}
    (hB : p06MatrixFamilyIsBigOAtZero B f) :
    p06MatrixFamilyIsBigOAtZero (fun u ↦ A * B u) f := by
  intro i j
  simp only [Matrix.mul_apply]
  apply Asymptotics.IsBigO.sum
  intro k _hk
  exact (hB k j).const_mul_left (A i k)

private lemma p06_matrix_bigO_mul_const_right {m : ℕ}
    {A : ℝ → Matrix (Fin m) (Fin m) ℝ} (B : Matrix (Fin m) (Fin m) ℝ)
    {f : ℝ → ℝ} (hA : p06MatrixFamilyIsBigOAtZero A f) :
    p06MatrixFamilyIsBigOAtZero (fun u ↦ A u * B) f := by
  intro i j
  simp only [Matrix.mul_apply]
  apply Asymptotics.IsBigO.sum
  intro k _hk
  convert (hA i k).const_mul_left (B k j) using 1 <;> simp [mul_comm]

private lemma p06_matrix_bigO_mul {m : ℕ}
    {A B : ℝ → Matrix (Fin m) (Fin m) ℝ} {f g : ℝ → ℝ}
    (hA : p06MatrixFamilyIsBigOAtZero A f)
    (hB : p06MatrixFamilyIsBigOAtZero B g) :
    p06MatrixFamilyIsBigOAtZero
      (fun u ↦ A u * B u) (fun u ↦ f u * g u) := by
  intro i j
  simp only [Matrix.mul_apply]
  apply Asymptotics.IsBigO.sum
  intro k _hk
  exact (hA i k).mul (hB k j)

private lemma p06_matrix_bigO_trans {m : ℕ}
    {A : ℝ → Matrix (Fin m) (Fin m) ℝ} {f g : ℝ → ℝ}
    (hA : p06MatrixFamilyIsBigOAtZero A f)
    (hfg : f =O[nhds 0] g) :
    p06MatrixFamilyIsBigOAtZero A g := by
  intro i j
  exact (hA i j).trans hfg

private lemma p06_householderSequence_symmetric {m : ℕ}
    (v : ℕ → Fin m → ℝ) (j : ℕ) :
    Matrix.transpose (p06HouseholderSequenceMatrix v j) =
      p06HouseholderSequenceMatrix v j := by
  ext i k
  simp [p06HouseholderSequenceMatrix, p06HouseholderMatrix,
    p06FiniteId, eq_comm, mul_comm]

private lemma p06_householderProduct_mul_transpose_eq_one {m r : ℕ}
    (v : ℕ → Fin m → ℝ)
    (hinv : ∀ j, j < r →
      p06HouseholderSequenceMatrix v j *
        p06HouseholderSequenceMatrix v j = 1) :
    ∀ n, n ≤ r →
      p06HouseholderProduct (p06HouseholderSequenceMatrix v) n *
        Matrix.transpose
          (p06HouseholderProduct (p06HouseholderSequenceMatrix v) n) = 1 := by
  intro n hn
  induction n with
  | zero => simp [p06HouseholderProduct]
  | succ n ih =>
      have hnlt : n < r := lt_of_lt_of_le (Nat.lt_succ_self n) hn
      have ih' := ih (Nat.le_of_lt hnlt)
      rw [p06HouseholderProduct, Matrix.transpose_mul,
        p06_householderSequence_symmetric]
      calc
        (p06HouseholderSequenceMatrix v n *
              p06HouseholderProduct (p06HouseholderSequenceMatrix v) n) *
            (Matrix.transpose
                (p06HouseholderProduct (p06HouseholderSequenceMatrix v) n) *
              p06HouseholderSequenceMatrix v n) =
            p06HouseholderSequenceMatrix v n *
              (p06HouseholderProduct (p06HouseholderSequenceMatrix v) n *
                Matrix.transpose
                  (p06HouseholderProduct (p06HouseholderSequenceMatrix v) n)) *
              p06HouseholderSequenceMatrix v n := by noncomm_ring
        _ = p06HouseholderSequenceMatrix v n *
              p06HouseholderSequenceMatrix v n := by rw [ih']; simp
        _ = 1 := hinv n hnlt

private lemma p06_product_mul_insertionSum_eq_first
    {Omega : Type*} {m r : ℕ}
    (v : ℕ → Fin m → ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (hinv : ∀ j, j < r →
      p06HouseholderSequenceMatrix v j *
        p06HouseholderSequenceMatrix v j = 1) :
    ∀ n, n ≤ r → ∀ u omega,
      p06HouseholderProduct (p06HouseholderSequenceMatrix v) n *
          p06TransformedHouseholderInsertionSum
            (p06HouseholderSequenceMatrix v) DeltaP u omega n =
        p06FirstOrderHouseholderProduct
          (p06HouseholderSequenceMatrix v) DeltaP u omega n := by
  intro n hn
  induction n with
  | zero =>
      intro u omega
      simp [p06HouseholderProduct, p06TransformedHouseholderInsertionSum,
        p06FirstOrderHouseholderProduct]
  | succ n ih =>
      intro u omega
      have hnlt : n < r := lt_of_lt_of_le (Nat.lt_succ_self n) hn
      have ih' := ih (Nat.le_of_lt hnlt) u omega
      have horth := p06_householderProduct_mul_transpose_eq_one v hinv
        (n + 1) hn
      have horth' :
          (p06HouseholderSequenceMatrix v n *
              p06HouseholderProduct (p06HouseholderSequenceMatrix v) n) *
            Matrix.transpose
              (p06HouseholderSequenceMatrix v n *
                p06HouseholderProduct (p06HouseholderSequenceMatrix v) n) = 1 := by
        simpa only [p06HouseholderProduct] using horth
      rw [p06HouseholderProduct, p06FirstOrderHouseholderProduct,
        p06TransformedHouseholderInsertionSum, Finset.sum_range_succ,
        p06TransformedHouseholderInsertion]
      calc
        (p06HouseholderSequenceMatrix v n *
              p06HouseholderProduct (p06HouseholderSequenceMatrix v) n) *
            (p06TransformedHouseholderInsertionSum
                (p06HouseholderSequenceMatrix v) DeltaP u omega n +
              Matrix.transpose
                  (p06HouseholderSequenceMatrix v n *
                    p06HouseholderProduct (p06HouseholderSequenceMatrix v) n) *
                DeltaP u n omega *
                  p06HouseholderProduct (p06HouseholderSequenceMatrix v) n) =
            p06HouseholderSequenceMatrix v n *
              (p06HouseholderProduct (p06HouseholderSequenceMatrix v) n *
                p06TransformedHouseholderInsertionSum
                  (p06HouseholderSequenceMatrix v) DeltaP u omega n) +
              ((p06HouseholderSequenceMatrix v n *
                    p06HouseholderProduct (p06HouseholderSequenceMatrix v) n) *
                Matrix.transpose
                  (p06HouseholderSequenceMatrix v n *
                    p06HouseholderProduct (p06HouseholderSequenceMatrix v) n)) *
                DeltaP u n omega *
                  p06HouseholderProduct (p06HouseholderSequenceMatrix v) n := by
            noncomm_ring
        _ = p06HouseholderSequenceMatrix v n *
              p06FirstOrderHouseholderProduct
                (p06HouseholderSequenceMatrix v) DeltaP u omega n +
              1 * DeltaP u n omega *
                p06HouseholderProduct (p06HouseholderSequenceMatrix v) n := by
            rw [ih', horth']
        _ = p06HouseholderSequenceMatrix v n *
              p06FirstOrderHouseholderProduct
                (p06HouseholderSequenceMatrix v) DeltaP u omega n +
              DeltaP u n omega *
                p06HouseholderProduct (p06HouseholderSequenceMatrix v) n := by
            simp

private lemma p06_perturbed_eq_exact_add_first_add_higher
    {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (u : ℝ) (omega : Omega) (n : ℕ) :
    p06PerturbedHouseholderProduct P DeltaP u omega n =
      p06HouseholderProduct P n +
        p06FirstOrderHouseholderProduct P DeltaP u omega n +
          p06HigherOrderHouseholderProduct P DeltaP u omega n := by
  induction n with
  | zero =>
      simp [p06PerturbedHouseholderProduct, p06HouseholderProduct,
        p06FirstOrderHouseholderProduct, p06HigherOrderHouseholderProduct]
  | succ n ih =>
      rw [p06PerturbedHouseholderProduct, p06HouseholderProduct,
        p06FirstOrderHouseholderProduct, p06HigherOrderHouseholderProduct, ih]
      noncomm_ring

private lemma p06_first_and_higher_bigO
    {Omega : Type*} {m r : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (omega : Omega)
    (hDelta : ∀ j, j < r →
      p06MatrixFamilyIsBigOAtZero (fun u ↦ DeltaP u j omega) (fun u ↦ u)) :
    ∀ n, n ≤ r →
      p06MatrixFamilyIsBigOAtZero
          (fun u ↦ p06FirstOrderHouseholderProduct P DeltaP u omega n)
          (fun u ↦ u) ∧
        p06MatrixFamilyIsBigOAtZero
          (fun u ↦ p06HigherOrderHouseholderProduct P DeltaP u omega n)
          (fun u ↦ u ^ 2) := by
  intro n hn
  induction n with
  | zero =>
      constructor <;> intro i j
      · simpa [p06FirstOrderHouseholderProduct] using
          (Asymptotics.isBigO_zero (fun u : ℝ ↦ u) (nhds 0))
      · simpa [p06HigherOrderHouseholderProduct] using
          (Asymptotics.isBigO_zero (fun u : ℝ ↦ u ^ 2) (nhds 0))
  | succ n ih =>
      have hnlt : n < r := lt_of_lt_of_le (Nat.lt_succ_self n) hn
      have ihn := ih (Nat.le_of_lt hnlt)
      have hDeltaN := hDelta n hnlt
      constructor
      · simpa only [p06FirstOrderHouseholderProduct] using
          p06_matrix_bigO_add
            (p06_matrix_bigO_const_mul_left (P n) ihn.1)
            (p06_matrix_bigO_mul_const_right (p06HouseholderProduct P n) hDeltaN)
      · have hlinearQuadratic := p06_matrix_bigO_mul hDeltaN ihn.2
        have hscale :
            (fun u : ℝ ↦ u * u ^ 2) =O[nhds 0] (fun u : ℝ ↦ u ^ 2) := by
          convert (Asymptotics.isLittleO_pow_pow
            (show (2 : ℕ) < 3 by omega) :
              (fun u : ℝ ↦ u ^ 3) =o[nhds 0] (fun u : ℝ ↦ u ^ 2)).isBigO using 1
          funext u
          ring
        have hlast := p06_matrix_bigO_trans hlinearQuadratic hscale
        simpa only [p06HigherOrderHouseholderProduct] using
          p06_matrix_bigO_add
            (p06_matrix_bigO_add
              (p06_matrix_bigO_const_mul_left (P n) ihn.2)
              (by
                convert p06_matrix_bigO_mul hDeltaN ihn.1 using 1 <;>
                  simp [pow_two]))
            hlast

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
  let higher : ℝ → Omega → Matrix (Fin m) (Fin m) ℝ :=
    fun u omega ↦
      p06HigherOrderHouseholderProduct
        (p06HouseholderSequenceMatrix run.householderVector)
        run.localPerturbation u omega r
  let factored : ℝ → Omega → Matrix (Fin m) (Fin m) ℝ :=
    fun u omega ↦ p06ApplicationQ run * higher u omega
  refine ⟨higher, factored, ?_, ?_, ?_, ?_, ?_⟩
  · intro omega homega
    dsimp only [higher]
    exact (p06_first_and_higher_bigO
      (p06HouseholderSequenceMatrix run.householderVector)
      run.localPerturbation omega
      (hlocal.local_first_order omega homega) r (le_refl r)).2
  · intro omega homega
    dsimp only [factored]
    apply p06_matrix_bigO_const_mul_left
    dsimp only [higher]
    exact (p06_first_and_higher_bigO
      (p06HouseholderSequenceMatrix run.householderVector)
      run.localPerturbation omega
      (hlocal.local_first_order omega homega) r (le_refl r)).2
  · intro u omega
    rw [run.computed_product,
      p06_perturbed_eq_exact_add_first_add_higher]
    ext i
    simp [p06ApplicationExactState, p06ApplicationFirstOrderMatrix,
      higher, p06MatVec, add_mul, Finset.sum_add_distrib, add_assoc]
  · intro u omega
    have hfirst := p06_product_mul_insertionSum_eq_first
      run.householderVector run.localPerturbation
      run.householder_involutory r (le_refl r) u omega
    have horth := p06_householderProduct_mul_transpose_eq_one
      run.householderVector run.householder_involutory r (le_refl r)
    have hfactor :
        Matrix.transpose (p06ApplicationQ run) *
            (p06ApplicationFSum run u omega + factored u omega) =
          p06ApplicationFirstOrderMatrix run u omega + higher u omega := by
      dsimp only [p06ApplicationQ, p06ApplicationFSum,
        p06ApplicationFirstOrderMatrix, factored]
      rw [Matrix.transpose_transpose]
      calc
        p06HouseholderProduct
              (p06HouseholderSequenceMatrix run.householderVector) r *
            (p06TransformedHouseholderInsertionSum
                (p06HouseholderSequenceMatrix run.householderVector)
                run.localPerturbation u omega r +
              Matrix.transpose
                  (p06HouseholderProduct
                    (p06HouseholderSequenceMatrix run.householderVector) r) *
                higher u omega) =
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
                higher u omega := by noncomm_ring
        _ = p06FirstOrderHouseholderProduct
                (p06HouseholderSequenceMatrix run.householderVector)
                run.localPerturbation u omega r +
              1 * higher u omega := by rw [hfirst, horth]
        _ = p06FirstOrderHouseholderProduct
                (p06HouseholderSequenceMatrix run.householderVector)
                run.localPerturbation u omega r +
              higher u omega := by simp
    rw [run.computed_product,
      p06_perturbed_eq_exact_add_first_add_higher]
    rw [hfactor]
    ext i
    simp [p06ApplicationExactState, p06ApplicationFirstOrderMatrix,
      higher, p06MatVec, add_mul, Finset.sum_add_distrib, add_assoc]
  · intro u omega j
    rfl

end HighamBench
