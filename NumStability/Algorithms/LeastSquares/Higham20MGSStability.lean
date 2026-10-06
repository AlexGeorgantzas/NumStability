import NumStability.Algorithms.HighamChapter8
import NumStability.Algorithms.LeastSquares.LSQRSolve
import NumStability.Algorithms.QR.Higham19
import NumStability.Algorithms.QR.Higham19Alg12MGSRounded
import NumStability.Algorithms.QR.Higham19Alg12MGSRepair

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

noncomputable section

namespace Problem20_5

/-!
# Higham, Chapter 20, Problem 20.5: MGS least-squares stability

The Appendix A proof applies the Chapter 19 MGS theorem to the augmented
matrix `[A b]`, selects its orthonormal repair `[W₁ w]`, and folds the
back-substitution perturbation `Delta R` into the matrix perturbation as
`W₁ Delta R`.  This file proves that complete Chapter 20 transfer.

The first transfer theorem below accepts the public `MGSQRBounds` result of
Theorem 19.13, and a weaker reusable transfer accepts
`ModifiedGramSchmidtGlobalRepair`.  The later
`actualAugmentedMGSBackSub_end_to_end_accumulatedPolar` and `_localGram`
theorems instantiate that weaker repair for the literal rounded MGS loop.  The
padded-Householder route remains relevant only to the stronger printed
condition-number-independent `c3 * u` coefficient.
-/

/-- The source augmented matrix `[A b]`, with `b` as the final column. -/
def augmentedInput {m n : Nat}
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real) :
    Fin m -> Fin (n + 1) -> Real :=
  fun i => Fin.lastCases (b i) (fun j => A i j)

/-- The computed `Q-hat` obtained by running the literal rounded Algorithm
19.12 loop on the actual augmented matrix `[A b]`. -/
def actualAugmentedMGSQ {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real) :
    Fin m -> Fin (n + 1) -> Real :=
  fl_modifiedGramSchmidtQ fp (augmentedInput A b)

/-- The computed `R-hat` obtained by running the literal rounded Algorithm
19.12 loop on the actual augmented matrix `[A b]`. -/
def actualAugmentedMGSR {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real) :
    Fin (n + 1) -> Fin (n + 1) -> Real :=
  fl_modifiedGramSchmidtR fp (augmentedInput A b)

/-- The actual augmented MGS factors satisfy every local floating-point field
of Algorithm 19.12.  This is the implementation-backed `[A b]` handoff used by
the accumulated-polar and computed-Gram repair producers later in this file.
The stronger printed `c3 * u` compression remains a separate Chapter 19
QR-sensitivity result. -/
theorem actualAugmentedMGS_roundedState {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (hm : gammaValid fp (2 * (m + 1)))
    (hpivot : forall k : Fin (n + 1), actualAugmentedMGSR fp A b k k ≠ 0) :
    ModifiedGramSchmidtRoundedState fp (augmentedInput A b)
      (actualAugmentedMGSQ fp A b) (actualAugmentedMGSR fp A b)
      (flMGSVectors fp (augmentedInput A b)) := by
  exact fl_modifiedGramSchmidt_roundedState fp (augmentedInput A b) hm hpivot

/-- The first `n` columns of an `(n+1)`-column economy factor. -/
def leadingQ {m n : Nat} (Q : Fin m -> Fin (n + 1) -> Real) :
    Fin m -> Fin n -> Real :=
  fun i j => Q i j.castSucc

/-- The final column of an `(n+1)`-column economy factor. -/
def lastQ {m n : Nat} (Q : Fin m -> Fin (n + 1) -> Real) : Fin m -> Real :=
  fun i => Q i (Fin.last n)

/-- The leading `n`-by-`n` block of the augmented triangular factor. -/
def leadingR {n : Nat} (R : Fin (n + 1) -> Fin (n + 1) -> Real) :
    Fin n -> Fin n -> Real :=
  fun i j => R i.castSucc j.castSucc

/-- The first `n` entries of the last column of the augmented triangular factor. -/
def lastColumnTop {n : Nat}
    (R : Fin (n + 1) -> Fin (n + 1) -> Real) : Fin n -> Real :=
  fun i => R i.castSucc (Fin.last n)

/-- The bottom-right entry of the augmented triangular factor. -/
def lastDiagonal {n : Nat}
    (R : Fin (n + 1) -> Fin (n + 1) -> Real) : Real :=
  R (Fin.last n) (Fin.last n)

/-- The concrete Chapter 20 Problem 20.5 output: run literal rounded MGS on
`[A b]`, then run the repository's literal rounded back substitution on the
leading block and final-column top of its computed `R-hat`. -/
def actualAugmentedMGSBackSub {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real) : Fin n -> Real :=
  fl_backSub fp n (leadingR (actualAugmentedMGSR fp A b))
    (lastColumnTop (actualAugmentedMGSR fp A b))

/-- Restrict an augmented perturbation to the source matrix columns. -/
def matrixPerturbation {m n : Nat}
    (Delta : Fin m -> Fin (n + 1) -> Real) : Fin m -> Fin n -> Real :=
  fun i j => Delta i j.castSucc

/-- Restrict an augmented perturbation to its right-hand-side column. -/
def rhsPerturbation {m n : Nat}
    (Delta : Fin m -> Fin (n + 1) -> Real) : Fin m -> Real :=
  fun i => Delta i (Fin.last n)

/-- Fold a triangular-solve perturbation into the repaired matrix factor. -/
def foldedMatrixPerturbation {m n : Nat}
    (Q : Fin m -> Fin n -> Real)
    (DeltaA : Fin m -> Fin n -> Real)
    (DeltaR : Fin n -> Fin n -> Real) : Fin m -> Fin n -> Real :=
  fun i j => DeltaA i j + matMulRect m n n Q DeltaR i j

/-- The exact coefficient in the Appendix A columnwise matrix bound after
combining the Theorem 19.13 perturbation `eta` with back substitution. -/
def matrixCoeff (fp : FPModel) (n : Nat) (eta : Real) : Real :=
  eta + gamma fp n * (1 + eta)

/-- The common Theorem 20.3-style coefficient covering both matrix and RHS
perturbations. -/
def commonCoeff (fp : FPModel) (n : Nat) (eta : Real) : Real :=
  max (matrixCoeff fp n eta) eta

/-- Splitting the orthonormal repaired factorization of `[A b]` gives the
exact augmented least-squares factorization used in Section 20.3. -/
theorem augmented_factorization_of_repaired_factor
    {m n : Nat}
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (Q : Fin m -> Fin (n + 1) -> Real)
    (R : Fin (n + 1) -> Fin (n + 1) -> Real)
    (Delta : Fin m -> Fin (n + 1) -> Real)
    (hQ : GramSchmidtOrthonormalColumns Q)
    (hfactor : forall i j,
      augmentedInput A b i j + Delta i j =
        matMulRect m (n + 1) (n + 1) Q R i j)
    (hupper : IsUpperTrapezoidal (n + 1) (n + 1) R) :
    MGSAugmentedLSFactorization
      (fun i j => A i j + matrixPerturbation Delta i j)
      (fun i => b i + rhsPerturbation Delta i)
      (leadingQ Q) (lastQ Q) (leadingR R) (lastColumnTop R)
      (lastDiagonal R) := by
  constructor
  . intro i j
    have h := hfactor i j.castSucc
    unfold matMulRect at h
    rw [Fin.sum_univ_castSucc] at h
    have hzero : R (Fin.last n) j.castSucc = 0 := by
      apply hupper
      simp
    simpa [augmentedInput, matrixPerturbation, leadingQ, leadingR,
      matMulRect, hzero] using h
  . intro i
    have h := hfactor i (Fin.last n)
    unfold matMulRect at h
    rw [Fin.sum_univ_castSucc] at h
    calc
      b i + rhsPerturbation Delta i =
          (∑ k : Fin n, leadingQ Q i k * lastColumnTop R k) +
            lastQ Q i * lastDiagonal R := by
              simpa [augmentedInput, rhsPerturbation, leadingQ, lastQ,
                lastColumnTop, lastDiagonal] using h
      _ = (∑ k : Fin n, leadingQ Q i k * lastColumnTop R k) +
            lastDiagonal R * lastQ Q i := by ring
  . intro j k
    have h := hQ j.castSucc k.castSucc
    simpa [GramSchmidtOrthonormalColumns, rectangularGram, leadingQ,
      idMatrix] using h
  . intro j
    have h := hQ j.castSucc (Fin.last n)
    simpa [GramSchmidtOrthonormalColumns, rectangularGram, leadingQ, lastQ,
      idMatrix] using h
  . have h := hQ (Fin.last n) (Fin.last n)
    simpa [GramSchmidtOrthonormalColumns, rectangularGram, lastQ,
      vecNorm2Sq, idMatrix, pow_two] using h

/-- Folding `DeltaR` into the leading repaired factor preserves the exact
augmented factorization. -/
theorem folded_augmented_factorization
    {m n : Nat}
    {A : Fin m -> Fin n -> Real} {b : Fin m -> Real}
    {Q1 : Fin m -> Fin n -> Real} {q : Fin m -> Real}
    {R DeltaR : Fin n -> Fin n -> Real} {z : Fin n -> Real} {rho : Real}
    (h : MGSAugmentedLSFactorization A b Q1 q R z rho) :
    MGSAugmentedLSFactorization
      (fun i j => A i j + matMulRect m n n Q1 DeltaR i j)
      b Q1 q (fun i j => R i j + DeltaR i j) z rho := by
  constructor
  . intro i j
    have hadd := congrFun (congrFun
      (matMulRect_add_right m n n Q1 R DeltaR) i) j
    calc
      A i j + matMulRect m n n Q1 DeltaR i j =
          matMulRect m n n Q1 R i j +
            matMulRect m n n Q1 DeltaR i j := by
              change A i j + matMulRect m n n Q1 DeltaR i j =
                (∑ k : Fin n, Q1 i k * R k j) +
                  matMulRect m n n Q1 DeltaR i j
              rw [h.A_eq i j]
      _ = matMulRect m n n Q1 (fun a b => R a b + DeltaR a b) i j :=
        hadd.symm
  . exact h.b_eq
  . exact h.Q1_col_orthonormal
  . exact h.q_orthogonal
  . exact h.q_norm

/-- An economy matrix with orthonormal columns preserves Euclidean norm. -/
theorem orthonormal_columns_action_norm_eq {m n : Nat}
    (Q : Fin m -> Fin n -> Real) (hQ : GramSchmidtOrthonormalColumns Q)
    (x : Fin n -> Real) :
    vecNorm2 (rectMatMulVec Q x) = vecNorm2 x := by
  have hforward := hQ.rectOpNorm2Le_one x
  have hQT : rectOpNorm2Le (finiteTranspose Q) 1 :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le Q (by norm_num)
      hQ.rectOpNorm2Le_one
  have hback := hQT (rectMatMulVec Q x)
  have hid :
      rectMatMulVec (finiteTranspose Q) (rectMatMulVec Q x) = x := by
    ext i
    have hgram : forall j : Fin n,
        (∑ k : Fin m, Q k i * Q k j) = if i = j then 1 else 0 := by
      intro j
      simpa [GramSchmidtOrthonormalColumns, rectangularGram, idMatrix] using
        hQ i j
    unfold rectMatMulVec finiteTranspose
    calc
      (Finset.univ.sum fun k : Fin m =>
          Q k i * (Finset.univ.sum fun j : Fin n => Q k j * x j)) =
          Finset.univ.sum fun k : Fin m =>
            Finset.univ.sum fun j : Fin n => Q k i * (Q k j * x j) := by
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.mul_sum]
      _ = Finset.univ.sum fun j : Fin n =>
            Finset.univ.sum fun k : Fin m => Q k i * (Q k j * x j) := by
            rw [Finset.sum_comm]
      _ =
          Finset.univ.sum fun j : Fin n =>
            (Finset.univ.sum fun k : Fin m => Q k i * Q k j) * x j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro k _
            ring
      _ = x i := by
        simp_rw [hgram]
        simp
  rw [hid] at hback
  apply le_antisymm
  . simpa using hforward
  . simpa using hback

/-- Column form of the economy isometry. -/
theorem orthonormal_columns_matMulRect_columnFrob {m n p : Nat}
    (Q : Fin m -> Fin n -> Real) (R : Fin n -> Fin p -> Real)
    (hQ : GramSchmidtOrthonormalColumns Q) (j : Fin p) :
    columnFrob (matMulRect m n p Q R) j = columnFrob R j := by
  rw [columnFrob_eq_vecNorm2, columnFrob_eq_vecNorm2]
  change vecNorm2 (rectMatMulVec Q (fun i : Fin n => R i j)) =
    vecNorm2 (fun i : Fin n => R i j)
  exact orthonormal_columns_action_norm_eq Q hQ (fun i => R i j)

/-- Entrywise relative perturbations give the corresponding column 2-norm
bound. -/
theorem columnFrob_le_of_entrywise_relative_bound {m n : Nat}
    (A Delta : Fin m -> Fin n -> Real) {eta : Real}
    (heta : 0 <= eta)
    (hDelta : forall i j, |Delta i j| <= eta * |A i j|) :
    forall j, columnFrob Delta j <= eta * columnFrob A j := by
  intro j
  rw [columnFrob_eq_vecNorm2, columnFrob_eq_vecNorm2]
  have hpoint : forall i : Fin m, |Delta i j| <= eta * |A i j| := by
    intro i
    exact hDelta i j
  calc
    vecNorm2 (fun i : Fin m => Delta i j) <=
        vecNorm2 (fun i : Fin m => eta * |A i j|) :=
      vecNorm2_le_of_abs_le _ _ hpoint
    _ = eta * vecNorm2 (fun i : Fin m => A i j) := by
      rw [vecNorm2_smul, abs_of_nonneg heta, vecNorm2_abs]

/-- Columnwise bound after folding the concrete triangular-solve perturbation
into the repaired MGS factor. -/
theorem folded_matrix_column_bound
    {m n : Nat}
    (A DeltaA : Fin m -> Fin n -> Real)
    (Q : Fin m -> Fin n -> Real)
    (R DeltaR : Fin n -> Fin n -> Real)
    {etaQR etaR : Real}
    (hQ : GramSchmidtOrthonormalColumns Q)
    (hfactor : forall i j,
      A i j + DeltaA i j = matMulRect m n n Q R i j)
    (_hetaQR : 0 <= etaQR)
    (hDeltaA : forall j,
      columnFrob DeltaA j <= etaQR * columnFrob A j)
    (hetaR : 0 <= etaR)
    (hDeltaR : forall i j, |DeltaR i j| <= etaR * |R i j|) :
    forall j,
      columnFrob (foldedMatrixPerturbation Q DeltaA DeltaR) j <=
        (etaQR + etaR * (1 + etaQR)) * columnFrob A j := by
  intro j
  have hmat : matMulRect m n n Q R = fun i j => A i j + DeltaA i j := by
    ext i k
    exact (hfactor i k).symm
  have hR : columnFrob R j <= (1 + etaQR) * columnFrob A j := by
    calc
      columnFrob R j = columnFrob (matMulRect m n n Q R) j :=
        (orthonormal_columns_matMulRect_columnFrob Q R hQ j).symm
      _ = columnFrob (fun i k => A i k + DeltaA i k) j := by rw [hmat]
      _ <= columnFrob A j + columnFrob DeltaA j :=
        columnFrob_add_le A DeltaA j
      _ <= columnFrob A j + etaQR * columnFrob A j :=
        add_le_add_right (hDeltaA j) _
      _ = (1 + etaQR) * columnFrob A j := by ring
  have hDeltaRCol : columnFrob DeltaR j <= etaR * columnFrob R j :=
    columnFrob_le_of_entrywise_relative_bound R DeltaR hetaR hDeltaR j
  have hQDeltaR :
      columnFrob (matMulRect m n n Q DeltaR) j <= columnFrob DeltaR j := by
    have hbound := columnFrob_matMulRect_le_rectOpNorm2_mul_columnFrob
      Q DeltaR hQ.rectOpNorm2Le_one j
    simpa using hbound
  calc
    columnFrob (foldedMatrixPerturbation Q DeltaA DeltaR) j <=
        columnFrob DeltaA j +
          columnFrob (matMulRect m n n Q DeltaR) j :=
      columnFrob_add_le DeltaA (matMulRect m n n Q DeltaR) j
    _ <= etaQR * columnFrob A j + columnFrob DeltaR j :=
      add_le_add (hDeltaA j) hQDeltaR
    _ <= etaQR * columnFrob A j + etaR * columnFrob R j :=
      add_le_add_right hDeltaRCol _
    _ <= etaQR * columnFrob A j +
        etaR * ((1 + etaQR) * columnFrob A j) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hR hetaR)
        (etaQR * columnFrob A j)
    _ = (etaQR + etaR * (1 + etaQR)) * columnFrob A j := by ring

/-- The exact Chapter 20 transfer from the weakest global MGS input it uses:
an upper-triangular computed `R-hat` and the columnwise orthonormal repair
channel of Higham Theorem 19.13.  No computed-`Q` orthogonality or residual
bound is needed by the least-squares argument.

For the literal rounded loop, `actualAugmentedMGS_roundedState` proves the
algorithmic fields and upper shape.  This reusable transfer still accepts
`ModifiedGramSchmidtGlobalRepair` as a premise; the direct accumulated-polar
and computed-Gram endpoints later in the file construct that premise from the
literal trace. -/
theorem augmented_fl_backSub_columnwise_backward_error_of_globalRepair
    {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (Rhat : Fin (n + 1) -> Fin (n + 1) -> Real)
    {eta : Real}
    (hupper : IsUpperTrapezoidal (n + 1) (n + 1) Rhat)
    (hrepair : ModifiedGramSchmidtGlobalRepair m (n + 1)
      (augmentedInput A b) Rhat eta)
    (heta : 0 <= eta)
    (hdiag : forall i : Fin n, leadingR Rhat i i ≠ 0)
    (hvalid : gammaValid fp n) :
    exists DeltaA : Fin m -> Fin n -> Real,
    exists Deltab : Fin m -> Real,
      (forall j,
        vecNorm2 (fun i => DeltaA i j) <=
          matrixCoeff fp n eta * vecNorm2 (fun i => A i j)) /\
      vecNorm2 Deltab <= eta * vecNorm2 b /\
      IsLeastSquaresMinimizer
        (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i)
        (fl_backSub fp n (leadingR Rhat) (lastColumnTop Rhat)) := by
  rcases hrepair.repair with
    ⟨Qrepair, DeltaAug, hQ, hfactor, hDeltaAug⟩
  let DeltaA0 : Fin m -> Fin n -> Real := matrixPerturbation DeltaAug
  let Deltab0 : Fin m -> Real := rhsPerturbation DeltaAug
  let Q1 : Fin m -> Fin n -> Real := leadingQ Qrepair
  let R : Fin n -> Fin n -> Real := leadingR Rhat
  let z : Fin n -> Real := lastColumnTop Rhat
  have haug : MGSAugmentedLSFactorization
      (fun i j => A i j + DeltaA0 i j)
      (fun i => b i + Deltab0 i)
      Q1 (lastQ Qrepair) R z (lastDiagonal Rhat) := by
    exact augmented_factorization_of_repaired_factor
      A b Qrepair Rhat DeltaAug hQ hfactor hupper
  have hQ1 : GramSchmidtOrthonormalColumns Q1 := by
    intro i j
    simpa [Q1, leadingQ, GramSchmidtOrthonormalColumns, rectangularGram,
      idMatrix] using hQ i.castSucc j.castSucc
  have hDeltaA0 : forall j,
      columnFrob DeltaA0 j <= eta * columnFrob A j := by
    intro j
    simpa [DeltaA0, matrixPerturbation, augmentedInput,
      columnFrob_eq_vecNorm2] using hDeltaAug j.castSucc
  have hDeltab0 : vecNorm2 Deltab0 <= eta * vecNorm2 b := by
    simpa [Deltab0, rhsPerturbation, augmentedInput,
      columnFrob_eq_vecNorm2] using hDeltaAug (Fin.last n)
  have hRupper : forall i j : Fin n, j.val < i.val -> R i j = 0 := by
    intro i j hji
    exact hupper i.castSucc j.castSucc (by simpa using hji)
  rcases higham8_5_backSub_backward_error fp n R z
      (by simpa [R] using hdiag) hRupper hvalid with
    ⟨DeltaR, hDeltaR, hsolve⟩
  let DeltaA : Fin m -> Fin n -> Real :=
    foldedMatrixPerturbation Q1 DeltaA0 DeltaR
  have hfold : MGSAugmentedLSFactorization
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab0 i)
      Q1 (lastQ Qrepair) (fun i j => R i j + DeltaR i j) z
        (lastDiagonal Rhat) := by
    have hraw := folded_augmented_factorization
      (A := fun i j => A i j + DeltaA0 i j)
      (b := fun i => b i + Deltab0 i)
      (DeltaR := DeltaR) haug
    simpa [DeltaA, foldedMatrixPerturbation, add_assoc] using hraw
  have hmin : IsLeastSquaresMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab0 i)
      (fl_backSub fp n R z) := by
    apply hfold.isLeastSquaresMinimizer_of_solve
    intro i
    simpa [matMulVec] using hsolve i
  have hgamma : 0 <= gamma fp n := gamma_nonneg fp hvalid
  have hDeltaA : forall j,
      columnFrob DeltaA j <=
        matrixCoeff fp n eta * columnFrob A j := by
    intro j
    simpa [DeltaA, matrixCoeff] using
      folded_matrix_column_bound A DeltaA0 Q1 R DeltaR hQ1 haug.A_eq
        heta hDeltaA0 hgamma hDeltaR j
  refine ⟨DeltaA, Deltab0, ?_, hDeltab0, ?_⟩
  . intro j
    simpa [columnFrob_eq_vecNorm2] using hDeltaA j
  . simpa [R, z] using hmin

/-- Higham, 2nd ed., Appendix A, solution to Problem 20.5 (printed p. 566):
the Theorem 19.13 columnwise repair for the actual augmented input `[A b]`,
followed by the repository's concrete `fl_backSub`, returns an exact minimizer
of a columnwise perturbed least-squares problem.

This theorem proves the complete Chapter 20 transfer.  It does not assume the
least-squares conclusion, a triangular-solve error, or a perturbation witness:
all are constructed from `hMGS` and Theorem 8.5. -/
theorem augmented_mgs_fl_backSub_columnwise_backward_error
    {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (Qhat : Fin m -> Fin (n + 1) -> Real)
    (Rhat : Fin (n + 1) -> Fin (n + 1) -> Real)
    {c1 c2 c3 u normA kappaA higherOrder : Real}
    (hMGS : H19.Theorem19_13.MGSQRBounds m (n + 1)
      (augmentedInput A b) Qhat Rhat
      c1 c2 c3 u normA kappaA higherOrder)
    (heta : 0 <= c3 * u)
    (hdiag : forall i : Fin n, leadingR Rhat i i ≠ 0)
    (hvalid : gammaValid fp n) :
    exists DeltaA : Fin m -> Fin n -> Real,
    exists Deltab : Fin m -> Real,
      (forall j,
        vecNorm2 (fun i => DeltaA i j) <=
          matrixCoeff fp n (c3 * u) * vecNorm2 (fun i => A i j)) /\
      vecNorm2 Deltab <= (c3 * u) * vecNorm2 b /\
      IsLeastSquaresMinimizer
        (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i)
        (fl_backSub fp n (leadingR Rhat) (lastColumnTop Rhat)) := by
  rcases hMGS.r_factor with
    ⟨Qrepair, DeltaAug, hQ, hfactor, hDeltaAug⟩
  let DeltaA0 : Fin m -> Fin n -> Real := matrixPerturbation DeltaAug
  let Deltab0 : Fin m -> Real := rhsPerturbation DeltaAug
  let Q1 : Fin m -> Fin n -> Real := leadingQ Qrepair
  let R : Fin n -> Fin n -> Real := leadingR Rhat
  let z : Fin n -> Real := lastColumnTop Rhat
  have haug : MGSAugmentedLSFactorization
      (fun i j => A i j + DeltaA0 i j)
      (fun i => b i + Deltab0 i)
      Q1 (lastQ Qrepair) R z (lastDiagonal Rhat) := by
    exact augmented_factorization_of_repaired_factor
      A b Qrepair Rhat DeltaAug hQ hfactor hMGS.upper
  have hQ1 : GramSchmidtOrthonormalColumns Q1 := by
    intro i j
    simpa [Q1, leadingQ, GramSchmidtOrthonormalColumns, rectangularGram,
      idMatrix] using hQ i.castSucc j.castSucc
  have hDeltaA0 : forall j,
      columnFrob DeltaA0 j <= (c3 * u) * columnFrob A j := by
    intro j
    simpa [DeltaA0, matrixPerturbation, augmentedInput,
      columnFrob_eq_vecNorm2] using
      hDeltaAug j.castSucc
  have hDeltab0 : vecNorm2 Deltab0 <= (c3 * u) * vecNorm2 b := by
    simpa [Deltab0, rhsPerturbation, augmentedInput,
      columnFrob_eq_vecNorm2] using hDeltaAug (Fin.last n)
  have hupper : forall i j : Fin n, j.val < i.val -> R i j = 0 := by
    intro i j hji
    exact hMGS.upper i.castSucc j.castSucc (by simpa using hji)
  rcases higham8_5_backSub_backward_error fp n R z
      (by simpa [R] using hdiag) hupper hvalid with
    ⟨DeltaR, hDeltaR, hsolve⟩
  let DeltaA : Fin m -> Fin n -> Real :=
    foldedMatrixPerturbation Q1 DeltaA0 DeltaR
  have hfold : MGSAugmentedLSFactorization
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab0 i)
      Q1 (lastQ Qrepair) (fun i j => R i j + DeltaR i j) z
        (lastDiagonal Rhat) := by
    have hraw := folded_augmented_factorization
      (A := fun i j => A i j + DeltaA0 i j)
      (b := fun i => b i + Deltab0 i)
      (DeltaR := DeltaR) haug
    simpa [DeltaA, foldedMatrixPerturbation, add_assoc] using hraw
  have hmin : IsLeastSquaresMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab0 i)
      (fl_backSub fp n R z) := by
    apply hfold.isLeastSquaresMinimizer_of_solve
    intro i
    simpa [matMulVec] using hsolve i
  have hgamma : 0 <= gamma fp n := gamma_nonneg fp hvalid
  have hDeltaA : forall j,
      columnFrob DeltaA j <=
        matrixCoeff fp n (c3 * u) * columnFrob A j := by
    intro j
    simpa [DeltaA, matrixCoeff] using
      folded_matrix_column_bound A DeltaA0 Q1 R DeltaR hQ1 haug.A_eq
        heta hDeltaA0 hgamma hDeltaR j
  refine ⟨DeltaA, Deltab0, ?_, hDeltab0, ?_⟩
  . intro j
    simpa [columnFrob_eq_vecNorm2] using hDeltaA j
  . simpa [R, z] using hmin

/-- **Implementation-backed Problem 20.5 endpoint.**  The factors and returned
vector in this theorem are definitionally the outputs of the literal rounded
MGS loop on `[A b]` followed by literal rounded back substitution.

This reusable endpoint accepts `ModifiedGramSchmidtGlobalRepair` for that
computed `R-hat`.  It is strictly weaker than `MGSQRBounds` and assumes no
least-squares conclusion or triangular-solve error.  The direct endpoints
below construct it from the literal trace with accumulated-polar or
computed-Gram budgets. -/
theorem actualAugmentedMGS_fl_backSub_columnwise_backward_error
    {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    {eta : Real}
    (hrepair : ModifiedGramSchmidtGlobalRepair m (n + 1)
      (augmentedInput A b) (actualAugmentedMGSR fp A b) eta)
    (heta : 0 <= eta)
    (hdiag : forall i : Fin n,
      leadingR (actualAugmentedMGSR fp A b) i i ≠ 0)
    (hvalid : gammaValid fp n) :
    exists DeltaA : Fin m -> Fin n -> Real,
    exists Deltab : Fin m -> Real,
      (forall j,
        vecNorm2 (fun i => DeltaA i j) <=
          matrixCoeff fp n eta * vecNorm2 (fun i => A i j)) /\
      vecNorm2 Deltab <= eta * vecNorm2 b /\
      IsLeastSquaresMinimizer
        (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i)
        (actualAugmentedMGSBackSub fp A b) := by
  simpa [actualAugmentedMGSBackSub] using
    augmented_fl_backSub_columnwise_backward_error_of_globalRepair
      fp A b (actualAugmentedMGSR fp A b)
        (fl_modifiedGramSchmidtR_upperTrapezoidal fp (augmentedInput A b))
        hrepair heta hdiag hvalid

/-- The literal rounded state and the reusable conditional least-squares
backward-error endpoint packaged together.  This theorem makes the transfer
boundary auditable: `hm` and `hpivot` discharge every local Algorithm 19.12
field and the leading back-substitution pivots, while `hrepair` is supplied by
the accumulated-polar or computed-Gram producers in the direct endpoints
below. -/
theorem actualAugmentedMGSBackSub_implementation_endpoint
    {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    {eta : Real}
    (hm : gammaValid fp (2 * (m + 1)))
    (hpivot : forall k : Fin (n + 1),
      actualAugmentedMGSR fp A b k k ≠ 0)
    (hrepair : ModifiedGramSchmidtGlobalRepair m (n + 1)
      (augmentedInput A b) (actualAugmentedMGSR fp A b) eta)
    (heta : 0 <= eta)
    (hvalid : gammaValid fp n) :
    ModifiedGramSchmidtRoundedState fp (augmentedInput A b)
        (actualAugmentedMGSQ fp A b) (actualAugmentedMGSR fp A b)
        (flMGSVectors fp (augmentedInput A b)) /\
      exists DeltaA : Fin m -> Fin n -> Real,
      exists Deltab : Fin m -> Real,
        (forall j,
          vecNorm2 (fun i => DeltaA i j) <=
            matrixCoeff fp n eta * vecNorm2 (fun i => A i j)) /\
        vecNorm2 Deltab <= eta * vecNorm2 b /\
        IsLeastSquaresMinimizer
          (fun i j => A i j + DeltaA i j)
          (fun i => b i + Deltab i)
          (actualAugmentedMGSBackSub fp A b) := by
  refine ⟨actualAugmentedMGS_roundedState fp A b hm hpivot, ?_⟩
  exact actualAugmentedMGS_fl_backSub_columnwise_backward_error
    fp A b hrepair heta (fun i => hpivot i.castSucc) hvalid

/-- The explicit repair coefficient produced internally from the literal
augmented MGS run: locally accumulated product error plus polar Gram-defect
sensitivity. -/
noncomputable def actualAugmentedMGSAccumulatedPolarEta {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real) (b : Fin m -> Real) : Real :=
  mgsRoundedAccumulatedPolarRelativeBudget fp (augmentedInput A b)
    (actualAugmentedMGSQ fp A b) (actualAugmentedMGSR fp A b)
    (flMGSVectors fp (augmentedInput A b))

/-- **Direct end-to-end literal-MGS Problem 20.5 endpoint on its valid
domain.**  This theorem constructs the Chapter 19 polar repair internally,
runs the actual rounded back substitution, and returns the exact minimizer of
the displayed nearby least-squares problem.

The full-pivot premise includes the final augmented pivot.  It is intentionally
explicit: inputs such as `b = 0` or, in the exact limit, `b` already in the
range of `A`, may make that pivot zero and are not claimed by this endpoint. -/
theorem actualAugmentedMGSBackSub_end_to_end_accumulatedPolar
    {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (hnm : n + 1 <= m)
    (hm : gammaValid fp (2 * (m + 1)))
    (hpivot : forall k : Fin (n + 1),
      Ne (actualAugmentedMGSR fp A b k k) 0)
    (hsource : forall j : Fin (n + 1),
      0 < columnFrob (augmentedInput A b) j) :
    ModifiedGramSchmidtRoundedState fp (augmentedInput A b)
        (actualAugmentedMGSQ fp A b) (actualAugmentedMGSR fp A b)
        (flMGSVectors fp (augmentedInput A b)) /\
      exists DeltaA : Fin m -> Fin n -> Real,
      exists Deltab : Fin m -> Real,
        (forall j,
          vecNorm2 (fun i => DeltaA i j) <=
            matrixCoeff fp n (actualAugmentedMGSAccumulatedPolarEta fp A b) *
              vecNorm2 (fun i => A i j)) /\
        vecNorm2 Deltab <=
          actualAugmentedMGSAccumulatedPolarEta fp A b * vecNorm2 b /\
        IsLeastSquaresMinimizer
          (fun i j => A i j + DeltaA i j)
          (fun i => b i + Deltab i)
          (actualAugmentedMGSBackSub fp A b) := by
  let eta := actualAugmentedMGSAccumulatedPolarEta fp A b
  have hrepair : ModifiedGramSchmidtGlobalRepair m (n + 1)
      (augmentedInput A b) (actualAugmentedMGSR fp A b) eta := by
    simpa [eta, actualAugmentedMGSAccumulatedPolarEta,
      actualAugmentedMGSQ, actualAugmentedMGSR] using
      fl_modifiedGramSchmidt_globalRepairWithAccumulatedPolarBudget
        fp (augmentedInput A b) hnm hm hpivot hsource
  have heta : 0 <= eta := by
    simpa [eta, actualAugmentedMGSAccumulatedPolarEta] using
      mgsRoundedAccumulatedPolarRelativeBudget_nonneg fp
        (augmentedInput A b) (actualAugmentedMGSQ fp A b)
        (actualAugmentedMGSR fp A b)
        (flMGSVectors fp (augmentedInput A b))
  have hvalid : gammaValid fp n := gammaValid_mono fp (by omega) hm
  simpa [eta] using
    actualAugmentedMGSBackSub_implementation_endpoint
      fp A b hm hpivot hrepair heta hvalid

/-- The source-relative repair coefficient for a literal augmented-MGS run
when an independent analysis bounds the *computed* Gram defect by
`gramCoeff * fp.u`.  Its numerator is the telescoped local Algorithm 19.12
budget plus `(gramCoeff * fp.u) * ||Rhat(:,j)||₂`; it is not measured from the
realized repair residual. -/
noncomputable def actualAugmentedMGSLocalGramEta {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (gramCoeff : Real) : Real :=
  mgsRoundedLocalGramRepairRelativeBudget fp (augmentedInput A b)
    (actualAugmentedMGSQ fp A b) (actualAugmentedMGSR fp A b)
    (flMGSVectors fp (augmentedInput A b)) gramCoeff

/-- **Runtime/computed-Gram Problem 20.5 endpoint for literal MGS.**

This theorem runs the actual rounded MGS and back-substitution programs.  Its
only global numerical premise bounds the Gram defect computed from their
`Qhat` output; it does not assume a QR repair or least-squares conclusion.
The resulting perturbation coefficient is expanded into local trace budgets,
`gramCoeff * fp.u`, computed `Rhat` columns, and source-column norms.

This polar route is a quantitative implementation bridge.  Higham's printed
condition-number-independent `c3 * u` constant remains the separate padded-
Householder/QR-sensitivity conclusion of Theorem 19.13. -/
theorem actualAugmentedMGSBackSub_end_to_end_localGram
    {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (hnm : n + 1 <= m)
    (hm : gammaValid fp (2 * (m + 1)))
    (hpivot : forall k : Fin (n + 1),
      Ne (actualAugmentedMGSR fp A b k k) 0)
    {gramCoeff : Real} (hgramCoeff : 0 <= gramCoeff)
    (hgram : mgsRoundedPolarSensitivityBudget
      (actualAugmentedMGSQ fp A b) <= gramCoeff * fp.u)
    (hsource : forall j : Fin (n + 1),
      0 < columnFrob (augmentedInput A b) j) :
    ModifiedGramSchmidtRoundedState fp (augmentedInput A b)
        (actualAugmentedMGSQ fp A b) (actualAugmentedMGSR fp A b)
        (flMGSVectors fp (augmentedInput A b)) /\
      exists DeltaA : Fin m -> Fin n -> Real,
      exists Deltab : Fin m -> Real,
        (forall j,
          vecNorm2 (fun i => DeltaA i j) <=
            matrixCoeff fp n
                (actualAugmentedMGSLocalGramEta fp A b gramCoeff) *
              vecNorm2 (fun i => A i j)) /\
        vecNorm2 Deltab <=
          actualAugmentedMGSLocalGramEta fp A b gramCoeff * vecNorm2 b /\
        IsLeastSquaresMinimizer
          (fun i j => A i j + DeltaA i j)
          (fun i => b i + Deltab i)
          (actualAugmentedMGSBackSub fp A b) := by
  let eta := actualAugmentedMGSLocalGramEta fp A b gramCoeff
  have hrepair : ModifiedGramSchmidtGlobalRepair m (n + 1)
      (augmentedInput A b) (actualAugmentedMGSR fp A b) eta := by
    simpa [eta, actualAugmentedMGSLocalGramEta,
      actualAugmentedMGSQ, actualAugmentedMGSR] using
      fl_modifiedGramSchmidt_globalRepairWithLocalGramBudget
        fp (augmentedInput A b) hnm hm hpivot hgramCoeff hgram hsource
  have heta : 0 <= eta := by
    simpa [eta, actualAugmentedMGSLocalGramEta] using
      mgsRoundedLocalGramRepairRelativeBudget_nonneg fp
        (augmentedInput A b) (actualAugmentedMGSQ fp A b)
        (actualAugmentedMGSR fp A b)
        (flMGSVectors fp (augmentedInput A b)) hgramCoeff
  have hvalid : gammaValid fp n := gammaValid_mono fp (by omega) hm
  simpa [eta] using
    actualAugmentedMGSBackSub_implementation_endpoint
      fp A b hm hpivot hrepair heta hvalid

/-- Common-coefficient form matching the displayed conclusion shape of
Theorem 20.3. -/
theorem augmented_mgs_fl_backSub_theorem20_3_form
    {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (Qhat : Fin m -> Fin (n + 1) -> Real)
    (Rhat : Fin (n + 1) -> Fin (n + 1) -> Real)
    {c1 c2 c3 u normA kappaA higherOrder : Real}
    (hMGS : H19.Theorem19_13.MGSQRBounds m (n + 1)
      (augmentedInput A b) Qhat Rhat
      c1 c2 c3 u normA kappaA higherOrder)
    (heta : 0 <= c3 * u)
    (hdiag : forall i : Fin n, leadingR Rhat i i ≠ 0)
    (hvalid : gammaValid fp n) :
    exists DeltaA : Fin m -> Fin n -> Real,
    exists Deltab : Fin m -> Real,
      (forall j,
        vecNorm2 (fun i => DeltaA i j) <=
          commonCoeff fp n (c3 * u) * vecNorm2 (fun i => A i j)) /\
      vecNorm2 Deltab <= commonCoeff fp n (c3 * u) * vecNorm2 b /\
      IsLeastSquaresMinimizer
        (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i)
        (fl_backSub fp n (leadingR Rhat) (lastColumnTop Rhat)) := by
  rcases augmented_mgs_fl_backSub_columnwise_backward_error
      fp A b Qhat Rhat hMGS heta hdiag hvalid with
    ⟨DeltaA, Deltab, hDeltaA, hDeltab, hmin⟩
  refine ⟨DeltaA, Deltab, ?_, ?_, hmin⟩
  . intro j
    exact le_trans (hDeltaA j)
      (mul_le_mul_of_nonneg_right
        (le_max_left (matrixCoeff fp n (c3 * u)) (c3 * u))
        (vecNorm2_nonneg _))
  . exact le_trans hDeltab
      (mul_le_mul_of_nonneg_right
        (le_max_right (matrixCoeff fp n (c3 * u)) (c3 * u))
        (vecNorm2_nonneg b))

/-- Normwise consequence of the columnwise Problem 20.5 theorem.  The same
common coefficient controls the rectangular Frobenius matrix perturbation and
the Euclidean RHS perturbation. -/
theorem augmented_mgs_fl_backSub_normwise_backward_error
    {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (Qhat : Fin m -> Fin (n + 1) -> Real)
    (Rhat : Fin (n + 1) -> Fin (n + 1) -> Real)
    {c1 c2 c3 u normA kappaA higherOrder : Real}
    (hMGS : H19.Theorem19_13.MGSQRBounds m (n + 1)
      (augmentedInput A b) Qhat Rhat
      c1 c2 c3 u normA kappaA higherOrder)
    (heta : 0 <= c3 * u)
    (hdiag : forall i : Fin n, leadingR Rhat i i ≠ 0)
    (hvalid : gammaValid fp n) :
    exists DeltaA : Fin m -> Fin n -> Real,
    exists Deltab : Fin m -> Real,
      frobNormRect DeltaA <=
          commonCoeff fp n (c3 * u) * frobNormRect A /\
      vecNorm2 Deltab <= commonCoeff fp n (c3 * u) * vecNorm2 b /\
      IsLeastSquaresMinimizer
        (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i)
        (fl_backSub fp n (leadingR Rhat) (lastColumnTop Rhat)) := by
  rcases augmented_mgs_fl_backSub_theorem20_3_form
      fp A b Qhat Rhat hMGS heta hdiag hvalid with
    ⟨DeltaA, Deltab, hDeltaA, hDeltab, hmin⟩
  have hcoeff : 0 <= commonCoeff fp n (c3 * u) :=
    le_trans heta
      (le_max_right (matrixCoeff fp n (c3 * u)) (c3 * u))
  refine ⟨DeltaA, Deltab, ?_, hDeltab, hmin⟩
  exact frobNormRect_le_of_col_vecNorm2_le DeltaA A hcoeff hDeltaA

end Problem20_5

end

end NumStability
