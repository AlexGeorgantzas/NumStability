-- Algorithms/Underdetermined/Higham21Attainability.lean
--
-- Holder p-norm first-order attainability in Higham's Theorem 21.1.

import NumStability.Algorithms.Underdetermined.Higham21Perturbation

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-- The complete printed first-order majorant in Theorem 21.1, equation
    (21.6). -/
noncomputable def higham21Theorem21_1Majorant {m n : Nat}
    (A E : Fin m -> Fin n -> Real) (b f : Fin m -> Real) :
    Fin n -> Real :=
  fun j =>
    higham21Theorem21_1NullspaceMajorant A E b j +
      higham21Theorem21_1DataMajorant A E b f j

theorem higham21Theorem21_1Majorant_nonneg {m n : Nat}
    (A E : Fin m -> Fin n -> Real) (b f : Fin m -> Real)
    (hE : forall i j, 0 <= E i j) (hf : forall i, 0 <= f i) :
    forall j, 0 <= higham21Theorem21_1Majorant A E b f j := by
  intro j
  exact add_nonneg
    (higham21Theorem21_1NullspaceMajorant_nonneg A E b hE j)
    (higham21Theorem21_1DataMajorant_nonneg A E b f hE hf j)

/-- The null-space source vector in the first-order expansion (21.7). -/
noncomputable def higham21Theorem21_1NullspaceSource {m n : Nat}
    (A DeltaA : Fin m -> Fin n -> Real) (b : Fin m -> Real) :
    Fin n -> Real :=
  let Aplus := undetAplusOfGramNonsingInv A
  let x := rectMatMulVec Aplus b
  let z := rectTransposeMulVec Aplus x
  let w := rectTransposeMulVec DeltaA z
  fun j => w j - rectMatMulVec Aplus (rectMatMulVec A w) j

/-- The pseudoinverse-range source vector in the first-order expansion
    (21.7). -/
noncomputable def higham21Theorem21_1DataSource {m n : Nat}
    (A DeltaA : Fin m -> Fin n -> Real)
    (b Deltab : Fin m -> Real) : Fin n -> Real :=
  let Aplus := undetAplusOfGramNonsingInv A
  let x := rectMatMulVec Aplus b
  let q := fun i => Deltab i - rectMatMulVec DeltaA x i
  rectMatMulVec Aplus q

private theorem higham21_theorem21_1_gramDual_eq_pseudoinverseTranspose
    {m n : Nat} (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0) :
    matMulVec m (undetGramNonsingInv A) b =
      rectTransposeMulVec (undetAplusOfGramNonsingInv A)
        (rectMatMulVec (undetAplusOfGramNonsingInv A) b) := by
  let G_inv : Fin m -> Fin m -> Real := undetGramNonsingInv A
  let Aplus : Fin n -> Fin m -> Real := undetAplusOfGramNonsingInv A
  let y : Fin m -> Real := matMulVec m G_inv b
  let x : Fin n -> Real := rectMatMulVec Aplus b
  have hRight : rectMatMul A Aplus = idMatrix m := by
    simpa [Aplus] using
      higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_det_ne_zero
        A hdet
  have hx : x = rectTransposeMulVec A y := by
    simpa [x, Aplus, y, G_inv, undetAplusOfGramNonsingInv] using
      (rectMatMulVec_undetAplusOfGramInv A G_inv b)
  have htranspose :=
    higham21_theorem21_1_transpose_left_inverse_of_right_inverse
      A Aplus hRight y
  have hz :
      rectTransposeMulVec Aplus x =
        rectMatMulVec (finiteTranspose Aplus)
          (rectMatMulVec (finiteTranspose A) y) := by
    rw [hx]
    rfl
  change y = rectTransposeMulVec Aplus x
  exact (hz.trans htranspose).symm

/-- Equation (21.7) is the sum of its null-space and pseudoinverse-range
    source vectors. -/
theorem higham21_theorem21_1_firstOrder_eq_sources {m n : Nat}
    (A DeltaA : Fin m -> Fin n -> Real)
    (b Deltab : Fin m -> Real)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0) :
    higham21Eq21_7FirstOrder A DeltaA b Deltab
        (undetGramNonsingInv A) =
      fun j =>
        higham21Theorem21_1NullspaceSource A DeltaA b j +
          higham21Theorem21_1DataSource A DeltaA b Deltab j := by
  let G_inv : Fin m -> Fin m -> Real := undetGramNonsingInv A
  let Aplus : Fin n -> Fin m -> Real := undetAplusOfGramNonsingInv A
  let x : Fin n -> Real := rectMatMulVec Aplus b
  let y : Fin m -> Real := matMulVec m G_inv b
  let z : Fin m -> Real := rectTransposeMulVec Aplus x
  let w : Fin n -> Real := rectTransposeMulVec DeltaA z
  let q : Fin m -> Real := fun i => Deltab i - rectMatMulVec DeltaA x i
  have hyz : y = z := by
    simpa [y, z, x, Aplus, G_inv] using
      (higham21_theorem21_1_gramDual_eq_pseudoinverseTranspose A b hdet)
  ext j
  simp only [higham21Eq21_7FirstOrder]
  change
    rectTransposeMulVec DeltaA y j -
          rectMatMulVec Aplus
            (rectMatMulVec A (rectTransposeMulVec DeltaA y)) j +
        rectMatMulVec Aplus q j =
      (w j - rectMatMulVec Aplus (rectMatMulVec A w) j) +
        rectMatMulVec Aplus q j
  rw [hyz]

/-- The two named source vectors are orthogonal. -/
theorem higham21_theorem21_1_sources_orthogonal {m n : Nat}
    (A DeltaA : Fin m -> Fin n -> Real)
    (b Deltab : Fin m -> Real)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0) :
    (Finset.univ.sum fun j : Fin n =>
      higham21Theorem21_1NullspaceSource A DeltaA b j *
        higham21Theorem21_1DataSource A DeltaA b Deltab j) = 0 := by
  simpa [higham21Theorem21_1NullspaceSource,
    higham21Theorem21_1DataSource] using
      (higham21Eq21_7_source_vectors_orthogonal
        A DeltaA b Deltab hdet)

private theorem higham21_vecNorm2_left_le_add_of_inner_eq_zero {n : Nat}
    (u v : Fin n -> Real)
    (horth : (Finset.univ.sum fun j : Fin n => u j * v j) = 0) :
    vecNorm2 u <= vecNorm2 (fun j => u j + v j) := by
  have hpyth :
      vecNorm2Sq (fun j => u j + v j) = vecNorm2Sq u + vecNorm2Sq v := by
    simpa [finiteVecNorm2Sq_fin] using
      (finiteVecNorm2Sq_add_of_inner_eq_zero u v horth)
  unfold vecNorm2
  exact Real.sqrt_le_sqrt (by
    rw [hpyth]
    exact le_add_of_nonneg_right (vecNorm2Sq_nonneg v))

private theorem higham21_vecNorm2_right_le_add_of_inner_eq_zero {n : Nat}
    (u v : Fin n -> Real)
    (horth : (Finset.univ.sum fun j : Fin n => u j * v j) = 0) :
    vecNorm2 v <= vecNorm2 (fun j => u j + v j) := by
  have hpyth :
      vecNorm2Sq (fun j => u j + v j) = vecNorm2Sq u + vecNorm2Sq v := by
    simpa [finiteVecNorm2Sq_fin] using
      (finiteVecNorm2Sq_add_of_inner_eq_zero u v horth)
  unfold vecNorm2
  exact Real.sqrt_le_sqrt (by
    rw [hpyth]
    exact le_add_of_nonneg_left (vecNorm2Sq_nonneg u))

theorem higham21_theorem21_1_nullspaceSource_vecNorm2_le_firstOrder
    {m n : Nat} (A DeltaA : Fin m -> Fin n -> Real)
    (b Deltab : Fin m -> Real)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0) :
    vecNorm2 (higham21Theorem21_1NullspaceSource A DeltaA b) <=
      vecNorm2 (higham21Eq21_7FirstOrder A DeltaA b Deltab
        (undetGramNonsingInv A)) := by
  rw [higham21_theorem21_1_firstOrder_eq_sources A DeltaA b Deltab hdet]
  exact higham21_vecNorm2_left_le_add_of_inner_eq_zero _ _
    (higham21_theorem21_1_sources_orthogonal
      A DeltaA b Deltab hdet)

theorem higham21_theorem21_1_dataSource_vecNorm2_le_firstOrder
    {m n : Nat} (A DeltaA : Fin m -> Fin n -> Real)
    (b Deltab : Fin m -> Real)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0) :
    vecNorm2 (higham21Theorem21_1DataSource A DeltaA b Deltab) <=
      vecNorm2 (higham21Eq21_7FirstOrder A DeltaA b Deltab
        (undetGramNonsingInv A)) := by
  rw [higham21_theorem21_1_firstOrder_eq_sources A DeltaA b Deltab hdet]
  exact higham21_vecNorm2_right_le_add_of_inner_eq_zero _ _
    (higham21_theorem21_1_sources_orthogonal
      A DeltaA b Deltab hdet)

/-- The printed equation-(21.6) upper bound in a finite Holder `p`-norm. -/
theorem higham21_theorem21_1_holder_firstOrder_upper_bound {m n : Nat}
    {p : Real} (hp : 1 <= p)
    (A DeltaA E : Fin m -> Fin n -> Real)
    (b Deltab f : Fin m -> Real) (eps : Real)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0)
    (heps : 0 <= eps) (hE : forall i j, 0 <= E i j)
    (hf : forall i, 0 <= f i)
    (hDeltaA : forall i j, abs (DeltaA i j) <= eps * E i j)
    (hDeltab : forall i, abs (Deltab i) <= eps * f i) :
    complexVecLpNorm (ENNReal.ofReal p)
        (realVecToComplex
          (higham21Eq21_7FirstOrder A DeltaA b Deltab
            (undetGramNonsingInv A))) <=
      eps * complexVecLpNorm (ENNReal.ofReal p)
        (realVecToComplex (higham21Theorem21_1Majorant A E b f)) := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  letI : Fact (1 <= ENNReal.ofReal p) := by
    constructor
    rw [ENNReal.one_le_ofReal]
    exact hp
  let nu : CVec n -> Real := complexVecLpNorm (ENNReal.ofReal p)
  have hnu : IsComplexVectorNorm nu :=
    complexVecLpNorm_isComplexVectorNorm (ENNReal.ofReal p)
  have habs : IsAbsoluteComplexVectorNorm nu :=
    complexVecLpNorm_ofReal_abs_eq hp_pos
  have hmajor : forall j,
      0 <= eps * higham21Theorem21_1Majorant A E b f j := by
    intro j
    exact mul_nonneg heps
      (higham21Theorem21_1Majorant_nonneg A E b f hE hf j)
  have hpoint : forall j,
      abs (higham21Eq21_7FirstOrder A DeltaA b Deltab
        (undetGramNonsingInv A) j) <=
        eps * higham21Theorem21_1Majorant A E b f j := by
    intro j
    simpa [higham21Theorem21_1Majorant] using
      (higham21_theorem21_1_firstOrder_componentwise_bound
        A DeltaA E b Deltab f eps hdet hDeltaA hDeltab j)
  calc
    complexVecLpNorm (ENNReal.ofReal p)
        (realVecToComplex
          (higham21Eq21_7FirstOrder A DeltaA b Deltab
            (undetGramNonsingInv A))) <=
        nu (realVecToComplex
          (fun j => eps * higham21Theorem21_1Majorant A E b f j)) :=
      realVecToComplex_norm_le_of_abs_le hnu habs hmajor hpoint
    _ = eps * nu
        (realVecToComplex (higham21Theorem21_1Majorant A E b f)) :=
      realVecToComplex_norm_smul_nonneg hnu eps heps _

/-- Sign perturbation attaining a chosen coordinate of the null-space
    majorant. -/
noncomputable def higham21Theorem21_1NullspaceAttainingDeltaA {m n : Nat}
    (A E : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (eps : Real) (j0 : Fin n) : Fin m -> Fin n -> Real :=
  let Aplus := undetAplusOfGramNonsingInv A
  let x := rectMatMulVec Aplus b
  let z := rectTransposeMulVec Aplus x
  let P := lsAugmentedProjectionBlock Aplus A
  fun i k =>
    eps * summationAbsSign (P j0 k) * E i k * summationAbsSign (z i)

theorem higham21Theorem21_1NullspaceAttainingDeltaA_abs {m n : Nat}
    (A E : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (eps : Real) (j0 : Fin n) (heps : 0 <= eps)
    (hE : forall i k, 0 <= E i k) :
    forall i k,
      abs (higham21Theorem21_1NullspaceAttainingDeltaA
        A E b eps j0 i k) = eps * E i k := by
  intro i k
  simp [higham21Theorem21_1NullspaceAttainingDeltaA, abs_mul,
    abs_summationAbsSign, abs_of_nonneg heps, abs_of_nonneg (hE i k)]

theorem higham21Theorem21_1NullspaceAttainingDeltaA_source_coord
    {m n : Nat} (A E : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (eps : Real) (j0 : Fin n) :
    higham21Theorem21_1NullspaceSource A
        (higham21Theorem21_1NullspaceAttainingDeltaA A E b eps j0) b j0 =
      eps * higham21Theorem21_1NullspaceMajorant A E b j0 := by
  let Aplus : Fin n -> Fin m -> Real := undetAplusOfGramNonsingInv A
  let x : Fin n -> Real := rectMatMulVec Aplus b
  let z : Fin m -> Real := rectTransposeMulVec Aplus x
  let P : Fin n -> Fin n -> Real := lsAugmentedProjectionBlock Aplus A
  let DeltaA : Fin m -> Fin n -> Real :=
    higham21Theorem21_1NullspaceAttainingDeltaA A E b eps j0
  let w : Fin n -> Real := rectTransposeMulVec DeltaA z
  let W : Fin n -> Real := lsComponentwiseTransposeMajorant E z
  have hw : forall k,
      w k = eps * summationAbsSign (P j0 k) * W k := by
    intro k
    change
      (Finset.univ.sum fun i : Fin m =>
        (eps * summationAbsSign (P j0 k) * E i k *
          summationAbsSign (z i)) * z i) =
        eps * summationAbsSign (P j0 k) *
          (Finset.univ.sum fun i : Fin m => E i k * abs (z i))
    calc
      (Finset.univ.sum fun i : Fin m =>
          (eps * summationAbsSign (P j0 k) * E i k *
            summationAbsSign (z i)) * z i) =
          Finset.univ.sum (fun i : Fin m =>
            (eps * summationAbsSign (P j0 k)) *
              (E i k * abs (z i))) := by
            apply Finset.sum_congr rfl
            intro i _
            calc
              (eps * summationAbsSign (P j0 k) * E i k *
                  summationAbsSign (z i)) * z i =
                  (eps * summationAbsSign (P j0 k) * E i k) *
                    (summationAbsSign (z i) * z i) := by ring
              _ = (eps * summationAbsSign (P j0 k)) *
                    (E i k * abs (z i)) := by
                  rw [summationAbsSign_mul_eq_abs]
                  ring
      _ = eps * summationAbsSign (P j0 k) *
          (Finset.univ.sum fun i : Fin m => E i k * abs (z i)) := by
            rw [Finset.mul_sum]
  have hprojection :
      higham21Theorem21_1NullspaceSource A DeltaA b j0 =
        rectMatMulVec P w j0 := by
    have hact := congrFun (lsAugmentedProjectionBlock_mulVec Aplus A w) j0
    exact hact.symm
  calc
    higham21Theorem21_1NullspaceSource A
        (higham21Theorem21_1NullspaceAttainingDeltaA A E b eps j0) b j0 =
        Finset.univ.sum (fun k : Fin n => P j0 k * w k) := by
          change higham21Theorem21_1NullspaceSource A DeltaA b j0 = _
          rw [hprojection]
          rfl
    _ = Finset.univ.sum (fun k : Fin n =>
        P j0 k * (eps * summationAbsSign (P j0 k) * W k)) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [hw k]
    _ = eps * Finset.univ.sum (fun k : Fin n => abs (P j0 k) * W k) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          calc
            P j0 k * (eps * summationAbsSign (P j0 k) * W k) =
                eps * (P j0 k * summationAbsSign (P j0 k)) * W k := by
              ring
            _ = eps * (abs (P j0 k) * W k) := by
              rw [mul_summationAbsSign_eq_abs]
              ring
    _ = eps * higham21Theorem21_1NullspaceMajorant A E b j0 := by
          rfl

/-- Sign matrix attaining the `E|x|` part of a chosen coordinate of the data
    majorant. -/
noncomputable def higham21Theorem21_1DataAttainingDeltaA {m n : Nat}
    (A E : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (eps : Real) (j0 : Fin n) : Fin m -> Fin n -> Real :=
  let Aplus := undetAplusOfGramNonsingInv A
  let x := rectMatMulVec Aplus b
  fun i k =>
    -(eps * summationAbsSign (Aplus j0 i) * E i k *
      summationAbsSign (x k))

/-- Sign right-hand-side perturbation attaining the `f` part of a chosen
    coordinate of the data majorant. -/
noncomputable def higham21Theorem21_1DataAttainingDeltab {m n : Nat}
    (A : Fin m -> Fin n -> Real) (f : Fin m -> Real)
    (eps : Real) (j0 : Fin n) : Fin m -> Real :=
  let Aplus := undetAplusOfGramNonsingInv A
  fun i => eps * summationAbsSign (Aplus j0 i) * f i

theorem higham21Theorem21_1DataAttainingDeltaA_abs {m n : Nat}
    (A E : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (eps : Real) (j0 : Fin n) (heps : 0 <= eps)
    (hE : forall i k, 0 <= E i k) :
    forall i k,
      abs (higham21Theorem21_1DataAttainingDeltaA
        A E b eps j0 i k) = eps * E i k := by
  intro i k
  simp [higham21Theorem21_1DataAttainingDeltaA, abs_mul,
    abs_summationAbsSign, abs_of_nonneg heps, abs_of_nonneg (hE i k)]

theorem higham21Theorem21_1DataAttainingDeltab_abs {m n : Nat}
    (A : Fin m -> Fin n -> Real) (f : Fin m -> Real)
    (eps : Real) (j0 : Fin n) (heps : 0 <= eps)
    (hf : forall i, 0 <= f i) :
    forall i,
      abs (higham21Theorem21_1DataAttainingDeltab A f eps j0 i) =
        eps * f i := by
  intro i
  simp [higham21Theorem21_1DataAttainingDeltab, abs_mul,
    abs_summationAbsSign, abs_of_nonneg heps, abs_of_nonneg (hf i)]

theorem higham21Theorem21_1DataAttainers_source_coord {m n : Nat}
    (A E : Fin m -> Fin n -> Real) (b f : Fin m -> Real)
    (eps : Real) (j0 : Fin n) :
    higham21Theorem21_1DataSource A
        (higham21Theorem21_1DataAttainingDeltaA A E b eps j0) b
        (higham21Theorem21_1DataAttainingDeltab A f eps j0) j0 =
      eps * higham21Theorem21_1DataMajorant A E b f j0 := by
  let Aplus : Fin n -> Fin m -> Real := undetAplusOfGramNonsingInv A
  let x : Fin n -> Real := rectMatMulVec Aplus b
  let DeltaA : Fin m -> Fin n -> Real :=
    higham21Theorem21_1DataAttainingDeltaA A E b eps j0
  let Deltab : Fin m -> Real :=
    higham21Theorem21_1DataAttainingDeltab A f eps j0
  let q : Fin m -> Real := fun i => Deltab i - rectMatMulVec DeltaA x i
  let budget : Fin m -> Real := lsComponentwiseDataMajorant E f x
  have haction : forall i,
      rectMatMulVec DeltaA x i =
        -(eps * summationAbsSign (Aplus j0 i)) *
          rectMatMulVec E (fun k => abs (x k)) i := by
    intro i
    change
      (Finset.univ.sum fun k : Fin n =>
        (-(eps * summationAbsSign (Aplus j0 i) * E i k *
          summationAbsSign (x k))) * x k) =
        -(eps * summationAbsSign (Aplus j0 i)) *
          (Finset.univ.sum fun k : Fin n => E i k * abs (x k))
    calc
      (Finset.univ.sum fun k : Fin n =>
          (-(eps * summationAbsSign (Aplus j0 i) * E i k *
            summationAbsSign (x k))) * x k) =
          Finset.univ.sum (fun k : Fin n =>
            (-(eps * summationAbsSign (Aplus j0 i))) *
              (E i k * abs (x k))) := by
            apply Finset.sum_congr rfl
            intro k _
            calc
              (-(eps * summationAbsSign (Aplus j0 i) * E i k *
                  summationAbsSign (x k))) * x k =
                  -(eps * summationAbsSign (Aplus j0 i) * E i k) *
                    (summationAbsSign (x k) * x k) := by ring
              _ = (-(eps * summationAbsSign (Aplus j0 i))) *
                    (E i k * abs (x k)) := by
                  rw [summationAbsSign_mul_eq_abs]
                  ring
      _ = -(eps * summationAbsSign (Aplus j0 i)) *
          (Finset.univ.sum fun k : Fin n => E i k * abs (x k)) := by
            rw [Finset.mul_sum]
  have hq : forall i,
      q i = eps * summationAbsSign (Aplus j0 i) * budget i := by
    intro i
    change
      eps * summationAbsSign (Aplus j0 i) * f i -
          rectMatMulVec DeltaA x i =
        eps * summationAbsSign (Aplus j0 i) *
          (f i + rectMatMulVec E (fun k => abs (x k)) i)
    rw [haction i]
    ring
  calc
    higham21Theorem21_1DataSource A
        (higham21Theorem21_1DataAttainingDeltaA A E b eps j0) b
        (higham21Theorem21_1DataAttainingDeltab A f eps j0) j0 =
        Finset.univ.sum (fun i : Fin m => Aplus j0 i * q i) := by
          rfl
    _ = Finset.univ.sum (fun i : Fin m =>
        Aplus j0 i *
          (eps * summationAbsSign (Aplus j0 i) * budget i)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hq i]
    _ = eps * Finset.univ.sum (fun i : Fin m =>
        abs (Aplus j0 i) * budget i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          calc
            Aplus j0 i *
                (eps * summationAbsSign (Aplus j0 i) * budget i) =
                eps * (Aplus j0 i * summationAbsSign (Aplus j0 i)) *
                  budget i := by ring
            _ = eps * (abs (Aplus j0 i) * budget i) := by
              rw [mul_summationAbsSign_eq_abs]
              ring
    _ = eps * higham21Theorem21_1DataMajorant A E b f j0 := by
          rfl

/-- Index at which the larger of the two source majorants is globally
    maximal. -/
noncomputable def higham21Theorem21_1MajorantArgmax {m n : Nat}
    (hn : 0 < n) (A E : Fin m -> Fin n -> Real)
    (b f : Fin m -> Real) : Fin n :=
  (Finset.exists_max_image Finset.univ
    (fun j : Fin n => max
      (higham21Theorem21_1NullspaceMajorant A E b j)
      (higham21Theorem21_1DataMajorant A E b f j))
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩).choose

theorem higham21Theorem21_1MajorantArgmax_spec {m n : Nat}
    (hn : 0 < n) (A E : Fin m -> Fin n -> Real)
    (b f : Fin m -> Real) :
    forall j : Fin n,
      max (higham21Theorem21_1NullspaceMajorant A E b j)
          (higham21Theorem21_1DataMajorant A E b f j) <=
        max
          (higham21Theorem21_1NullspaceMajorant A E b
            (higham21Theorem21_1MajorantArgmax hn A E b f))
          (higham21Theorem21_1DataMajorant A E b f
            (higham21Theorem21_1MajorantArgmax hn A E b f)) := by
  intro j
  exact
    ((Finset.exists_max_image Finset.univ
      (fun k : Fin n => max
        (higham21Theorem21_1NullspaceMajorant A E b k)
        (higham21Theorem21_1DataMajorant A E b f k))
      ⟨⟨0, hn⟩, Finset.mem_univ _⟩).choose_spec.2
        j (Finset.mem_univ j))

/-- The explicit finite-dimensional loss used in the constructive half of
    Theorem 21.1. -/
noncomputable def higham21Theorem21_1HolderAttainmentFactor
    (n : Nat) (p : Real) : Real :=
  2 * (n : Real) ^ p⁻¹ *
    (n : Real) ^ abs (p⁻¹ - (2 : Real)⁻¹)

private theorem higham21_complexVecLpNorm_two_realVecToComplex_eq_vecNorm2
    {n : Nat} (x : Fin n -> Real) :
    complexVecLpNorm (ENNReal.ofReal (2 : Real)) (realVecToComplex x) =
      vecNorm2 x := by
  calc
    complexVecLpNorm (ENNReal.ofReal (2 : Real)) (realVecToComplex x) =
        norm (WithLp.toLp (2 : ENNReal) (realVecToComplex x)) :=
      complexVecLpNorm_two_eq_toLp (realVecToComplex x)
    _ = norm (realVecToEuclidean x) := by
      rfl
    _ = vecNorm2 x := realVecToEuclidean_norm x

private theorem higham21_vecNorm2_le_holderFactor_mul_lpNorm {n : Nat}
    (hn : 0 < n) {p : Real} (hp : 1 <= p) (x : Fin n -> Real) :
    vecNorm2 x <=
      (n : Real) ^ abs (p⁻¹ - (2 : Real)⁻¹) *
        complexVecLpNorm (ENNReal.ofReal p) (realVecToComplex x) := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hn_one_nat : 1 <= n := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn)
  have hn_one : (1 : Real) <= (n : Real) := by
    exact_mod_cast hn_one_nat
  have hfactor_one :
      1 <= (n : Real) ^ abs (p⁻¹ - (2 : Real)⁻¹) :=
    Real.one_le_rpow hn_one (abs_nonneg _)
  by_cases hp2 : p <= 2
  · have hmono :
        complexVecLpNorm (ENNReal.ofReal (2 : Real)) (realVecToComplex x) <=
          complexVecLpNorm (ENNReal.ofReal p) (realVecToComplex x) := by
      exact complexVecLpNorm_le_complexVecLpNorm_of_exponent_le
        hp hp2 (realVecToComplex x)
    calc
      vecNorm2 x =
          complexVecLpNorm (ENNReal.ofReal (2 : Real))
            (realVecToComplex x) :=
        (higham21_complexVecLpNorm_two_realVecToComplex_eq_vecNorm2 x).symm
      _ <= complexVecLpNorm (ENNReal.ofReal p) (realVecToComplex x) := hmono
      _ <= (n : Real) ^ abs (p⁻¹ - (2 : Real)⁻¹) *
          complexVecLpNorm (ENNReal.ofReal p) (realVecToComplex x) :=
        le_mul_of_one_le_left
          (complexVecLpNorm_ofReal_nonneg hp_pos (realVecToComplex x))
          hfactor_one
  · have h2p : (2 : Real) <= p := le_of_not_ge hp2
    have habs :
        abs (p⁻¹ - (2 : Real)⁻¹) = (2 : Real)⁻¹ - p⁻¹ := by
      have hinv_le : p⁻¹ <= (2 : Real)⁻¹ := by
        have htwo_pos : (0 : Real) < 2 := by norm_num
        simpa [one_div] using (one_div_le_one_div_of_le htwo_pos h2p)
      simpa using
        (abs_of_nonpos (sub_nonpos.mpr hinv_le) :
          abs (p⁻¹ - (2 : Real)⁻¹) =
            -(p⁻¹ - (2 : Real)⁻¹))
    calc
      vecNorm2 x =
          complexVecLpNorm (ENNReal.ofReal (2 : Real))
            (realVecToComplex x) :=
        (higham21_complexVecLpNorm_two_realVecToComplex_eq_vecNorm2 x).symm
      _ <= (n : Real) ^ ((2 : Real)⁻¹ - p⁻¹) *
          complexVecLpNorm (ENNReal.ofReal p) (realVecToComplex x) := by
        exact complexVecLpNorm_le_card_rpow_mul_complexVecLpNorm_of_exponent_le
          (q := (2 : Real)) (p := p) (by norm_num) h2p
            (realVecToComplex x)
      _ = (n : Real) ^ abs (p⁻¹ - (2 : Real)⁻¹) *
          complexVecLpNorm (ENNReal.ofReal p) (realVecToComplex x) := by
        rw [habs]

/-- Constructive Holder `p`-norm attainability for Theorem 21.1.  A sign
    perturbation attains a maximal coordinate of the larger source majorant;
    orthogonality protects that source in the 2-norm.  The only losses are the
    two-source maximum estimate and finite-dimensional `p`/`2` comparison. -/
theorem higham21_theorem21_1_holder_firstOrder_attainability {m n : Nat}
    (hn : 0 < n) {p : Real} (hp : 1 <= p)
    (A E : Fin m -> Fin n -> Real) (b f : Fin m -> Real)
    (eps : Real)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0)
    (heps : 0 <= eps) (hE : forall i j, 0 <= E i j)
    (hf : forall i, 0 <= f i) :
    exists DeltaA : Fin m -> Fin n -> Real, exists Deltab : Fin m -> Real,
      (forall i j, abs (DeltaA i j) <= eps * E i j) /\
      (forall i, abs (Deltab i) <= eps * f i) /\
      eps * complexVecLpNorm (ENNReal.ofReal p)
          (realVecToComplex (higham21Theorem21_1Majorant A E b f)) <=
        higham21Theorem21_1HolderAttainmentFactor n p *
          complexVecLpNorm (ENNReal.ofReal p)
            (realVecToComplex
              (higham21Eq21_7FirstOrder A DeltaA b Deltab
                (undetGramNonsingInv A))) := by
  let left : Fin n -> Real := higham21Theorem21_1NullspaceMajorant A E b
  let right : Fin n -> Real := higham21Theorem21_1DataMajorant A E b f
  let total : Fin n -> Real := higham21Theorem21_1Majorant A E b f
  let jstar : Fin n := higham21Theorem21_1MajorantArgmax hn A E b f
  let M : Real := max (left jstar) (right jstar)
  let np : Real := (n : Real) ^ p⁻¹
  let c : Real := (n : Real) ^ abs (p⁻¹ - (2 : Real)⁻¹)
  have hleft : forall j, 0 <= left j := by
    intro j
    exact higham21Theorem21_1NullspaceMajorant_nonneg A E b hE j
  have hright : forall j, 0 <= right j := by
    intro j
    exact higham21Theorem21_1DataMajorant_nonneg A E b f hE hf j
  have htotal : forall j, total j = left j + right j := by
    intro j
    rfl
  have htotal_nonneg : forall j, 0 <= total j := by
    intro j
    rw [htotal j]
    exact add_nonneg (hleft j) (hright j)
  have hmax : forall j, max (left j) (right j) <= M := by
    intro j
    simpa [left, right, M, jstar] using
      (higham21Theorem21_1MajorantArgmax_spec hn A E b f j)
  have hM_nonneg : 0 <= M :=
    (hleft jstar).trans (le_max_left (left jstar) (right jstar))
  have htotal_le : forall j, total j <= 2 * M := by
    intro j
    have hlM : left j <= M :=
      (le_max_left (left j) (right j)).trans (hmax j)
    have hrM : right j <= M :=
      (le_max_right (left j) (right j)).trans (hmax j)
    rw [htotal j]
    linarith
  have hinf :
      complexVecInfNorm (realVecToComplex total) <= 2 * M := by
    apply complexVecInfNorm_le_of_coord_le _
      (mul_nonneg (by norm_num) hM_nonneg)
    intro j
    simpa [realVecToComplex, Real.norm_eq_abs,
      abs_of_nonneg (htotal_nonneg j)] using htotal_le j
  have hnp_nonneg : 0 <= np :=
    Real.rpow_nonneg (Nat.cast_nonneg n) p⁻¹
  have htotal_lp :
      complexVecLpNorm (ENNReal.ofReal p) (realVecToComplex total) <=
        2 * np * M := by
    calc
      complexVecLpNorm (ENNReal.ofReal p) (realVecToComplex total) <=
          np * complexVecInfNorm (realVecToComplex total) := by
        simpa [np] using
          (complexVecLpNorm_le_card_rpow_mul_complexVecInfNorm
            hp (realVecToComplex total))
      _ <= np * (2 * M) :=
        mul_le_mul_of_nonneg_left hinf hnp_nonneg
      _ = 2 * np * M := by ring
  have hscaled_total :
      eps * complexVecLpNorm (ENNReal.ofReal p) (realVecToComplex total) <=
        (2 * np) * (eps * M) := by
    calc
      eps * complexVecLpNorm (ENNReal.ofReal p) (realVecToComplex total) <=
          eps * (2 * np * M) :=
        mul_le_mul_of_nonneg_left htotal_lp heps
      _ = (2 * np) * (eps * M) := by ring
  have hselected :
      exists DeltaA : Fin m -> Fin n -> Real,
        exists Deltab : Fin m -> Real,
          (forall i j, abs (DeltaA i j) <= eps * E i j) /\
          (forall i, abs (Deltab i) <= eps * f i) /\
          eps * M <=
            vecNorm2 (higham21Eq21_7FirstOrder A DeltaA b Deltab
              (undetGramNonsingInv A)) := by
    by_cases hbranch : right jstar <= left jstar
    · let DeltaA :=
        higham21Theorem21_1NullspaceAttainingDeltaA A E b eps jstar
      let Deltab : Fin m -> Real := 0
      refine ⟨DeltaA, Deltab, ?_, ?_, ?_⟩
      · intro i j
        rw [higham21Theorem21_1NullspaceAttainingDeltaA_abs
          A E b eps jstar heps hE i j]
      · intro i
        simpa [Deltab] using mul_nonneg heps (hf i)
      · have hM : M = left jstar := max_eq_left hbranch
        calc
          eps * M =
              abs (higham21Theorem21_1NullspaceSource A DeltaA b jstar) := by
            rw [hM]
            change eps * left jstar =
              abs (higham21Theorem21_1NullspaceSource A
                (higham21Theorem21_1NullspaceAttainingDeltaA
                  A E b eps jstar) b jstar)
            rw [higham21Theorem21_1NullspaceAttainingDeltaA_source_coord]
            rw [abs_of_nonneg (mul_nonneg heps (hleft jstar))]
          _ <= vecNorm2
              (higham21Theorem21_1NullspaceSource A DeltaA b) :=
            abs_coord_le_vecNorm2 _ jstar
          _ <= vecNorm2
              (higham21Eq21_7FirstOrder A DeltaA b Deltab
                (undetGramNonsingInv A)) :=
            higham21_theorem21_1_nullspaceSource_vecNorm2_le_firstOrder
              A DeltaA b Deltab hdet
    · have hleftRight : left jstar <= right jstar :=
        (lt_of_not_ge hbranch).le
      let DeltaA :=
        higham21Theorem21_1DataAttainingDeltaA A E b eps jstar
      let Deltab :=
        higham21Theorem21_1DataAttainingDeltab A f eps jstar
      refine ⟨DeltaA, Deltab, ?_, ?_, ?_⟩
      · intro i j
        rw [higham21Theorem21_1DataAttainingDeltaA_abs
          A E b eps jstar heps hE i j]
      · intro i
        rw [higham21Theorem21_1DataAttainingDeltab_abs
          A f eps jstar heps hf i]
      · have hM : M = right jstar := max_eq_right hleftRight
        calc
          eps * M =
              abs (higham21Theorem21_1DataSource A DeltaA b Deltab jstar) := by
            rw [hM]
            change eps * right jstar =
              abs (higham21Theorem21_1DataSource A
                (higham21Theorem21_1DataAttainingDeltaA
                  A E b eps jstar) b
                (higham21Theorem21_1DataAttainingDeltab
                  A f eps jstar) jstar)
            rw [higham21Theorem21_1DataAttainers_source_coord]
            rw [abs_of_nonneg (mul_nonneg heps (hright jstar))]
          _ <= vecNorm2
              (higham21Theorem21_1DataSource A DeltaA b Deltab) :=
            abs_coord_le_vecNorm2 _ jstar
          _ <= vecNorm2
              (higham21Eq21_7FirstOrder A DeltaA b Deltab
                (undetGramNonsingInv A)) :=
            higham21_theorem21_1_dataSource_vecNorm2_le_firstOrder
              A DeltaA b Deltab hdet
  rcases hselected with ⟨DeltaA, Deltab, hDeltaA, hDeltab, hsource⟩
  refine ⟨DeltaA, Deltab, hDeltaA, hDeltab, ?_⟩
  have hsource_lp :
      eps * M <= c *
        complexVecLpNorm (ENNReal.ofReal p)
          (realVecToComplex
            (higham21Eq21_7FirstOrder A DeltaA b Deltab
              (undetGramNonsingInv A))) :=
    hsource.trans (by
      simpa [c] using
        (higham21_vecNorm2_le_holderFactor_mul_lpNorm hn hp
          (higham21Eq21_7FirstOrder A DeltaA b Deltab
            (undetGramNonsingInv A))))
  calc
    eps * complexVecLpNorm (ENNReal.ofReal p)
        (realVecToComplex (higham21Theorem21_1Majorant A E b f)) =
        eps * complexVecLpNorm (ENNReal.ofReal p)
          (realVecToComplex total) := by rfl
    _ <= (2 * np) * (eps * M) := hscaled_total
    _ <= (2 * np) *
        (c * complexVecLpNorm (ENNReal.ofReal p)
          (realVecToComplex
            (higham21Eq21_7FirstOrder A DeltaA b Deltab
              (undetGramNonsingInv A)))) :=
      mul_le_mul_of_nonneg_left hsource_lp
        (mul_nonneg (by norm_num) hnp_nonneg)
    _ = higham21Theorem21_1HolderAttainmentFactor n p *
        complexVecLpNorm (ENNReal.ofReal p)
          (realVecToComplex
            (higham21Eq21_7FirstOrder A DeltaA b Deltab
              (undetGramNonsingInv A))) := by
      simp [higham21Theorem21_1HolderAttainmentFactor, np, c]
      ring

/-- Two-sided first-order content of Higham's Theorem 21.1 for every finite
    Holder `p`-norm: the printed majorant is an upper bound for all admissible
    perturbations and is attained by explicit sign perturbations up to the
    displayed dimension factor. -/
theorem higham21_theorem21_1_holder_firstOrder_upper_and_attainment
    {m n : Nat} (hn : 0 < n) {p : Real} (hp : 1 <= p)
    (A E : Fin m -> Fin n -> Real) (b f : Fin m -> Real)
    (eps : Real)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0)
    (heps : 0 <= eps) (hE : forall i j, 0 <= E i j)
    (hf : forall i, 0 <= f i) :
    (forall (DeltaA : Fin m -> Fin n -> Real) (Deltab : Fin m -> Real),
      (forall i j, abs (DeltaA i j) <= eps * E i j) ->
      (forall i, abs (Deltab i) <= eps * f i) ->
      complexVecLpNorm (ENNReal.ofReal p)
          (realVecToComplex
            (higham21Eq21_7FirstOrder A DeltaA b Deltab
              (undetGramNonsingInv A))) <=
        eps * complexVecLpNorm (ENNReal.ofReal p)
          (realVecToComplex (higham21Theorem21_1Majorant A E b f))) /\
    (exists DeltaA : Fin m -> Fin n -> Real, exists Deltab : Fin m -> Real,
      (forall i j, abs (DeltaA i j) <= eps * E i j) /\
      (forall i, abs (Deltab i) <= eps * f i) /\
      eps * complexVecLpNorm (ENNReal.ofReal p)
          (realVecToComplex (higham21Theorem21_1Majorant A E b f)) <=
        higham21Theorem21_1HolderAttainmentFactor n p *
          complexVecLpNorm (ENNReal.ofReal p)
            (realVecToComplex
              (higham21Eq21_7FirstOrder A DeltaA b Deltab
                (undetGramNonsingInv A)))) := by
  constructor
  · intro DeltaA Deltab hDeltaA hDeltab
    exact higham21_theorem21_1_holder_firstOrder_upper_bound hp
      A DeltaA E b Deltab f eps hdet heps hE hf hDeltaA hDeltab
  · exact higham21_theorem21_1_holder_firstOrder_attainability
      hn hp A E b f eps hdet heps hE hf

end NumStability
