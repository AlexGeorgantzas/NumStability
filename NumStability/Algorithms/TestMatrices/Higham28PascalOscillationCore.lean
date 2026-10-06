import NumStability.Algorithms.TestMatrices.Higham28PascalOscillation

namespace NumStability

open scoped BigOperators

theorem pascalOscillation_exists_positive_dominant_eigenvector
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (A : Matrix α α ℝ) (hA : ∀ i j, 0 < A i j) :
    ∃ ρ : ℝ, ∃ p : α → ℝ,
      (∀ i, 0 < p i) ∧
      Matrix.mulVec A p = ρ • p ∧
      ∀ (μ : ℝ) (x : α → ℝ), x ≠ 0 →
        Matrix.mulVec A x = μ • x → |μ| ≤ ρ := by
  classical
  let q := Fintype.card α
  let e : α ≃ Fin q := Fintype.equivFin α
  let B : RSqMat q := fun i j => A (e.symm i) (e.symm j)
  have hq : 0 < q := Fintype.card_pos
  have hBpos : ∀ i j, 0 < B i j := fun i j => hA _ _
  have hBirred : Matrix.IsIrreducible
      (Matrix.of B : Matrix (Fin q) (Fin q) ℝ) :=
    ch7_matrix_isIrreducible_of_pos_entries B hBpos
  obtain ⟨mu, _z, _x, y, _hz_ne, _hx_ne, _hx_nonneg, hy_pos,
      _heig_complex, _hrad, _hsubx, heig_real⟩ :=
    ch7_exists_spectralRadius_attaining_positive_eigenvector hq B hBirred
  let ρ : ℝ := ‖mu‖
  let p : α → ℝ := fun i => y (e i)
  refine ⟨ρ, p, fun i => hy_pos (e i), ?_, ?_⟩
  · funext i
    have hi := heig_real (e i)
    simp only [matMulVec, B, e, Equiv.symm_apply_apply,
      Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, ρ, p] at hi ⊢
    rw [← e.sum_comp (fun j => A i (e.symm j) * y j)] at hi
    simpa using hi
  · intro μ x hx heigx
    let z : CVec q := fun j => (x (e.symm j) : ℂ)
    have hz : z ≠ 0 := by
      intro hz0
      apply hx
      funext i
      have hi := congrFun hz0 (e i)
      simp [z] at hi
      exact hi
    have heigz : ∀ i : Fin q,
        complexMatrixVecMul (realRectToCMatrix B) z i = (μ : ℂ) * z i := by
      intro j
      have hj := congrFun heigx (e.symm j)
      have hjc := congrArg (fun r : ℝ => (r : ℂ)) hj
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hjc
      simp only [complexMatrixVecMul, realRectToCMatrix, B, z,
        Complex.ofReal_sum, Complex.ofReal_mul]
      rw [← e.sum_comp (fun i =>
        (A (e.symm j) (e.symm i) : ℂ) * (x (e.symm i) : ℂ))]
      simpa using hjc
    have hdom := ch7_complex_eigenvalue_norm_le_of_positive_real_eigenvector
      hq B ρ y (μ : ℂ) z (fun i j => le_of_lt (hBpos i j)) hy_pos
      heig_real hz heigz
    simpa [ρ, Complex.norm_real] using hdom

theorem pascalOscillation_positiveMatrix_eigenvector_unique_up_to_smul
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (A : Matrix α α ℝ) (ρ : ℝ)
    (p : α → ℝ) (hp : ∀ i, 0 < p i)
    (hA : ∀ i j, 0 < A i j)
    (heigp : Matrix.mulVec A p = ρ • p)
    (x : α → ℝ) (heigx : Matrix.mulVec A x = ρ • x) :
    ∃ t : ℝ, x = t • p := by
  let ratio : α → ℝ := fun i => x i / p i
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max ratio
  let t := ratio i₀
  let z : α → ℝ := t • p - x
  have hz_nonneg : ∀ i, 0 ≤ z i := by
    intro i
    change 0 ≤ t * p i - x i
    rw [sub_nonneg]
    apply (div_le_iff₀ (hp i)).mp
    exact hi₀ i
  have hz_i₀ : z i₀ = 0 := by
    change t * p i₀ - x i₀ = 0
    dsimp [t, ratio]
    rw [div_mul_cancel₀ _ (hp i₀).ne']
    ring
  have heigz : Matrix.mulVec A z = ρ • z := by
    rw [show z = t • p - x by rfl, Matrix.mulVec_sub,
      Matrix.mulVec_smul, heigp, heigx]
    module
  have hz_zero : z = 0 := by
    by_contra hz
    have hex : ∃ j, z j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hz (funext h)
    obtain ⟨j, hj⟩ := hex
    have hzj : 0 < z j := lt_of_le_of_ne (hz_nonneg j) (Ne.symm hj)
    have hAz : 0 < Matrix.mulVec A z i₀ := by
      simp only [Matrix.mulVec, dotProduct]
      apply Finset.sum_pos'
      · intro q _
        exact mul_nonneg (le_of_lt (hA i₀ q)) (hz_nonneg q)
      · exact ⟨j, Finset.mem_univ j, mul_pos (hA i₀ j) hzj⟩
    have heigz_i := congrFun heigz i₀
    simp only [Pi.smul_apply, smul_eq_mul, hz_i₀, mul_zero] at heigz_i
    exact (ne_of_gt hAz) heigz_i
  refine ⟨t, ?_⟩
  have := sub_eq_zero.mp hz_zero
  exact this.symm

end NumStability

namespace NumStability

open scoped BigOperators
open Set


/-- Replace the final index `i` of `0, …, i` by `i+1`. -/
def pascalOscillationPascalAdjacentAlternateEmbedding {n : ℕ} (i : Fin n) :
    Fin (i.val + 1) ↪o Fin (n + 1) :=
  OrderEmbedding.ofStrictMono
    (fun j =>
      if h : j.val < i.val then
        (⟨j.val, by omega⟩ : Fin (n + 1))
      else
        (⟨i.val + 1, by omega⟩ : Fin (n + 1)))
    (by
      intro a b hab
      change a.val < b.val at hab
      dsimp
      split <;> split <;>
        simp only [Fin.mk_lt_mk, Fin.val_mk] <;> omega)

noncomputable def pascalOscillationPascalAdjacentAlternatePowerset {n : ℕ} (i : Fin n) :
    Set.powersetCard (Fin (n + 1)) (i.val + 1) :=
  Set.powersetCard.ofFinEmbEquiv (pascalOscillationPascalAdjacentAlternateEmbedding i)

noncomputable def pascalOscillationPascalEigenvalueSubsetProduct
    (n k : ℕ) (s : Set.powersetCard (Fin n) k) : ℝ :=
  ∏ j : Fin k, pascalSortedEigenvalue n
    (Set.powersetCard.ofFinEmbEquiv.symm s j)

theorem pascalOscillationPascalAdjacentAlternatePowerset_ne_initial
    {n : ℕ} (i : Fin n) :
    pascalOscillationPascalAdjacentAlternatePowerset i ≠
      initialPowerset (show i.val + 1 ≤ n + 1 by omega) := by
  intro h
  have hemb := congrArg Set.powersetCard.ofFinEmbEquiv.symm h
  have happ := DFunLike.congr_fun hemb (Fin.last i.val)
  have hval := congrArg Fin.val happ
  simp [pascalOscillationPascalAdjacentAlternatePowerset,
    pascalOscillationPascalAdjacentAlternateEmbedding, initialPowerset] at hval

theorem pascalOscillationPascalAdjacentAlternateProduct_eq_of_eq
    {n : ℕ} (i : Fin n)
    (hlambda : pascalSortedEigenvalue (n + 1) i.castSucc =
      pascalSortedEigenvalue (n + 1) i.succ) :
    pascalOscillationPascalEigenvalueSubsetProduct (n + 1) (i.val + 1)
        (pascalOscillationPascalAdjacentAlternatePowerset i) =
      pascalLeadingEigenvalueProduct (n + 1) (i.val + 1)
        (show i.val + 1 ≤ n + 1 by omega) := by
  unfold pascalOscillationPascalEigenvalueSubsetProduct pascalLeadingEigenvalueProduct
  apply Finset.prod_congr rfl
  intro j _
  simp only [pascalOscillationPascalAdjacentAlternatePowerset,
    Equiv.symm_apply_apply]
  by_cases hj : j.val < i.val
  · apply congrArg (pascalSortedEigenvalue (n + 1))
    apply Fin.ext
    simp [pascalOscillationPascalAdjacentAlternateEmbedding, hj]
  · have hji : j.val = i.val := by omega
    calc
      pascalSortedEigenvalue (n + 1)
          (pascalOscillationPascalAdjacentAlternateEmbedding i j) =
        pascalSortedEigenvalue (n + 1) i.succ := by
          apply congrArg (pascalSortedEigenvalue (n + 1))
          apply Fin.ext
          simp [pascalOscillationPascalAdjacentAlternateEmbedding, hj]
      _ = pascalSortedEigenvalue (n + 1) i.castSucc := hlambda.symm
      _ = pascalSortedEigenvalue (n + 1)
          (Fin.castLE (show i.val + 1 ≤ n + 1 by omega) j) := by
            apply congrArg (pascalSortedEigenvalue (n + 1))
            apply Fin.ext
            simpa using hji.symm

theorem pascalOscillation_compoundMatrix_sortedEigenvalueDiagonal
    {n k : ℕ} (s t : Set.powersetCard (Fin n) k) :
    compoundMatrix n k (pascalSortedEigenvalueDiagonal n) s t =
      if s = t then pascalOscillationPascalEigenvalueSubsetProduct n k s else 0 := by
  classical
  split
  · next hst =>
    subst t
    rw [compoundMatrix_apply]
    have hmatrix : (fun i j : Fin k =>
        pascalSortedEigenvalueDiagonal n
          (Set.powersetCard.ofFinEmbEquiv.symm s i)
          (Set.powersetCard.ofFinEmbEquiv.symm s j)) =
        Matrix.diagonal (fun j : Fin k =>
          pascalSortedEigenvalue n
            (Set.powersetCard.ofFinEmbEquiv.symm s j)) := by
      ext i j
      simp [pascalSortedEigenvalueDiagonal, Matrix.diagonal_apply]
    rw [hmatrix, Matrix.det_diagonal]
    rfl
  · next hst =>
    rw [compoundMatrix_apply]
    obtain ⟨a, ha0, ha1⟩ :=
      (Set.powersetCard.exists_mem_notMem_iff_ne t s).mp (Ne.symm hst)
    obtain ⟨j, rfl⟩ :=
      (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem t a).mpr ha0
    apply Matrix.det_eq_zero_of_column_eq_zero j
    intro i
    simp only [pascalSortedEigenvalueDiagonal, Matrix.diagonal_apply]
    split
    · next hij =>
      exfalso
      apply ha1
      rw [← hij]
      apply (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s _).mp
      exact ⟨i, rfl⟩
    · rfl

theorem pascalOscillationPascalEigenvalueSubsetProduct_le_leading
    {n k : ℕ} (hkn : k ≤ n)
    (s : Set.powersetCard (Fin n) k) :
    pascalOscillationPascalEigenvalueSubsetProduct n k s ≤
      pascalLeadingEigenvalueProduct n k hkn := by
  unfold pascalOscillationPascalEigenvalueSubsetProduct pascalLeadingEigenvalueProduct
  apply Finset.prod_le_prod
  · intro j _
    exact le_of_lt (pascalSortedEigenvalue_pos
      (Set.powersetCard.ofFinEmbEquiv.symm s j))
  · intro j _
    apply pascalSortedEigenvalue_antitone
    apply Fin.le_iff_val_le_val.mpr
    have hindex : ∀ {m n : ℕ} (f : Fin m → Fin n), StrictMono f →
        ∀ a, a.val ≤ (f a).val := by
      intro m
      induction m with
      | zero =>
        intro n f hf a
        exact Fin.elim0 a
      | succ m ih =>
        intro n f hf a
        refine Fin.cases ?_ (fun b => ?_) a
        · exact Nat.zero_le _
        · have hprev := ih (fun c => f c.castSucc)
            (hf.comp (Fin.strictMono_castLE (Nat.le_succ m))) b
          have hstep := hf (show b.castSucc < b.succ from Fin.castSucc_lt_succ)
          simp only [Fin.val_succ] at hstep ⊢
          omega
    exact hindex _ (Set.powersetCard.ofFinEmbEquiv.symm s).strictMono j

theorem pascalOscillation_pascalLeadingEigenvalueProduct_pos
    {n k : ℕ} (hkn : k ≤ n) :
    0 < pascalLeadingEigenvalueProduct n k hkn := by
  unfold pascalLeadingEigenvalueProduct
  exact Finset.prod_pos fun j _ =>
    pascalSortedEigenvalue_pos (Fin.castLE hkn j)

theorem pascalOscillation_pascalLeadingPlucker_ne_zero
    {n k : ℕ} (hkn : k ≤ n) :
    pascalLeadingPlucker n k hkn ≠ 0 := by
  intro hd
  have horth := compoundMatrix_sortedEigenvectorMatrix_transpose_mul_self n k
  have hentry := congrArg
    (fun M : Matrix (Set.powersetCard (Fin n) k)
        (Set.powersetCard (Fin n) k) ℝ =>
      M (initialPowerset hkn) (initialPowerset hkn)) horth
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
    ↓reduceIte] at hentry
  have hcol : ∀ s : Set.powersetCard (Fin n) k,
      compoundMatrix n k (pascalSortedEigenvectorMatrix n) s
        (initialPowerset hkn) = 0 := by
    intro s
    have hs := congrFun hd s
    simpa [pascalLeadingPlucker] using hs
  simp [hcol] at hentry

theorem pascalOscillation_compoundMatrix_pascal_mul_sortedEigenvectorMatrix
    (n k : ℕ) :
    compoundMatrix n k (pascalMatrix n) *
        compoundMatrix n k (pascalSortedEigenvectorMatrix n) =
      compoundMatrix n k (pascalSortedEigenvectorMatrix n) *
        compoundMatrix n k (pascalSortedEigenvalueDiagonal n) := by
  calc
    compoundMatrix n k (pascalMatrix n) *
        compoundMatrix n k (pascalSortedEigenvectorMatrix n) =
      compoundMatrix n k
        (pascalMatrix n * pascalSortedEigenvectorMatrix n) := by
          rw [compoundMatrix_mul]
    _ = compoundMatrix n k
        (pascalSortedEigenvectorMatrix n *
          pascalSortedEigenvalueDiagonal n) := by
            rw [pascalMatrix_mul_sortedEigenvectorMatrix]
    _ = compoundMatrix n k (pascalSortedEigenvectorMatrix n) *
        compoundMatrix n k (pascalSortedEigenvalueDiagonal n) := by
          rw [compoundMatrix_mul]

noncomputable def pascalOscillationPascalSortedPlucker
    (n k : ℕ) (t : Set.powersetCard (Fin n) k) :
    Set.powersetCard (Fin n) k → ℝ :=
  fun s => compoundMatrix n k (pascalSortedEigenvectorMatrix n) s t

theorem pascalOscillationPascalSortedPlucker_ne_zero
    {n k : ℕ} (t : Set.powersetCard (Fin n) k) :
    pascalOscillationPascalSortedPlucker n k t ≠ 0 := by
  intro hx
  have horth := compoundMatrix_sortedEigenvectorMatrix_transpose_mul_self n k
  have hentry := congrArg
    (fun M : Matrix (Set.powersetCard (Fin n) k)
        (Set.powersetCard (Fin n) k) ℝ => M t t) horth
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
    ↓reduceIte] at hentry
  have hcol : ∀ s : Set.powersetCard (Fin n) k,
      compoundMatrix n k (pascalSortedEigenvectorMatrix n) s t = 0 := by
    intro s
    have hs := congrFun hx s
    simpa [pascalOscillationPascalSortedPlucker] using hs
  simp [hcol] at hentry

theorem pascalOscillation_compoundMatrix_pascal_mul_sortedPlucker
    {n k : ℕ} (t : Set.powersetCard (Fin n) k) :
    Matrix.mulVec (compoundMatrix n k (pascalMatrix n))
        (pascalOscillationPascalSortedPlucker n k t) =
      pascalOscillationPascalEigenvalueSubsetProduct n k t •
        pascalOscillationPascalSortedPlucker n k t := by
  have hmat := pascalOscillation_compoundMatrix_pascal_mul_sortedEigenvectorMatrix n k
  funext s
  have hs := congrArg
    (fun M : Matrix (Set.powersetCard (Fin n) k)
      (Set.powersetCard (Fin n) k) ℝ => M s t) hmat
  simp only [Matrix.mul_apply] at hs
  simpa [Matrix.mulVec, dotProduct, pascalOscillationPascalSortedPlucker,
    pascalOscillation_compoundMatrix_sortedEigenvalueDiagonal,
    Pi.smul_apply, smul_eq_mul, mul_comm] using hs

theorem pascalOscillation_compoundSortedCoefficient_eigen
    {n k : ℕ} {ρ : ℝ}
    (p : Set.powersetCard (Fin n) k → ℝ)
    (hp : Matrix.mulVec (compoundMatrix n k (pascalMatrix n)) p = ρ • p) :
    Matrix.mulVec (compoundMatrix n k (pascalSortedEigenvalueDiagonal n))
        (Matrix.mulVec
          (compoundMatrix n k (pascalSortedEigenvectorMatrix n)).transpose p) =
      ρ • (Matrix.mulVec
        (compoundMatrix n k (pascalSortedEigenvectorMatrix n)).transpose p) := by
  let C := compoundMatrix n k (pascalMatrix n)
  let Q := compoundMatrix n k (pascalSortedEigenvectorMatrix n)
  let D := compoundMatrix n k (pascalSortedEigenvalueDiagonal n)
  have hCQ : C * Q = Q * D := pascalOscillation_compoundMatrix_pascal_mul_sortedEigenvectorMatrix n k
  have hQtQ : Q.transpose * Q = 1 :=
    compoundMatrix_sortedEigenvectorMatrix_transpose_mul_self n k
  have hQQt : Q * Q.transpose = 1 :=
    compoundMatrix_sortedEigenvectorMatrix_mul_transpose n k
  have hDQ : D * Q.transpose = Q.transpose * C := by
    calc
      D * Q.transpose = 1 * D * Q.transpose := by rw [Matrix.one_mul]
      _ = (Q.transpose * Q) * D * Q.transpose := by rw [hQtQ]
      _ = Q.transpose * (Q * D) * Q.transpose := by
        noncomm_ring
      _ = Q.transpose * (C * Q) * Q.transpose := by rw [hCQ]
      _ = Q.transpose * C * (Q * Q.transpose) := by noncomm_ring
      _ = Q.transpose * C := by rw [hQQt, Matrix.mul_one]
  change Matrix.mulVec D (Matrix.mulVec Q.transpose p) =
    ρ • Matrix.mulVec Q.transpose p
  calc
    Matrix.mulVec D (Matrix.mulVec Q.transpose p) =
        Matrix.mulVec (D * Q.transpose) p := Matrix.mulVec_mulVec _ _ _
    _ = Matrix.mulVec (Q.transpose * C) p := by rw [hDQ]
    _ = Matrix.mulVec Q.transpose (Matrix.mulVec C p) :=
      (Matrix.mulVec_mulVec _ _ _).symm
    _ = Matrix.mulVec Q.transpose (ρ • p) := by rw [hp]
    _ = ρ • Matrix.mulVec Q.transpose p := by rw [Matrix.mulVec_smul]

theorem pascalOscillation_pascalLeadingPlucker_same_sign
    {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ∀ s : Set.powersetCard (Fin n) k,
        0 < ε * pascalLeadingPlucker n k hkn s := by
  classical
  let α := Set.powersetCard (Fin n) k
  let C : Matrix α α ℝ := compoundMatrix n k (pascalMatrix n)
  let Q : Matrix α α ℝ :=
    compoundMatrix n k (pascalSortedEigenvectorMatrix n)
  let D : Matrix α α ℝ :=
    compoundMatrix n k (pascalSortedEigenvalueDiagonal n)
  let μ := pascalLeadingEigenvalueProduct n k hkn
  let d : α → ℝ := pascalLeadingPlucker n k hkn
  letI : Nonempty α := ⟨initialPowerset hkn⟩
  have hCpos : ∀ s t, 0 < C s t := fun s t =>
    compoundMatrix_pascal_pos hk s t
  obtain ⟨ρ, p, hp, heigp, hdominant⟩ :=
    pascalOscillation_exists_positive_dominant_eigenvector C hCpos
  have hd_ne : d ≠ 0 := pascalOscillation_pascalLeadingPlucker_ne_zero hkn
  have hμpos : 0 < μ := pascalOscillation_pascalLeadingEigenvalueProduct_pos hkn
  have heigd : Matrix.mulVec C d = μ • d :=
    compoundMatrix_pascal_mul_leadingPlucker hkn
  have hμ_le_ρ : μ ≤ ρ := by
    have h := hdominant μ d hd_ne heigd
    simpa [abs_of_pos hμpos] using h
  let a : α → ℝ := Matrix.mulVec Q.transpose p
  have ha_eig : Matrix.mulVec D a = ρ • a := by
    exact pascalOscillation_compoundSortedCoefficient_eigen p heigp
  have ha_ne : a ≠ 0 := by
    intro ha
    have hQQt : Q * Q.transpose = 1 :=
      compoundMatrix_sortedEigenvectorMatrix_mul_transpose n k
    have hp0 : p = 0 := by
      calc
        p = Matrix.mulVec 1 p := by simp
        _ = Matrix.mulVec (Q * Q.transpose) p := by rw [hQQt]
        _ = Matrix.mulVec Q (Matrix.mulVec Q.transpose p) :=
          (Matrix.mulVec_mulVec _ _ _).symm
        _ = Matrix.mulVec Q a := rfl
        _ = 0 := by rw [ha]; simp
    have hi := congrFun hp0 (initialPowerset hkn)
    exact (ne_of_gt (hp (initialPowerset hkn))) hi
  obtain ⟨s, hs⟩ : ∃ s, a s ≠ 0 := by
    by_contra h
    push_neg at h
    exact ha_ne (funext h)
  have heq : pascalOscillationPascalEigenvalueSubsetProduct n k s * a s = ρ * a s := by
    have hsrow := congrFun ha_eig s
    simpa [D, Matrix.mulVec, dotProduct,
      pascalOscillation_compoundMatrix_sortedEigenvalueDiagonal,
      Pi.smul_apply, smul_eq_mul] using hsrow
  have hρeq : ρ = pascalOscillationPascalEigenvalueSubsetProduct n k s := by
    have hprod : pascalOscillationPascalEigenvalueSubsetProduct n k s = ρ :=
      mul_right_cancel₀ hs heq
    exact hprod.symm
  have hρ_le_μ : ρ ≤ μ := by
    rw [hρeq]
    exact pascalOscillationPascalEigenvalueSubsetProduct_le_leading hkn s
  have hρμ : ρ = μ := le_antisymm hρ_le_μ hμ_le_ρ
  have heigpμ : Matrix.mulVec C p = μ • p := by simpa [hρμ] using heigp
  obtain ⟨t, hdt⟩ := pascalOscillation_positiveMatrix_eigenvector_unique_up_to_smul
    C μ p hp hCpos heigpμ d heigd
  have ht : t ≠ 0 := by
    intro ht0
    apply hd_ne
    rw [hdt, ht0]
    simp
  rcases lt_or_gt_of_ne ht with htneg | htpos
  · refine ⟨-1, Or.inr rfl, ?_⟩
    intro s
    have hds := congrFun hdt s
    simp only [Pi.smul_apply, smul_eq_mul] at hds
    change 0 < -1 * d s
    rw [hds]
    convert mul_pos (neg_pos.mpr htneg) (hp s) using 1 <;> ring
  · refine ⟨1, Or.inl rfl, ?_⟩
    intro s
    have hds := congrFun hdt s
    simp only [Pi.smul_apply, smul_eq_mul] at hds
    change 0 < 1 * d s
    rw [hds, one_mul]
    exact mul_pos htpos (hp s)

theorem pascalOscillation_pascalSortedEigenvalue_strictAdjacent
    {n : ℕ} (i : Fin n) :
    pascalSortedEigenvalue (n + 1) i.succ <
      pascalSortedEigenvalue (n + 1) i.castSucc := by
  classical
  have hle : pascalSortedEigenvalue (n + 1) i.succ ≤
      pascalSortedEigenvalue (n + 1) i.castSucc :=
    pascalSortedEigenvalue_antitone (Fin.castSucc_le_succ i)
  apply lt_of_le_of_ne hle
  intro heq
  have hlambda : pascalSortedEigenvalue (n + 1) i.castSucc =
      pascalSortedEigenvalue (n + 1) i.succ := heq.symm
  let k := i.val + 1
  have hk : 0 < k := by omega
  have hkn : k ≤ n + 1 := by omega
  let α := Set.powersetCard (Fin (n + 1)) k
  let C : Matrix α α ℝ := compoundMatrix (n + 1) k (pascalMatrix (n + 1))
  let Q : Matrix α α ℝ :=
    compoundMatrix (n + 1) k (pascalSortedEigenvectorMatrix (n + 1))
  let μ := pascalLeadingEigenvalueProduct (n + 1) k hkn
  let init : α := initialPowerset hkn
  let alt : α := pascalOscillationPascalAdjacentAlternatePowerset i
  letI : Nonempty α := ⟨init⟩
  let d : α → ℝ := pascalLeadingPlucker (n + 1) k hkn
  let x : α → ℝ := pascalOscillationPascalSortedPlucker (n + 1) k alt
  have halt : alt ≠ init := by
    exact pascalOscillationPascalAdjacentAlternatePowerset_ne_initial i
  obtain ⟨ε, hε, hεd⟩ := pascalOscillation_pascalLeadingPlucker_same_sign hk hkn
  let p : α → ℝ := fun s => ε * d s
  have hp : ∀ s, 0 < p s := hεd
  have hCpos : ∀ s t, 0 < C s t := fun s t =>
    compoundMatrix_pascal_pos hk s t
  have heigd : Matrix.mulVec C d = μ • d :=
    compoundMatrix_pascal_mul_leadingPlucker hkn
  have heigp : Matrix.mulVec C p = μ • p := by
    have hpdef : p = ε • d := by
      funext s
      simp [p]
    rw [hpdef, Matrix.mulVec_smul, heigd]
    module
  have hprod : pascalOscillationPascalEigenvalueSubsetProduct (n + 1) k alt = μ := by
    exact pascalOscillationPascalAdjacentAlternateProduct_eq_of_eq i hlambda
  have heigx : Matrix.mulVec C x = μ • x := by
    have hx := pascalOscillation_compoundMatrix_pascal_mul_sortedPlucker alt
    simpa [C, x, hprod] using hx
  obtain ⟨t, hxt⟩ := pascalOscillation_positiveMatrix_eigenvector_unique_up_to_smul
    C μ p hp hCpos heigp x heigx
  have hQtQ : Q.transpose * Q = 1 :=
    compoundMatrix_sortedEigenvectorMatrix_transpose_mul_self (n + 1) k
  have hleft : Matrix.mulVec Q.transpose x alt = 1 := by
    have hentry := congrArg (fun M : Matrix α α ℝ => M alt alt) hQtQ
    simpa [Q, x, pascalOscillationPascalSortedPlucker,
      Matrix.mulVec, dotProduct, Matrix.mul_apply] using hentry
  have hright : Matrix.mulVec Q.transpose p alt = 0 := by
    have hentry := congrArg (fun M : Matrix α α ℝ => M alt init) hQtQ
    have hentry0 : (Q.transpose * Q) alt init = 0 := by
      rw [hQtQ]
      simp [halt]
    have hpdef : p = ε • d := by
      funext s
      simp [p]
    rw [hpdef, Matrix.mulVec_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    change ε * (∑ s, Q s alt * d s) = 0
    have hdcol : ∀ s, d s = Q s init := by
      intro s
      rfl
    simp only [hdcol]
    have hsum : (∑ s, Q s alt * Q s init) = 0 := by
      simpa [Matrix.mul_apply] using hentry0
    rw [hsum, mul_zero]
  have hcomp := congrArg (fun v : α → ℝ => Matrix.mulVec Q.transpose v alt) hxt
  change Matrix.mulVec Q.transpose x alt =
    Matrix.mulVec Q.transpose (t • p) alt at hcomp
  rw [hleft] at hcomp
  simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, hright,
    mul_zero] at hcomp
  exact one_ne_zero hcomp

/-- Higham, Section 28.4, p. 520: the eigenvalues of the symmetric Pascal
matrix are strictly decreasing in the chosen spectral ordering. -/
theorem pascalSortedEigenvalue_strictAnti (n : ℕ) :
    StrictAnti (pascalSortedEigenvalue n) := by
  cases n with
  | zero =>
    intro i
    exact Fin.elim0 i
  | succ n =>
    rw [Fin.strictAnti_iff_succ_lt]
    exact pascalOscillation_pascalSortedEigenvalue_strictAdjacent

/-- Alternate the signs of a Boolean word, beginning with the original sign
at row zero.  The recursive presentation makes the zero-compatible variation
identity transparent. -/
def pascalOscillationCheckerBool : {n : ℕ} →
    (Fin (n + 1) → Bool) → Fin (n + 1) → Bool
  | 0, s => s
  | n + 1, s => Fin.cases (s 0)
      (fun i => !(pascalOscillationCheckerBool (fun j : Fin (n + 1) => s j.succ) i))

@[simp] theorem pascalOscillationCheckerBool_zero {n : ℕ}
    (s : Fin (n + 1) → Bool) : pascalOscillationCheckerBool s 0 = s 0 := by
  cases n <;> rfl

@[simp] theorem pascalOscillationCheckerBool_succ {n : ℕ}
    (s : Fin (n + 2) → Bool) (i : Fin (n + 1)) :
    pascalOscillationCheckerBool s i.succ =
      !(pascalOscillationCheckerBool (fun j : Fin (n + 1) => s j.succ) i) := by
  rfl

theorem boolSignChangeCount_not {n : ℕ}
    (s : Fin (n + 1) → Bool) :
    boolSignChangeCount (fun i => !(s i)) =
      boolSignChangeCount s := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [boolSignChangeCount, boolSignChangeCount]
      have htail := ih (fun i : Fin (n + 1) => s i.succ)
      rw [← htail]
      congr 1
      cases h0 : s 0 <;> cases h1 : s 1 <;> simp [h0, h1]

theorem pascalOscillationCheckerBool_count_add {n : ℕ}
    (s : Fin (n + 1) → Bool) :
    boolSignChangeCount (pascalOscillationCheckerBool s) +
      boolSignChangeCount s = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [boolSignChangeCount, boolSignChangeCount]
      simp only [pascalOscillationCheckerBool_zero, pascalOscillationCheckerBool_succ]
      have hnot := boolSignChangeCount_not
        (pascalOscillationCheckerBool (fun i : Fin (n + 1) => s i.succ))
      have htail := ih (fun i : Fin (n + 1) => s i.succ)
      rw [hnot]
      have hc1 : pascalOscillationCheckerBool s 1 = !(s 1) := by
        change pascalOscillationCheckerBool s (Fin.succ 0) = !(s (Fin.succ 0))
        rw [pascalOscillationCheckerBool_succ, pascalOscillationCheckerBool_zero]
      rw [hc1]
      cases h0 : s 0 <;> cases h1 : s 1 <;>
        simp [h0, h1] at htail ⊢ <;> omega

theorem boolSignChangeCount_extract
    {n k : ℕ} (s : Fin (n + 1) → Bool)
    (hcount : k ≤ boolSignChangeCount s) :
    ∃ f : Fin (k + 1) → Fin (n + 1),
      StrictMono f ∧ f 0 = 0 ∧
        ∀ j : Fin k, s (f j.castSucc) ≠ s (f j.succ) := by
  induction n generalizing k with
  | zero =>
    have hk : k = 0 := by
      simpa [boolSignChangeCount] using hcount
    subst k
    refine ⟨fun _ => 0, ?_, rfl, ?_⟩
    · intro a b hab
      omega
    · exact Fin.elim0
  | succ n ih =>
    by_cases hk : k = 0
    · subst k
      refine ⟨fun _ => 0, ?_, rfl, ?_⟩
      · intro a b hab
        omega
      · exact Fin.elim0
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
      let stail : Fin (n + 1) → Bool := fun j => s j.succ
      by_cases hhead : s 0 ≠ s 1
      · have htail : k ≤ boolSignChangeCount stail := by
          change k + 1 ≤ (if s 0 ≠ s 1 then 1 else 0) +
            boolSignChangeCount (fun j : Fin (n + 1) => s j.succ) at hcount
          rw [if_pos hhead] at hcount
          have htail' : k ≤ boolSignChangeCount
              (fun j : Fin (n + 1) => s j.succ) := by omega
          simpa [stail] using htail'
        obtain ⟨f, hfmono, hf0, hfalt⟩ := ih stail htail
        let g : Fin (k + 2) → Fin (n + 2) :=
          Fin.cases 0 (fun j => (f j).succ)
        refine ⟨g, ?_, ?_, ?_⟩
        · rw [Fin.strictMono_iff_lt_succ]
          intro j
          refine Fin.cases ?_ (fun q => ?_) j
          · change 0 < (f 0).succ
            rw [hf0]
            simp
          · simpa [g] using hfmono
              (show q.castSucc < q.succ from Fin.castSucc_lt_succ)
        · simp [g]
        · intro j
          refine Fin.cases ?_ (fun q => ?_) j
          · change s 0 ≠ s ((f 0).succ)
            rw [hf0]
            exact hhead
          · simpa [g, stail] using hfalt q
      · have htail : k + 1 ≤ boolSignChangeCount stail := by
          change k + 1 ≤ (if s 0 ≠ s 1 then 1 else 0) +
            boolSignChangeCount (fun j : Fin (n + 1) => s j.succ) at hcount
          rw [if_neg hhead, zero_add] at hcount
          exact hcount
        obtain ⟨f, hfmono, hf0, hfalt⟩ := ih stail htail
        let g : Fin (k + 2) → Fin (n + 2) :=
          Fin.cases 0 (fun j => (f j.succ).succ)
        refine ⟨g, ?_, ?_, ?_⟩
        · rw [Fin.strictMono_iff_lt_succ]
          intro j
          refine Fin.cases ?_ (fun q => ?_) j
          · change 0 < (f (0 : Fin (k + 1)).succ).succ
            simp
          · simpa [g] using hfmono
              (show q.succ.castSucc < q.succ.succ from Fin.castSucc_lt_succ)
        · simp [g]
        · intro j
          refine Fin.cases ?_ (fun q => ?_) j
          · have hs01 : s 0 = s 1 := by simpa using hhead
            have hfirst := hfalt (0 : Fin (k + 1))
            change s (f 0).succ ≠
              s (f (0 : Fin (k + 1)).succ).succ at hfirst
            rw [hf0] at hfirst
            change s 0 ≠ s (f (0 : Fin (k + 1)).succ).succ
            rwa [hs01]
          · simpa [g, stail] using hfalt q.succ

theorem pascalOscillation_alternatingCofactor_relation
    {N k : ℕ} (B : Fin N → Fin k → ℝ) (c : Fin k)
    (f : Fin (k + 1) → Fin N) :
    (∑ r : Fin (k + 1),
      (-1 : ℝ) ^ (r.val + k) * B (f r) c *
        Matrix.det (fun a b : Fin k => B (f (r.succAbove a)) b)) = 0 := by
  let A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ := fun r j =>
    Fin.lastCases (B (f r) c) (fun q => B (f r) q) j
  have hlast_ne : (Fin.last k : Fin (k + 1)) ≠ c.castSucc := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have hdet0 : Matrix.det A = 0 := by
    apply Matrix.det_zero_of_column_eq hlast_ne
    intro r
    simp [A]
  have hexp := Matrix.det_succ_column A (Fin.last k)
  rw [hdet0] at hexp
  simpa [A, Matrix.submatrix] using hexp.symm

def pascalOscillationBoolToSign (b : Bool) : ℝ := if b then 1 else -1

theorem pascalOscillationBoolToSign_ne {a b : Bool} (h : a ≠ b) :
    pascalOscillationBoolToSign b = -pascalOscillationBoolToSign a := by
  cases a <;> cases b <;> simp_all [pascalOscillationBoolToSign]

@[simp] theorem pascalOscillationBoolToSign_not (b : Bool) :
    pascalOscillationBoolToSign (!b) = -pascalOscillationBoolToSign b := by
  cases b <;> norm_num [pascalOscillationBoolToSign]

theorem pascalOscillationBoolToSign_checker {n : ℕ}
    (s : Fin (n + 1) → Bool) (i : Fin (n + 1)) :
    pascalOscillationBoolToSign (pascalOscillationCheckerBool s i) =
      (-1 : ℝ) ^ i.val * pascalOscillationBoolToSign (s i) := by
  induction n with
  | zero =>
      have hi : i = 0 := Fin.eq_zero i
      subst i
      simp
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · rw [pascalOscillationCheckerBool_succ, pascalOscillationBoolToSign_not,
          ih (fun q : Fin (n + 1) => s q.succ) j]
        simp only [Fin.val_succ, pow_succ]
        ring

def pascalOscillationCheckerVector {n : ℕ} (x : Fin (n + 1) → ℝ) :
    Fin (n + 1) → ℝ :=
  fun i => (-1 : ℝ) ^ i.val * x i

theorem pascalOscillationBoolToSign_mul_nonneg_of_completion
    {N : ℕ} {x : Fin N → ℝ} {s : Fin N → Bool}
    (hs : IsSignCompletion x s) (i : Fin N) :
    0 ≤ pascalOscillationBoolToSign (s i) * x i := by
  rcases hs i with ⟨hpos, hneg⟩
  cases hsi : s i with
  | false =>
    have hxi : x i ≤ 0 := by
      by_contra h
      have := hpos (lt_of_not_ge h)
      simp [hsi] at this
    simp [pascalOscillationBoolToSign, hsi, hxi]
  | true =>
    have hxi : 0 ≤ x i := by
      by_contra h
      have := hneg (lt_of_not_ge h)
      simp [hsi] at this
    simp [pascalOscillationBoolToSign, hsi, hxi]

theorem pascalOscillationIsSignCompletion_of_boolToSign_mul_nonneg
    {N : ℕ} {x : Fin N → ℝ} {s : Fin N → Bool}
    (h : ∀ i, 0 ≤ pascalOscillationBoolToSign (s i) * x i) :
    IsSignCompletion x s := by
  intro i
  constructor
  · intro hxi
    cases hsi : s i with
    | false =>
        have hi := h i
        simp [pascalOscillationBoolToSign, hsi] at hi
        exact (not_lt_of_ge hi hxi).elim
    | true => rfl
  · intro hxi
    cases hsi : s i with
    | false => rfl
    | true =>
        have hi := h i
        simp [pascalOscillationBoolToSign, hsi] at hi
        exact (not_lt_of_ge hi hxi).elim

theorem pascalOscillationCheckerBool_isSignCompletion
    {n : ℕ} {x : Fin (n + 1) → ℝ} {s : Fin (n + 1) → Bool}
    (hs : IsSignCompletion x s) :
    IsSignCompletion (pascalOscillationCheckerVector x) (pascalOscillationCheckerBool s) := by
  apply pascalOscillationIsSignCompletion_of_boolToSign_mul_nonneg
  intro i
  rw [pascalOscillationBoolToSign_checker]
  dsimp [pascalOscillationCheckerVector]
  calc
    0 ≤ pascalOscillationBoolToSign (s i) * x i :=
      pascalOscillationBoolToSign_mul_nonneg_of_completion hs i
    _ = ((-1 : ℝ) ^ i.val * pascalOscillationBoolToSign (s i)) *
        ((-1 : ℝ) ^ i.val * x i) := by
          have hp : (-1 : ℝ) ^ i.val * (-1 : ℝ) ^ i.val = 1 := by
            rw [← pow_add]
            exact Even.neg_one_pow (Even.add_self i.val)
          symm
          calc
            ((-1 : ℝ) ^ i.val * pascalOscillationBoolToSign (s i)) *
                ((-1 : ℝ) ^ i.val * x i) =
              ((-1 : ℝ) ^ i.val * (-1 : ℝ) ^ i.val) *
                (pascalOscillationBoolToSign (s i) * x i) := by ring
            _ = pascalOscillationBoolToSign (s i) * x i := by rw [hp, one_mul]

theorem pascalOscillation_exists_signCompletion {N : ℕ} (x : Fin N → ℝ) :
    ∃ s : Fin N → Bool, IsSignCompletion x s := by
  let s : Fin N → Bool := fun i => if 0 ≤ x i then true else false
  refine ⟨s, ?_⟩
  intro i
  constructor
  · intro hxi
    simp [s, le_of_lt hxi]
  · intro hxi
    simp [s, not_le_of_gt hxi]

theorem pascalOscillationBoolToSign_mul_pos_of_completion
    {N : ℕ} {x : Fin N → ℝ} {s : Fin N → Bool}
    (hs : IsSignCompletion x s) (i : Fin N) (hxi : x i ≠ 0) :
    0 < pascalOscillationBoolToSign (s i) * x i := by
  have hnonneg := pascalOscillationBoolToSign_mul_nonneg_of_completion hs i
  have hsign : pascalOscillationBoolToSign (s i) ≠ 0 := by
    cases s i <;> norm_num [pascalOscillationBoolToSign]
  exact lt_of_le_of_ne hnonneg (Ne.symm (mul_ne_zero hsign hxi))

theorem pascalOscillationBoolToSign_alternating_subsequence
    {N k : ℕ} (s : Fin N → Bool) (f : Fin (k + 1) → Fin N)
    (halt : ∀ j : Fin k, s (f j.castSucc) ≠ s (f j.succ))
    (r : Fin (k + 1)) :
    pascalOscillationBoolToSign (s (f r)) =
      (-1 : ℝ) ^ r.val * pascalOscillationBoolToSign (s (f 0)) := by
  induction r using Fin.induction with
  | zero => simp
  | succ j ih =>
    change pascalOscillationBoolToSign (s (f j.castSucc)) =
      (-1 : ℝ) ^ j.val * pascalOscillationBoolToSign (s (f 0)) at ih
    rw [pascalOscillationBoolToSign_ne (halt j), ih, Fin.val_succ, pow_succ]
    ring

theorem pascalOscillation_tSystem_column_signChangeCount_lt
    {n k : ℕ} (B : Fin (n + 1) → Fin k → ℝ) (c : Fin k)
    (ε : ℝ)
    (hminor : ∀ (r : Fin k → Fin (n + 1)), StrictMono r →
      0 < ε * Matrix.det (fun a b : Fin k => B (r a) b))
    (s : Fin (n + 1) → Bool) (hs : IsSignCompletion (fun i => B i c) s) :
    boolSignChangeCount s < k := by
  by_contra hnot
  have hcount : k ≤ boolSignChangeCount s := by omega
  obtain ⟨f, hfmono, _hf0, hfalt⟩ :=
    boolSignChangeCount_extract s hcount
  have hrel := pascalOscillation_alternatingCofactor_relation B c f
  have hpow (m : ℕ) : (-1 : ℝ) ^ m * (-1 : ℝ) ^ m = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow (Even.add_self m)
  have hsum : (∑ r : Fin (k + 1),
      pascalOscillationBoolToSign (s (f r)) * B (f r) c *
        (ε * Matrix.det (fun a b : Fin k => B (f (r.succAbove a)) b))) = 0 := by
    have hscaled := congrArg
      (fun z : ℝ => (ε * (-1 : ℝ) ^ k * pascalOscillationBoolToSign (s (f 0))) * z) hrel
    dsimp only at hscaled
    rw [mul_zero] at hscaled
    rw [Finset.mul_sum] at hscaled
    calc
      (∑ r : Fin (k + 1),
          pascalOscillationBoolToSign (s (f r)) * B (f r) c *
            (ε * Matrix.det (fun a b : Fin k => B (f (r.succAbove a)) b))) =
        ∑ r : Fin (k + 1),
          (ε * (-1 : ℝ) ^ k * pascalOscillationBoolToSign (s (f 0))) *
            ((-1 : ℝ) ^ (r.val + k) * B (f r) c *
              Matrix.det (fun a b : Fin k => B (f (r.succAbove a)) b)) := by
          apply Finset.sum_congr rfl
          intro r _
          have hsign := pascalOscillationBoolToSign_alternating_subsequence s f hfalt r
          rw [hsign, pow_add]
          calc
            ((-1 : ℝ) ^ r.val * pascalOscillationBoolToSign (s (f 0))) * B (f r) c *
                (ε * Matrix.det (fun a b : Fin k => B (f (r.succAbove a)) b)) =
              1 * (((-1 : ℝ) ^ r.val * pascalOscillationBoolToSign (s (f 0))) * B (f r) c *
                (ε * Matrix.det (fun a b : Fin k => B (f (r.succAbove a)) b))) := by ring
            _ = (((-1 : ℝ) ^ k) * ((-1 : ℝ) ^ k)) *
                (((-1 : ℝ) ^ r.val * pascalOscillationBoolToSign (s (f 0))) * B (f r) c *
                  (ε * Matrix.det (fun a b : Fin k => B (f (r.succAbove a)) b))) := by
                    rw [hpow k]
            _ = (ε * (-1 : ℝ) ^ k * pascalOscillationBoolToSign (s (f 0))) *
                (((-1 : ℝ) ^ r.val * (-1 : ℝ) ^ k) * B (f r) c *
                  Matrix.det (fun a b : Fin k => B (f (r.succAbove a)) b)) := by ring
      _ = 0 := hscaled
  have hallminor : ∀ r : Fin (k + 1),
      0 < ε * Matrix.det (fun a b : Fin k => B (f (r.succAbove a)) b) := by
    intro r
    apply hminor
    exact hfmono.comp (Fin.strictMono_succAbove r)
  have hnonneg : ∀ r : Fin (k + 1),
      0 ≤ pascalOscillationBoolToSign (s (f r)) * B (f r) c *
        (ε * Matrix.det (fun a b : Fin k => B (f (r.succAbove a)) b)) := by
    intro r
    exact mul_nonneg
      (pascalOscillationBoolToSign_mul_nonneg_of_completion hs (f r))
      (le_of_lt (hallminor r))
  have hex : ∃ r : Fin (k + 1), B (f r) c ≠ 0 := by
    by_contra h
    push_neg at h
    let r0 : Fin k → Fin (n + 1) := fun a => f a.castSucc
    have hr0 : StrictMono r0 := hfmono.comp Fin.strictMono_castSucc
    have hpos := hminor r0 hr0
    have hzero : Matrix.det (fun a b : Fin k => B (r0 a) b) = 0 := by
      apply Matrix.det_eq_zero_of_column_eq_zero c
      intro a
      exact h a.castSucc
    rw [hzero, mul_zero] at hpos
    exact (lt_irrefl 0) hpos
  obtain ⟨r, hr⟩ := hex
  have htermpos : 0 < pascalOscillationBoolToSign (s (f r)) * B (f r) c *
      (ε * Matrix.det (fun a b : Fin k => B (f (r.succAbove a)) b)) :=
    mul_pos (pascalOscillationBoolToSign_mul_pos_of_completion hs (f r) hr)
      (hallminor r)
  have hsumpos : 0 < ∑ r : Fin (k + 1),
      pascalOscillationBoolToSign (s (f r)) * B (f r) c *
        (ε * Matrix.det (fun a b : Fin k => B (f (r.succAbove a)) b)) := by
    apply Finset.sum_pos'
    · intro r _
      exact hnonneg r
    · exact ⟨r, Finset.mem_univ r, htermpos⟩
  rw [hsum] at hsumpos
  exact (lt_irrefl 0) hsumpos

/-- A local form of the discrete Chebyshev bound.  The cofactor proof only
needs a common orientation for the `k+1` maximal minors obtained by deleting
one row from the alternating row set extracted from the sign word. -/
theorem pascalOscillation_tSystem_column_signChangeCount_lt_local
    {n k : ℕ} (B : Fin (n + 1) → Fin k → ℝ) (c : Fin k)
    (hminor : ∀ (f : Fin (k + 1) → Fin (n + 1)), StrictMono f →
      ∃ ε : ℝ, ∀ r : Fin (k + 1),
        0 < ε * Matrix.det (fun a b : Fin k => B (f (r.succAbove a)) b))
    (s : Fin (n + 1) → Bool) (hs : IsSignCompletion (fun i => B i c) s) :
    boolSignChangeCount s < k := by
  by_contra hnot
  have hcount : k ≤ boolSignChangeCount s := by omega
  obtain ⟨f, hfmono, _hf0, hfalt⟩ :=
    boolSignChangeCount_extract s hcount
  obtain ⟨ε, hallminor⟩ := hminor f hfmono
  have hrel := pascalOscillation_alternatingCofactor_relation B c f
  have hpow (m : ℕ) : (-1 : ℝ) ^ m * (-1 : ℝ) ^ m = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow (Even.add_self m)
  have hsum : (∑ r : Fin (k + 1),
      pascalOscillationBoolToSign (s (f r)) * B (f r) c *
        (ε * Matrix.det (fun a b : Fin k => B (f (r.succAbove a)) b))) = 0 := by
    have hscaled := congrArg
      (fun z : ℝ => (ε * (-1 : ℝ) ^ k * pascalOscillationBoolToSign (s (f 0))) * z) hrel
    dsimp only at hscaled
    rw [mul_zero] at hscaled
    rw [Finset.mul_sum] at hscaled
    calc
      (∑ r : Fin (k + 1),
          pascalOscillationBoolToSign (s (f r)) * B (f r) c *
            (ε * Matrix.det (fun a b : Fin k => B (f (r.succAbove a)) b))) =
        ∑ r : Fin (k + 1),
          (ε * (-1 : ℝ) ^ k * pascalOscillationBoolToSign (s (f 0))) *
            ((-1 : ℝ) ^ (r.val + k) * B (f r) c *
              Matrix.det (fun a b : Fin k => B (f (r.succAbove a)) b)) := by
          apply Finset.sum_congr rfl
          intro r _
          have hsign := pascalOscillationBoolToSign_alternating_subsequence s f hfalt r
          rw [hsign, pow_add]
          calc
            ((-1 : ℝ) ^ r.val * pascalOscillationBoolToSign (s (f 0))) * B (f r) c *
                (ε * Matrix.det (fun a b : Fin k => B (f (r.succAbove a)) b)) =
              1 * (((-1 : ℝ) ^ r.val * pascalOscillationBoolToSign (s (f 0))) * B (f r) c *
                (ε * Matrix.det (fun a b : Fin k => B (f (r.succAbove a)) b))) := by ring
            _ = (((-1 : ℝ) ^ k) * ((-1 : ℝ) ^ k)) *
                (((-1 : ℝ) ^ r.val * pascalOscillationBoolToSign (s (f 0))) * B (f r) c *
                  (ε * Matrix.det (fun a b : Fin k => B (f (r.succAbove a)) b))) := by
                    rw [hpow k]
            _ = (ε * (-1 : ℝ) ^ k * pascalOscillationBoolToSign (s (f 0))) *
                (((-1 : ℝ) ^ r.val * (-1 : ℝ) ^ k) * B (f r) c *
                  Matrix.det (fun a b : Fin k => B (f (r.succAbove a)) b)) := by ring
      _ = 0 := hscaled
  have hnonneg : ∀ r : Fin (k + 1),
      0 ≤ pascalOscillationBoolToSign (s (f r)) * B (f r) c *
        (ε * Matrix.det (fun a b : Fin k => B (f (r.succAbove a)) b)) := by
    intro r
    exact mul_nonneg
      (pascalOscillationBoolToSign_mul_nonneg_of_completion hs (f r))
      (le_of_lt (hallminor r))
  have hex : ∃ r : Fin (k + 1), B (f r) c ≠ 0 := by
    by_contra h
    push_neg at h
    have hpos := hallminor (Fin.last k)
    have hzero : Matrix.det
        (fun a b : Fin k => B (f ((Fin.last k).succAbove a)) b) = 0 := by
      apply Matrix.det_eq_zero_of_column_eq_zero c
      intro a
      exact h ((Fin.last k).succAbove a)
    rw [hzero, mul_zero] at hpos
    exact (lt_irrefl 0) hpos
  obtain ⟨r, hr⟩ := hex
  have htermpos : 0 < pascalOscillationBoolToSign (s (f r)) * B (f r) c *
      (ε * Matrix.det (fun a b : Fin k => B (f (r.succAbove a)) b)) :=
    mul_pos (pascalOscillationBoolToSign_mul_pos_of_completion hs (f r) hr)
      (hallminor r)
  have hsumpos : 0 < ∑ r : Fin (k + 1),
      pascalOscillationBoolToSign (s (f r)) * B (f r) c *
        (ε * Matrix.det (fun a b : Fin k => B (f (r.succAbove a)) b)) := by
    apply Finset.sum_pos'
    · intro r _
      exact hnonneg r
    · exact ⟨r, Finset.mem_univ r, htermpos⟩
  rw [hsum] at hsumpos
  exact (lt_irrefl 0) hsumpos

/-- Every zero-compatible sign completion of the rank-`i` Pascal eigenvector
has at most `i` adjacent sign changes. -/
theorem pascalSortedEigenvector_signChangeCount_le
    {n : ℕ} (i : Fin (n + 1)) (s : Fin (n + 1) → Bool)
    (hs : IsSignCompletion (pascalSortedEigenvector (n + 1) i) s) :
    boolSignChangeCount s ≤ i.val := by
  let k := i.val + 1
  have hk : 0 < k := by omega
  have hkn : k ≤ n + 1 := by omega
  let B : Fin (n + 1) → Fin k → ℝ := fun r c =>
    pascalSortedEigenvectorMatrix (n + 1) r (Fin.castLE hkn c)
  let c : Fin k := Fin.last i.val
  obtain ⟨ε, _hε, hminorLeading⟩ :=
    pascalOscillation_pascalLeadingPlucker_same_sign hk hkn
  have hminor : ∀ (r : Fin k → Fin (n + 1)), StrictMono r →
      0 < ε * Matrix.det (fun a b : Fin k => B (r a) b) := by
    intro r hr
    let sr : Set.powersetCard (Fin (n + 1)) k :=
      Set.powersetCard.ofFinEmbEquiv (OrderEmbedding.ofStrictMono r hr)
    have hp := hminorLeading sr
    have heq : Matrix.det (fun a b : Fin k => B (r a) b) =
        pascalLeadingPlucker (n + 1) k hkn sr := by
      rw [pascalLeadingPlucker, compoundMatrix_apply]
      congr 1
      funext a b
      simp [B, sr, initialPowerset]
    rwa [heq]
  have hcol : (fun r => B r c) = pascalSortedEigenvector (n + 1) i := by
    funext r
    change pascalSortedEigenvectorMatrix (n + 1) r (Fin.castLE hkn c) = _
    rw [pascalSortedEigenvectorMatrix_apply]
    congr 1
  have hs' : IsSignCompletion (fun r => B r c) s := by
    rwa [hcol]
  have hlt := pascalOscillation_tSystem_column_signChangeCount_lt B c ε hminor s hs'
  simpa [k] using Nat.lt_succ_iff.mp hlt

end NumStability
