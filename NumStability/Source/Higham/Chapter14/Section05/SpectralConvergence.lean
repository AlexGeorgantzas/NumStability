import NumStability.Algorithms.LeastSquares.Higham20Problem20_3
import NumStability.Algorithms.MatrixPowers
import NumStability.Source.Higham.Chapter14.Section05.RectangularIteration

/-!
# Higham, 2nd ed., Section 14.5: spectral convergence of the Schulz iteration

This module supplies the spectral argument behind the printed initializer
`X₀ = α Aᵀ`, with `0 < α < 2 / ‖A‖₂²`.  The exact rectangular operator
`2`-norm is the norm of the complexified Euclidean linear map.  The proof uses
the repository's exact right-Gram eigenbasis; no computed spectral data enter
the statement.
-/
namespace NumStability.Ch14Ext

open NumStability

open Filter

open scoped BigOperators

/-! ## Exact rectangular spectral norm and Gram-eigenvalue bounds -/

/-- The exact rectangular operator `2`-norm used in the Chapter 14 Schulz
initializer.  It is defined through the complexified Euclidean linear map so
that it applies uniformly to square and rectangular real matrices. -/
noncomputable def ch14ext_rectOpNorm2 {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : ℝ :=
  complexMatrixOp2 (realRectToCMatrix A)

theorem ch14ext_rectOpNorm2_nonneg {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    0 ≤ ch14ext_rectOpNorm2 A :=
  complexMatrixOp2_nonneg _

/-- The exact norm provides the local predicate-style rectangular operator
bound used by the finite real matrix library. -/
theorem ch14ext_rectOpNorm2_certificate {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    rectOpNorm2Le A (ch14ext_rectOpNorm2 A) :=
  rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le A le_rfl

/-- Every eigenvalue of `AᵀA` is bounded by `‖A‖₂²`. -/
theorem ch14ext_rectRightGramEigenvalue_le_norm_sq {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (a : Fin n) :
    rectRightGramEigenvalue A a ≤ (ch14ext_rectOpNorm2 A) ^ 2 := by
  let v : Fin n → ℝ := fun j => rectRightGramEigenbasis A j a
  have hv : vecNorm2 v = 1 := by
    simpa [v] using
      (rectRightGramEigenbasis_isOrthogonal A).column_vecNorm2_eq_one a
  have hop := ch14ext_rectOpNorm2_certificate A v
  rw [hv, mul_one] at hop
  have hop_sq :
      vecNorm2 (rectMatMulVec A v) ^ 2 ≤
        (ch14ext_rectOpNorm2 A) ^ 2 :=
    (sq_le_sq₀ (vecNorm2_nonneg _) (ch14ext_rectOpNorm2_nonneg A)).mpr hop
  calc
    rectRightGramEigenvalue A a =
        ∑ i : Fin m, (rectRightGramProjectedColumn A i a) ^ 2 := by
          symm
          exact rectRightGramProjectedColumn_normSq_eq_eigenvalue A a
    _ = vecNorm2 (rectMatMulVec A v) ^ 2 := by
          rw [vecNorm2_sq]
          rfl
    _ ≤ (ch14ext_rectOpNorm2 A) ^ 2 := hop_sq

/-! ## Scalar contraction factors -/

/-- The denominator-free Schulz initializer condition makes every positive
right-Gram eigen-direction contract strictly inside the unit disk. -/
theorem ch14ext_abs_one_sub_alpha_eigenvalue_lt_one {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (a : Fin n) (alpha : ℝ)
    (halpha : 0 < alpha)
    (hupper : alpha * (ch14ext_rectOpNorm2 A) ^ 2 < 2)
    (heig : 0 < rectRightGramEigenvalue A a) :
    |1 - alpha * rectRightGramEigenvalue A a| < 1 := by
  have hle := ch14ext_rectRightGramEigenvalue_le_norm_sq A a
  have hproduct_pos : 0 < alpha * rectRightGramEigenvalue A a :=
    mul_pos halpha heig
  have hproduct_lt : alpha * rectRightGramEigenvalue A a < 2 := by
    nlinarith
  rw [abs_lt]
  constructor <;> linarith

/-! ## Spectral form of the initial right residual -/

/-- Every right-Gram eigenvector is an eigenvector of the initial right
residual `I - α AᵀA`, with eigenvalue `1 - α λ`. -/
theorem ch14ext_rectSchulzRightResidual_eigenvector {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (alpha : ℝ) (a : Fin n) :
    finiteMatVec
        (ch14ext_rectSchulzRightResidual A
          (ch14ext_rectSchulzTransposeInitializer alpha A))
        (fun j : Fin n => rectRightGramEigenbasis A j a) =
      fun j : Fin n =>
        (1 - alpha * rectRightGramEigenvalue A a) *
          rectRightGramEigenbasis A j a := by
  funext i
  have hres :=
    (ch14ext_rectSchulzResiduals_transposeInitializer alpha A).2
  have hid := congrFun
    (idMatrix_mulVec n (fun j : Fin n => rectRightGramEigenbasis A j a)) i
  have heig := rectRightGramEigenbasis_eigenvector A a i
  change
    ∑ j : Fin n,
        ch14ext_rectSchulzRightResidual A
            (ch14ext_rectSchulzTransposeInitializer alpha A) i j *
          rectRightGramEigenbasis A j a = _
  rw [hres]
  change
    ∑ j : Fin n,
        (idMatrix n i j - alpha * rectRightGram A i j) *
          rectRightGramEigenbasis A j a = _
  calc
    ∑ j : Fin n,
        (idMatrix n i j - alpha * rectRightGram A i j) *
          rectRightGramEigenbasis A j a =
        (∑ j : Fin n,
          idMatrix n i j * rectRightGramEigenbasis A j a) -
          alpha *
            (∑ j : Fin n,
              rectRightGram A i j * rectRightGramEigenbasis A j a) := by
                rw [Finset.mul_sum]
                rw [← Finset.sum_sub_distrib]
                apply Finset.sum_congr rfl
                intro j _
                ring
    _ = rectRightGramEigenbasis A i a -
          alpha *
            (rectRightGramEigenvalue A a *
              rectRightGramEigenbasis A i a) := by
                rw [hid, heig]
    _ = (1 - alpha * rectRightGramEigenvalue A a) *
          rectRightGramEigenbasis A i a := by ring

/-- Similarity form `Vᵀ R₀ V = diag(1-αλ)` for the initial right
residual. -/
theorem ch14ext_rectSchulzRightResidual_similarity {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (alpha : ℝ) :
    matMul n (matTranspose (rectRightGramEigenbasis A))
        (matMul n
          (ch14ext_rectSchulzRightResidual A
            (ch14ext_rectSchulzTransposeInitializer alpha A))
          (rectRightGramEigenbasis A)) =
      finiteDiagonal
        (fun a : Fin n => 1 - alpha * rectRightGramEigenvalue A a) := by
  classical
  let Q := rectRightGramEigenbasis A
  let M := ch14ext_rectSchulzRightResidual A
    (ch14ext_rectSchulzTransposeInitializer alpha A)
  let d : Fin n → ℝ := fun a => 1 - alpha * rectRightGramEigenvalue A a
  have heig : ∀ a : Fin n,
      finiteMatVec M (fun j : Fin n => Q j a) =
        fun j : Fin n => d a * Q j a := by
    intro a
    simpa [M, Q, d] using
      ch14ext_rectSchulzRightResidual_eigenvector A alpha a
  have horth := (rectRightGramEigenbasis_isOrthogonal A).col_orthonormal
  ext a b
  change
    ∑ j : Fin n, Q j a * (∑ k : Fin n, M j k * Q k b) =
      (if a = b then d a else 0)
  have heig_entry : ∀ j : Fin n,
      (∑ k : Fin n, M j k * Q k b) = d b * Q j b := by
    intro j
    exact congrFun (heig b) j
  calc
    ∑ j : Fin n, Q j a * (∑ k : Fin n, M j k * Q k b) =
        d b * (∑ j : Fin n, Q j a * Q j b) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [heig_entry]
          ring
    _ = d b * (if a = b then 1 else 0) := by rw [horth a b]
    _ = if a = b then d a else 0 := by
      by_cases hab : a = b <;> simp [hab]

/-- Entrywise spectral expansion of every power of the initial right
residual. -/
theorem ch14ext_rectSchulzRightResidual_matPow_entry {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (alpha : ℝ) (p : ℕ)
    (i j : Fin n) :
    matPow n
        (ch14ext_rectSchulzRightResidual A
          (ch14ext_rectSchulzTransposeInitializer alpha A)) p i j =
      ∑ a : Fin n,
        rectRightGramEigenbasis A i a *
          ((1 - alpha * rectRightGramEigenvalue A a) ^ p *
            rectRightGramEigenbasis A j a) := by
  classical
  let Q := rectRightGramEigenbasis A
  let M := ch14ext_rectSchulzRightResidual A
    (ch14ext_rectSchulzTransposeInitializer alpha A)
  let d : Fin n → ℝ := fun a => 1 - alpha * rectRightGramEigenvalue A a
  have hQ : IsOrthogonal n Q := by
    simpa [Q] using rectRightGramEigenbasis_isOrthogonal A
  have hsim : matMul n (matTranspose Q) (matMul n M Q) = finiteDiagonal d := by
    simpa [M, Q, d] using ch14ext_rectSchulzRightResidual_similarity A alpha
  have hpow := matPow_similarity n M Q (matTranspose Q) (finiteDiagonal d)
    hQ.right_inv hQ.left_inv hsim p
  have hdiag : ∀ a b : Fin n, a ≠ b → finiteDiagonal d a b = 0 := by
    intro a b hab
    simp [finiteDiagonal, hab]
  have hdiagpow := matPow_diagonal n (finiteDiagonal d) hdiag p
  rw [show matPow n M p i j =
      matMul n Q
        (matMul n (matPow n (finiteDiagonal d) p) (matTranspose Q)) i j by
        exact congrFun (congrFun hpow i) j]
  unfold matMul
  apply Finset.sum_congr rfl
  intro a _
  have hinner :
      (∑ b : Fin n,
          matPow n (finiteDiagonal d) p a b * matTranspose Q b j) =
        d a ^ p * Q j a := by
    rw [Finset.sum_eq_single a]
    · rw [hdiagpow a a]
      simp [finiteDiagonal, matTranspose]
    · intro b _ hba
      rw [hdiagpow a b]
      simp [Ne.symm hba]
    · intro ha
      exact (ha (Finset.mem_univ a)).elim
  rw [hinner]

/-! ## Moore--Penrose support and entrywise convergence -/

/-- A null right-Gram eigenvector is orthogonal to every column of the
Moore--Penrose inverse.  This is the support fact that removes the nondecaying
residual eigenvalue `1` on `ker A`. -/
theorem ch14ext_rectMoorePenrose_nullEigenvector_dot_column {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (Aplus : Fin n → Fin m → ℝ)
    (hMP : RectMoorePenrosePseudoinverse m n A Aplus)
    (a : Fin n) (j : Fin m)
    (heig : rectRightGramEigenvalue A a = 0) :
    ∑ t : Fin n, rectRightGramEigenbasis A t a * Aplus t j = 0 := by
  let v : Fin n → ℝ := fun t => rectRightGramEigenbasis A t a
  let P : Fin n → Fin n → ℝ := rectMatMul Aplus A
  have hAv : rectMatMulVec A v = 0 := by
    funext i
    exact rectRightGramProjectedColumn_eq_zero_of_eigenvalue_eq_zero
      A a heig i
  have hPv : rectMatMulVec P v = 0 := by
    rw [show rectMatMulVec P v =
        rectMatMulVec Aplus (rectMatMulVec A v) by
          simpa [P] using rectMatMulVec_rectMatMul Aplus A v]
    rw [hAv]
    ext i
    simp [rectMatMulVec]
  have hrep : ∀ t : Fin n,
      Aplus t j = ∑ s : Fin n, P t s * Aplus s j := by
    intro t
    symm
    exact congrFun (congrFun hMP.reproduces_pseudoinverse t) j
  calc
    ∑ t : Fin n, rectRightGramEigenbasis A t a * Aplus t j =
        ∑ t : Fin n, v t * (∑ s : Fin n, P t s * Aplus s j) := by
          apply Finset.sum_congr rfl
          intro t _
          rw [hrep]
    _ = ∑ t : Fin n, ∑ s : Fin n,
          v t * (P t s * Aplus s j) := by
          apply Finset.sum_congr rfl
          intro t _
          rw [Finset.mul_sum]
    _ = ∑ s : Fin n, ∑ t : Fin n,
          v t * (P t s * Aplus s j) := by rw [Finset.sum_comm]
    _ = ∑ s : Fin n, (∑ t : Fin n, P s t * v t) * Aplus s j := by
          apply Finset.sum_congr rfl
          intro s _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro t _
          have hsym : P t s = P s t := by
            simpa [P] using hMP.domain_projection_symmetric t s
          rw [hsym]
          ring
    _ = 0 := by
          have hPv_entry : ∀ s : Fin n, (∑ t : Fin n, P s t * v t) = 0 := by
            intro s
            exact congrFun hPv s
          simp_rw [hPv_entry, zero_mul, Finset.sum_const_zero]

/-- Powers of the initial right residual, after multiplication by a
Moore--Penrose inverse, tend entrywise to zero under the exact source norm
condition. -/
theorem ch14ext_rectSchulzRightResidual_matPow_mul_moorePenrose_tendsto_zero
    {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (Aplus : Fin n → Fin m → ℝ)
    (hMP : RectMoorePenrosePseudoinverse m n A Aplus)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hupper : alpha * (ch14ext_rectOpNorm2 A) ^ 2 < 2)
    (i : Fin n) (j : Fin m) :
    Tendsto
      (fun k =>
        rectMatMul
          (matPow n
            (ch14ext_rectSchulzRightResidual A
              (ch14ext_rectSchulzTransposeInitializer alpha A))
            (2 ^ k))
          Aplus i j)
      atTop (nhds 0) := by
  let Q := rectRightGramEigenbasis A
  let lam := rectRightGramEigenvalue A
  let coeff : Fin n → ℝ :=
    fun a => ∑ t : Fin n, Q t a * Aplus t j
  have hexponents : Tendsto (fun k : ℕ => 2 ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt one_lt_two
  have hterm : ∀ a : Fin n,
      Tendsto
        (fun k => Q i a * ((1 - alpha * lam a) ^ (2 ^ k) * coeff a))
        atTop (nhds 0) := by
    intro a
    by_cases hzero : lam a = 0
    · have hcoeff : coeff a = 0 := by
        simpa [coeff, Q, lam] using
          ch14ext_rectMoorePenrose_nullEigenvector_dot_column
            A Aplus hMP a j hzero
      simp [hcoeff]
    · have hpos : 0 < lam a :=
        lt_of_le_of_ne (rectRightGramEigenvalue_nonneg A a) (Ne.symm hzero)
      have habs : |1 - alpha * lam a| < 1 := by
        simpa [lam] using
          ch14ext_abs_one_sub_alpha_eigenvalue_lt_one
            A a alpha halpha hupper hpos
      have hpow : Tendsto (fun p : ℕ => (1 - alpha * lam a) ^ p)
          atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_abs_lt_one habs
      simpa [Function.comp_apply] using
        ((hpow.comp hexponents).mul_const (coeff a)).const_mul (Q i a)
  have hsum : Tendsto
      (fun k =>
        ∑ a : Fin n,
          Q i a * ((1 - alpha * lam a) ^ (2 ^ k) * coeff a))
      atTop (nhds 0) :=
    by
      simpa using
        tendsto_finset_sum (Finset.univ : Finset (Fin n))
          (fun a _ => hterm a)
  apply hsum.congr'
  filter_upwards [] with k
  symm
  unfold rectMatMul
  simp_rw [ch14ext_rectSchulzRightResidual_matPow_entry]
  calc
    ∑ t : Fin n,
        (∑ a : Fin n,
          rectRightGramEigenbasis A i a *
            ((1 - alpha * rectRightGramEigenvalue A a) ^ (2 ^ k) *
              rectRightGramEigenbasis A t a)) *
            Aplus t j =
        ∑ t : Fin n, ∑ a : Fin n,
          Q i a * ((1 - alpha * lam a) ^ (2 ^ k) * Q t a) *
            Aplus t j := by
              apply Finset.sum_congr rfl
              intro t _
              rw [Finset.sum_mul]
    _ = ∑ a : Fin n, ∑ t : Fin n,
          Q i a * ((1 - alpha * lam a) ^ (2 ^ k) * Q t a) *
            Aplus t j := by rw [Finset.sum_comm]
    _ = ∑ a : Fin n,
          Q i a * ((1 - alpha * lam a) ^ (2 ^ k) * coeff a) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.mul_sum]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro t _
            ring

/-- Denominator-free exact convergence theorem for the rectangular Schulz
iteration to any certified Moore--Penrose inverse. -/
theorem ch14ext_rectSchulzIter_tendsto_moorePenrose_of_alpha_mul_norm_sq_lt_two
    {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (Aplus : Fin n → Fin m → ℝ)
    (hMP : RectMoorePenrosePseudoinverse m n A Aplus)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hupper : alpha * (ch14ext_rectOpNorm2 A) ^ 2 < 2)
    (i : Fin n) (j : Fin m) :
    Tendsto
      (fun k =>
        ch14ext_rectSchulzIter A
          (ch14ext_rectSchulzTransposeInitializer alpha A) k i j)
      atTop (nhds (Aplus i j)) := by
  have hpower :=
    ch14ext_rectSchulzRightResidual_matPow_mul_moorePenrose_tendsto_zero
      A Aplus hMP alpha halpha hupper i j
  have herr : Tendsto
      (fun k => Aplus i j -
        ch14ext_rectSchulzIter A
          (ch14ext_rectSchulzTransposeInitializer alpha A) k i j)
      atTop (nhds 0) := by
    apply hpower.congr'
    filter_upwards [] with k
    have herror := congrFun
      (congrFun
        (ch14ext_rectMoorePenrose_sub_iter_eq_rightResidual_mul
          alpha A Aplus hMP k) i) j
    rw [herror, ch14ext_rectSchulzRightResidual_iter]
  have hconst : Tendsto (fun _ : ℕ => Aplus i j) atTop (nhds (Aplus i j)) :=
    tendsto_const_nhds
  have hconv := hconst.sub herr
  simpa only [sub_zero, sub_sub_cancel] using hconv

/-! ## Canonical arbitrary-rank Moore--Penrose target -/

/-- The finite set of nonzero right-Gram singular directions. -/
noncomputable def ch14ext_nonzeroRightGramSingularIndices {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter
    (fun a => rectRightGramBasisSingularValue A a ≠ 0)

/-- Left factor of the canonical compact SVD, enumerating precisely the
nonzero right-Gram singular directions. -/
noncomputable def ch14ext_compactSVDLeft {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    Fin m → Fin (ch14ext_nonzeroRightGramSingularIndices A).card → ℝ :=
  fun i a =>
    rectRightGramLeftSingularZeroSafe A i
      ((ch14ext_nonzeroRightGramSingularIndices A).orderEmbOfFin rfl a)

/-- Positive singular values of the canonical compact SVD. -/
noncomputable def ch14ext_compactSVDSingularValues {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    Fin (ch14ext_nonzeroRightGramSingularIndices A).card → ℝ :=
  fun a =>
    rectRightGramBasisSingularValue A
      ((ch14ext_nonzeroRightGramSingularIndices A).orderEmbOfFin rfl a)

/-- Right factor of the canonical compact SVD. -/
noncomputable def ch14ext_compactSVDRight {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    Fin n → Fin (ch14ext_nonzeroRightGramSingularIndices A).card → ℝ :=
  fun j a =>
    rectRightGramEigenbasis A j
      ((ch14ext_nonzeroRightGramSingularIndices A).orderEmbOfFin rfl a)

private theorem ch14ext_compactSVD_selected_singularValue_ne_zero {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (a : Fin (ch14ext_nonzeroRightGramSingularIndices A).card) :
    rectRightGramBasisSingularValue A
        ((ch14ext_nonzeroRightGramSingularIndices A).orderEmbOfFin rfl a) ≠ 0 := by
  have hmem := Finset.orderEmbOfFin_mem
    (ch14ext_nonzeroRightGramSingularIndices A) rfl a
  simpa [ch14ext_nonzeroRightGramSingularIndices] using hmem

private theorem ch14ext_nonzeroRightGramSVDHead_eq {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    rectRightGramBasisSVDHead A
        (ch14ext_nonzeroRightGramSingularIndices A) = A := by
  classical
  let s := ch14ext_nonzeroRightGramSingularIndices A
  have htail : rectRightGramBasisSVDTail A s = 0 := by
    ext i j
    unfold rectRightGramBasisSVDTail
    apply Finset.sum_eq_zero
    intro a ha
    have hnot : a ∉ s := Finset.mem_compl.mp ha
    have htau : rectRightGramBasisSingularValue A a = 0 := by
      by_contra hne
      exact hnot (by
        simpa [s, ch14ext_nonzeroRightGramSingularIndices] using hne)
    simp [htau]
  ext i j
  have hsplit := rectRightGramBasisSVD_head_add_tail A s i j
  rw [htail] at hsplit
  simpa [s] using hsplit

/-- The right-Gram construction gives an exact compact SVD for every real
rectangular matrix, including rank zero. -/
theorem ch14ext_compactSVD_certificate {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    Higham20CompactRealSVD A
      (ch14ext_compactSVDLeft A)
      (ch14ext_compactSVDSingularValues A)
      (ch14ext_compactSVDRight A) := by
  classical
  let s := ch14ext_nonzeroRightGramSingularIndices A
  let e : Fin s.card → Fin n := fun a => s.orderEmbOfFin rfl a
  let U : Fin m → Fin s.card → ℝ :=
    fun i a => rectRightGramLeftSingularZeroSafe A i (e a)
  let sigma : Fin s.card → ℝ :=
    fun a => rectRightGramBasisSingularValue A (e a)
  let V : Fin n → Fin s.card → ℝ :=
    fun j a => rectRightGramEigenbasis A j (e a)
  have hne : ∀ a : Fin s.card, sigma a ≠ 0 := by
    intro a
    simpa [s, e, sigma] using
      ch14ext_compactSVD_selected_singularValue_ne_zero A a
  have hpos : ∀ a : Fin s.card, 0 < sigma a := by
    intro a
    exact lt_of_le_of_ne
      (rectRightGramBasisSingularValue_nonneg A (e a)) (Ne.symm (hne a))
  have hhead : rectRightGramBasisSVDHead A s = A := by
    simpa [s] using ch14ext_nonzeroRightGramSVDHead_eq A
  have hfactorization :
      rectMatMul (rectMatMul U (diagMatrix sigma)) (finiteTranspose V) = A := by
    ext i j
    calc
      rectMatMul (rectMatMul U (diagMatrix sigma)) (finiteTranspose V) i j =
          ∑ a : Fin s.card, U i a * (sigma a * V j a) := by
            unfold rectMatMul diagMatrix finiteTranspose
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.sum_eq_single a]
            · simp
              ring
            · intro b _ hba
              simp [hba]
            · intro ha
              exact (ha (Finset.mem_univ a)).elim
      _ = rectRightGramBasisSVDHead A s i j := by
            symm
            simpa [rectRightGramBasisSVDHeadRankFactorization,
              U, sigma, V, e] using
              (rectRightGramBasisSVDHeadRankFactorization A s).factorization i j
      _ = A i j := congrFun (congrFun hhead i) j
  have hleft : rectMatMul (finiteTranspose U) U = idMatrix s.card := by
    ext a b
    change ∑ i : Fin m, U i a * U i b = idMatrix s.card a b
    have horth :=
      rectRightGramLeftSingularZeroSafe_col_orthonormal_of_pos A
        (hpos a) (hpos b)
    change ∑ i : Fin m,
        rectRightGramLeftSingularZeroSafe A i (e a) *
          rectRightGramLeftSingularZeroSafe A i (e b) = _ at horth
    rw [horth]
    by_cases hab : a = b
    · subst b
      simp [idMatrix]
    · have heab : e a ≠ e b := fun h => hab ((s.orderEmbOfFin rfl).injective h)
      simp [idMatrix, hab, heab]
  have hright : rectMatMul (finiteTranspose V) V = idMatrix s.card := by
    ext a b
    change ∑ j : Fin n, V j a * V j b = idMatrix s.card a b
    have horth := rectRightGramEigenbasis_col_orthonormal A (e a) (e b)
    change ∑ j : Fin n,
        rectRightGramEigenbasis A j (e a) *
          rectRightGramEigenbasis A j (e b) = _ at horth
    rw [horth]
    by_cases hab : a = b
    · subst b
      simp [idMatrix]
    · have heab : e a ≠ e b := fun h => hab ((s.orderEmbOfFin rfl).injective h)
      simp [idMatrix, hab, heab]
  change Higham20CompactRealSVD A U sigma V
  exact ⟨hfactorization, hleft, hright, hpos⟩

/-- Canonical Moore--Penrose inverse obtained from the exact arbitrary-rank
right-Gram compact SVD. -/
noncomputable def ch14ext_rectMoorePenrosePseudoinverse {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : Fin n → Fin m → ℝ :=
  higham20Problem20_3SVDPseudoinverse
    (ch14ext_compactSVDLeft A)
    (ch14ext_compactSVDSingularValues A)
    (ch14ext_compactSVDRight A)

theorem ch14ext_rectMoorePenrosePseudoinverse_certificate {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    RectMoorePenrosePseudoinverse m n A
      (ch14ext_rectMoorePenrosePseudoinverse A) := by
  exact higham20_problem20_3_compactSVD_moorePenrose A
    (ch14ext_compactSVDLeft A)
    (ch14ext_compactSVDSingularValues A)
    (ch14ext_compactSVDRight A)
    (ch14ext_compactSVD_certificate A)

/-! ## Source-facing convergence statements -/

/-- Canonical arbitrary-rank rectangular convergence under the equivalent
denominator-free initializer condition. -/
theorem ch14ext_rectSchulzIter_tendsto_canonicalMoorePenrose
    {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hupper : alpha * (ch14ext_rectOpNorm2 A) ^ 2 < 2)
    (i : Fin n) (j : Fin m) :
    Tendsto
      (fun k =>
        ch14ext_rectSchulzIter A
          (ch14ext_rectSchulzTransposeInitializer alpha A) k i j)
      atTop (nhds (ch14ext_rectMoorePenrosePseudoinverse A i j)) := by
  exact
    ch14ext_rectSchulzIter_tendsto_moorePenrose_of_alpha_mul_norm_sq_lt_two
      A (ch14ext_rectMoorePenrosePseudoinverse A)
      (ch14ext_rectMoorePenrosePseudoinverse_certificate A)
      alpha halpha hupper i j

/-- Higham, 2nd ed., Section 14.5 (p. 278): for an arbitrary-rank real
rectangular matrix, `X₀ = α Aᵀ` and
`0 < α < 2 / ‖A‖₂²` imply entrywise convergence of the Schulz iterates
to the Moore--Penrose inverse. -/
theorem ch14ext_rectSchulzIter_tendsto_canonicalMoorePenrose_of_lt_two_div_norm_sq
    {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hsource : alpha < 2 / (ch14ext_rectOpNorm2 A) ^ 2)
    (i : Fin n) (j : Fin m) :
    Tendsto
      (fun k =>
        ch14ext_rectSchulzIter A
          (ch14ext_rectSchulzTransposeInitializer alpha A) k i j)
      atTop (nhds (ch14ext_rectMoorePenrosePseudoinverse A i j)) := by
  have hsq_nonneg : 0 ≤ (ch14ext_rectOpNorm2 A) ^ 2 := sq_nonneg _
  have hsq_ne : (ch14ext_rectOpNorm2 A) ^ 2 ≠ 0 := by
    intro hzero
    rw [hzero] at hsource
    norm_num at hsource
    exact (not_lt_of_ge (le_of_lt halpha)) hsource
  have hsq_pos : 0 < (ch14ext_rectOpNorm2 A) ^ 2 :=
    lt_of_le_of_ne hsq_nonneg (Ne.symm hsq_ne)
  have hupper : alpha * (ch14ext_rectOpNorm2 A) ^ 2 < 2 :=
    (lt_div_iff₀ hsq_pos).mp hsource
  exact ch14ext_rectSchulzIter_tendsto_canonicalMoorePenrose
    A alpha halpha hupper i j

/-- Square nonsingular specialization of the printed source statement: if
`Ainv` is an actual two-sided inverse, the same transpose initializer
converges entrywise to `Ainv`. -/
theorem ch14ext_schulzIter_tendsto_inverse_of_lt_two_div_norm_sq
    {n : ℕ} (A Ainv : Fin n → Fin n → ℝ)
    (hInv : IsInverse n A Ainv)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hsource : alpha < 2 / (ch14ext_rectOpNorm2 A) ^ 2)
    (i j : Fin n) :
    Tendsto
      (fun k =>
        ch14ext_rectSchulzIter A
          (ch14ext_rectSchulzTransposeInitializer alpha A) k i j)
      atTop (nhds (Ainv i j)) := by
  have hright : rectMatMul A Ainv = idMatrix n := by
    ext a b
    simpa [rectMatMul, idMatrix] using hInv.2 a b
  have hdomainEq : rectMatMul Ainv A = idMatrix n := by
    ext a b
    simpa [rectMatMul, idMatrix] using hInv.1 a b
  have hdomain : IsSymmetricFiniteMatrix (rectMatMul Ainv A) := by
    rw [hdomainEq]
    intro a b
    simp [idMatrix, eq_comm]
  have hMP : RectMoorePenrosePseudoinverse n n A Ainv :=
    rectMoorePenrosePseudoinverse_of_right_inverse_and_domain_symmetric
      A Ainv hright hdomain
  have hsq_nonneg : 0 ≤ (ch14ext_rectOpNorm2 A) ^ 2 := sq_nonneg _
  have hsq_ne : (ch14ext_rectOpNorm2 A) ^ 2 ≠ 0 := by
    intro hzero
    rw [hzero] at hsource
    norm_num at hsource
    exact (not_lt_of_ge (le_of_lt halpha)) hsource
  have hsq_pos : 0 < (ch14ext_rectOpNorm2 A) ^ 2 :=
    lt_of_le_of_ne hsq_nonneg (Ne.symm hsq_ne)
  have hupper : alpha * (ch14ext_rectOpNorm2 A) ^ 2 < 2 :=
    (lt_div_iff₀ hsq_pos).mp hsource
  exact
    ch14ext_rectSchulzIter_tendsto_moorePenrose_of_alpha_mul_norm_sq_lt_two
      A Ainv hMP alpha halpha hupper i j

end NumStability.Ch14Ext
