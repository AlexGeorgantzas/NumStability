import NumStability.Algorithms.Summation.Compensated.Kahan.Core
import NumStability.Analysis.LinearOperators.Jordan.NormalForm.PrimaryDecomposition
import NumStability.Analysis.TestMatrices.Pascal.PascalOscillationCore
import NumStability.Source.Higham.Chapter28.Section04.Pascal.OscillationEigenbasis

/-!
Relocated from the historical wave owners NumStability.Algorithms.TestMatrices.Higham28PascalOscillationCore under the R09/R10 completion waves; source-tier destination per the reviewed route ledger.
-/

namespace NumStability

open scoped BigOperators

open scoped BigOperators

open Set

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
