import NumStability.Algorithms.Summation.Compensated.Kahan.Core
import Mathlib.Analysis.SpecialFunctions.Stirling
import NumStability.Analysis.TestMatrices.Hilbert.Asymptotics
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.Asymptotics.Asymptotics
import NumStability.Source.Higham.Chapter28.Section03.RandomSVD.RandsvdNorm
import NumStability.Analysis.LinearOperators.Jordan.NormalForm.PrimaryDecomposition
import NumStability.Analysis.TestMatrices.Companion.Contracts
import NumStability.Analysis.TestMatrices.Pascal.Contracts
import NumStability.Analysis.TestMatrices.Toeplitz.Contracts
import NumStability.Source.Higham.Chapter09.Problems
import NumStability.Upstream.Lindemann.AlgebraicPart

/-!
Relocated from the historical wave owners NumStability.Algorithms.TestMatrices.Higham28Contracts under the R09/R10 completion waves; source-tier destination per the reviewed route ledger.
-/

open scoped BigOperators

namespace NumStability
/-- One transpose-companion step sends the reverse basis vector indexed by
`k` to the reverse basis vector indexed by `k+1`. -/
private theorem companion_transpose_reverseBasis_step
    {n k : ℕ} (a : ℕ → ℂ) (hk : k + 1 < n) :
    Matrix.mulVec (companionMatrix n a).transpose
        (Pi.single (Fin.rev ⟨k, by omega⟩ : Fin n) 1) =
      Pi.single (Fin.rev ⟨k + 1, hk⟩ : Fin n) 1 := by
  rw [Matrix.mulVec_single_one]
  funext i
  simp only [Matrix.col_apply, Matrix.transpose_apply]
  have hjpos : 0 < (Fin.rev ⟨k, by omega⟩ : Fin n).val := by
    simp [Fin.rev]
    omega
  rw [companionMatrix]
  simp only [if_neg (ne_of_gt hjpos)]
  simp only [Pi.single_apply]
  by_cases hidx : (Fin.rev ⟨k, by omega⟩ : Fin n).val = i.val + 1
  · rw [if_pos hidx]
    rw [if_pos]
    apply Fin.ext
    change i.val = n - ((k + 1) + 1)
    change n - (k + 1) = i.val + 1 at hidx
    omega
  · rw [if_neg hidx]
    rw [if_neg]
    intro hi
    apply hidx
    change n - (k + 1) = i.val + 1
    have hiv : i.val = n - ((k + 1) + 1) := by
      have := congrArg Fin.val hi
      simpa only [Fin.val_rev, Fin.val_mk] using this
    omega

private theorem companion_transpose_pow_seed_nat
    {n : ℕ} (hn : 0 < n) (a : ℕ → ℂ) (k : ℕ) (hk : k < n) :
    Matrix.mulVec ((companionMatrix n a).transpose ^ k)
        (Pi.single (Fin.rev ⟨0, hn⟩ : Fin n) 1) =
      Pi.single (Fin.rev ⟨k, hk⟩ : Fin n) 1 := by
  induction k with
  | zero =>
      rw [pow_zero, Matrix.one_mulVec]
  | succ k ih =>
      rw [pow_succ']
      rw [← Matrix.mulVec_mulVec]
      rw [ih (by omega)]
      exact companion_transpose_reverseBasis_step a hk

/-- The entire transpose Krylov family is exactly the reversed standard
basis; no cyclicity premise is assumed. -/
theorem companion_transpose_krylov_eq_reverseBasis
    {n : ℕ} (hn : 0 < n) (a : ℕ → ℂ) (k : Fin n) :
    Matrix.mulVec ((companionMatrix n a).transpose ^ k.val)
        (Pi.single (Fin.rev ⟨0, hn⟩ : Fin n) 1) =
      Pi.single k.rev 1 := by
  simpa using companion_transpose_pow_seed_nat hn a k.val k.isLt

theorem companion_transpose_krylov_linearIndependent
    {n : ℕ} (hn : 0 < n) (a : ℕ → ℂ) :
    LinearIndependent ℂ (fun k : Fin n =>
      Matrix.mulVec ((companionMatrix n a).transpose ^ k.val)
        (Pi.single (Fin.rev ⟨0, hn⟩ : Fin n) 1)) := by
  have hstd : LinearIndependent ℂ
      (fun k : Fin n => (Pi.single k.rev (1 : ℂ) : Fin n → ℂ)) := by
    simpa [Function.comp_def] using
      (Pi.linearIndependent_single_one (Fin n) ℂ).comp Fin.rev
        Fin.revPerm.injective
  convert hstd using 1
  funext k
  exact companion_transpose_krylov_eq_reverseBasis hn a k

/-- Every positive-order companion matrix has the explicit left cyclic vector
`e_n`.  This is the genuine finite construction behind nonderogatoriness. -/
theorem companion_hasLeftCyclicVector
    {n : ℕ} (hn : 0 < n) (a : ℕ → ℂ) :
    HasLeftCyclicVector (companionMatrix n a) := by
  refine ⟨Pi.single (Fin.rev ⟨0, hn⟩ : Fin n) 1, ?_⟩
  exact companion_transpose_krylov_linearIndependent hn a

private theorem companionMatrix_sub_scalar_rank_ge_succ
    (n : ℕ) (a : ℕ → ℂ) (lambda : ℂ) :
    n ≤ Matrix.rank
      (companionMatrix (n + 1) a -
        lambda • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) := by
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    companionMatrix (n + 1) a - lambda • 1
  let B : Matrix (Fin n) (Fin (n + 1)) ℂ :=
    A.submatrix Fin.succ (Equiv.refl _)
  have hrows : Matrix.rank B ≤ Matrix.rank A := by
    exact Matrix.rank_submatrix_le Fin.succ (Equiv.refl _) A
  have hcols :
      Matrix.rank
          (B.transpose.submatrix Fin.castSucc (Equiv.refl (Fin n))) ≤
        Matrix.rank B.transpose := by
    exact Matrix.rank_submatrix_le Fin.castSucc (Equiv.refl (Fin n)) B.transpose
  have hminor :
      B.transpose.submatrix Fin.castSucc (Equiv.refl (Fin n)) =
        (companionRankMinor n a lambda).transpose := by
    ext i j
    rfl
  rw [hminor, Matrix.rank_transpose, Matrix.rank_transpose] at hcols
  have hunit : IsUnit (companionRankMinor n a lambda) := by
    rw [Matrix.isUnit_iff_isUnit_det, companionRankMinor_det]
    exact isUnit_one
  have hrank := Matrix.rank_of_isUnit (companionRankMinor n a lambda) hunit
  have hrank' : Matrix.rank (companionRankMinor n a lambda) = n := by
    simpa using hrank
  change n ≤ Matrix.rank A
  calc
    n = Matrix.rank (companionRankMinor n a lambda) := hrank'.symm
    _ ≤ Matrix.rank B := hcols
    _ ≤ Matrix.rank A := hrows

/-- Higham, p. 523: every scalar shift of a companion matrix has rank at
least `n - 1`, the printed rank characterization of nonderogatoriness. -/
theorem companionMatrix_sub_scalar_rank_ge
    (n : ℕ) (a : ℕ → ℂ) (lambda : ℂ) :
    n - 1 ≤ Matrix.rank
      (companionMatrix n a -
        lambda • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  cases n with
  | zero => simp
  | succ n =>
      simpa [Nat.succ_eq_add_one] using
        companionMatrix_sub_scalar_rank_ge_succ n a lambda

end NumStability
