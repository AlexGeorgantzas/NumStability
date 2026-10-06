import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Integral
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.DiffContOnCl
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Sign.Basic
import Mathlib.LinearAlgebra.Basis.Flag
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.ProperSpace
import NumStability.Algorithms.LinearSystems.QR.HouseholderReflector
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Analysis.Conditioning.LinearSystems.PerronFrobenius
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.TestMatrices.Cauchy.Contracts
import NumStability.Analysis.TestMatrices.Pascal.Basic

/-!
# NumStability Analysis TestMatrices Pascal Contracts

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28Contracts` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open scoped BigOperators

/-- The signed Pascal involution conjugates the symmetric Pascal matrix to
its proved inverse.  Unlike the citation-dependent spectral consequence,
this matrix identity follows entirely from the local binomial algebra. -/
theorem signedPascal_conj_pascalMatrix (n : ℕ) :
    signedPascal n * pascalMatrix n * signedPascal n =
      (signedPascal n).transpose * signedPascal n := by
  rw [pascalMatrix_eq_lower_mul_transpose,
    signedPascal_eq_lower_mul_signDiagonal]
  have hleft := pascal_lower_sign_lower_eq_sign n
  calc
    (pascalLower n * pascalSignDiagonal n) *
        (pascalLower n * (pascalLower n).transpose) *
        (pascalLower n * pascalSignDiagonal n) =
      (pascalLower n * pascalSignDiagonal n * pascalLower n) *
        ((pascalLower n).transpose * pascalLower n) *
        pascalSignDiagonal n := by noncomm_ring
    _ = pascalSignDiagonal n *
        ((pascalLower n).transpose * pascalLower n) *
        pascalSignDiagonal n := by rw [hleft]
    _ = (pascalLower n * pascalSignDiagonal n).transpose *
        (pascalLower n * pascalSignDiagonal n) := by
      rw [Matrix.transpose_mul, pascalSignDiagonal_transpose]
      noncomm_ring

/-- The reciprocal-eigenvalue consequence of the proved Pascal similarity.
No spectral theorem is assumed: the proof applies the explicit inverse and
the signed involution directly to an eigenvector. -/
theorem pascal_reciprocal_eigenpair
    {n : ℕ} (lambda : ℝ) (v : RVec n)
    (hlambda : lambda ≠ 0) (hv : v ≠ 0)
    (heigen : Matrix.mulVec (pascalMatrix n) v = lambda • v) :
    let w := Matrix.mulVec (signedPascal n) v
    w ≠ 0 ∧ Matrix.mulVec (pascalMatrix n) w = lambda⁻¹ • w := by
  let P := pascalMatrix n
  let S := signedPascal n
  let B := (signedPascal n).transpose * signedPascal n
  let w := Matrix.mulVec S v
  have heigenP : Matrix.mulVec P v = lambda • v := by
    simpa [P] using heigen
  have hSS : S * S = (1 : RSqMat n) := signedPascal_mul_self n
  have hPw : P * B = (1 : RSqMat n) := pascalMatrix_mul_signedGram n
  have hsim : S * P * S = B := signedPascal_conj_pascalMatrix n
  have hSw : Matrix.mulVec S w = v := by
    rw [show w = Matrix.mulVec S v by rfl, Matrix.mulVec_mulVec, hSS,
      Matrix.one_mulVec]
  have hw : w ≠ 0 := by
    intro hw0
    apply hv
    rw [← hSw, hw0]
    simp
  have hBw : Matrix.mulVec B w = lambda • w := by
    calc
      Matrix.mulVec B w = Matrix.mulVec (S * P * S) w := by rw [hsim]
      _ = Matrix.mulVec (S * P) (Matrix.mulVec S w) := by
        exact (Matrix.mulVec_mulVec w (S * P) S).symm
      _ = Matrix.mulVec S (Matrix.mulVec P (Matrix.mulVec S w)) := by
        exact (Matrix.mulVec_mulVec (Matrix.mulVec S w) S P).symm
      _ = Matrix.mulVec S (Matrix.mulVec P v) := by rw [hSw]
      _ = Matrix.mulVec S (lambda • v) := by rw [heigenP]
      _ = lambda • w := by rw [Matrix.mulVec_smul]
  have happly := congrArg (Matrix.mulVec P) hBw
  have hscale : w = lambda • Matrix.mulVec P w := by
    simpa [Matrix.mulVec_mulVec, hPw, Matrix.mulVec_smul] using happly
  change w ≠ 0 ∧ Matrix.mulVec P w = lambda⁻¹ • w
  refine ⟨hw, ?_⟩
  funext i
  have hi := congrFun hscale i
  simp only [Pi.smul_apply, smul_eq_mul] at hi ⊢
  calc
    Matrix.mulVec P w i = lambda⁻¹ * (lambda * Matrix.mulVec P w i) := by
      field_simp
    _ = lambda⁻¹ * w i := by rw [← hi]
    _ = (lambda⁻¹ • w) i := by simp

/-- Corrected all-orders form of the characteristic-polynomial reciprocity
claim on p. 519.  Mathlib's convention is `det(XI-P)`, so odd orders are
anti-palindromic and even orders are palindromic.  The source's sign-free
identity is therefore valid only in even order (already `n=1` is a
counterexample). -/
theorem pascal_charpoly_reciprocal (n : ℕ) :
    (pascalMatrix n).charpoly =
      Polynomial.C ((-1 : ℝ) ^ n) * (pascalMatrix n).charpoly.reverse := by
  let P : RSqMat n := pascalMatrix n
  let S : RSqMat n := signedPascal n
  let B : RSqMat n := S.transpose * S
  have hdet : IsUnit (Matrix.det P) := by
    rw [show Matrix.det P = 1 by simpa [P] using pascalMatrix_det n]
    exact isUnit_one
  have hPunit : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).mpr hdet
  have hBinv : P⁻¹ = B := by
    have hBP : B * P = (1 : RSqMat n) := by
      simpa [P, B, S] using signedGram_mul_pascalMatrix n
    calc
      P⁻¹ = 1 * P⁻¹ := by rw [Matrix.one_mul]
      _ = (B * P) * P⁻¹ := by rw [hBP]
      _ = B * (P * P⁻¹) := by rw [Matrix.mul_assoc]
      _ = B := by rw [Matrix.mul_nonsing_inv P hdet, Matrix.mul_one]
  have hcharB : B.charpoly = P.charpoly := by
    have hconj : S * P * S = B := by
      simpa [P, S, B] using signedPascal_conj_pascalMatrix n
    rw [← hconj]
    calc
      (S * P * S).charpoly = (S * (P * S)).charpoly := by
        rw [Matrix.mul_assoc]
      _ = (P * S * S).charpoly := Matrix.charpoly_mul_comm S (P * S)
      _ = P.charpoly := by
        rw [Matrix.mul_assoc]
        have hSS : S * S = (1 : RSqMat n) := by
          simpa [S] using signedPascal_mul_self n
        rw [hSS, Matrix.mul_one]
  have hcharInv : P⁻¹.charpoly = P.charpoly := by rw [hBinv, hcharB]
  have hinv := Matrix.charpoly_inv P hPunit
  rw [hcharInv] at hinv
  have hdetOne : Matrix.det P = 1 := by simpa [P] using pascalMatrix_det n
  rw [hdetOne] at hinv
  simp only [Ring.inverse_one, Polynomial.C_1, mul_one,
    Fintype.card_fin] at hinv
  rw [← Matrix.reverse_charpoly] at hinv
  simpa [P] using hinv

/-- In even order the corrected theorem specializes to the sign-free
palindromic identity printed by Higham. -/
theorem pascal_charpoly_palindromic_of_even (n : ℕ) (hn : Even n) :
    (pascalMatrix n).charpoly = (pascalMatrix n).charpoly.reverse := by
  calc
    (pascalMatrix n).charpoly =
        Polynomial.C ((-1 : ℝ) ^ n) *
          (pascalMatrix n).charpoly.reverse := pascal_charpoly_reciprocal n
    _ = (pascalMatrix n).charpoly.reverse := by
      rw [Even.neg_one_pow hn]
      simp

/-- The final coordinate vector for an order-`n+1` Pascal matrix. -/
noncomputable def pascalLastBasis (n : ℕ) : RVec (n + 1) :=
  Pi.single (Fin.last n) 1

/-- The matrix that subtracts one from the final diagonal entry and changes
no other entry. -/
noncomputable def pascalLastEntryPerturbation (n : ℕ) : RSqMat (n + 1) :=
  Matrix.single (Fin.last n) (Fin.last n) (-1)

@[simp]
theorem pascalLastEntryPerturbation_apply (n : ℕ) (i j : Fin (n + 1)) :
    pascalLastEntryPerturbation n i j =
      if i = Fin.last n ∧ j = Fin.last n then -1 else 0 := by
  simp [pascalLastEntryPerturbation, Matrix.single_apply, eq_comm]

/-- The last column of the proved inverse `SᵀS`.  It is the source's
rank-one-perturbation kernel certificate. -/
noncomputable def pascalLastKernel (n : ℕ) : RVec (n + 1) :=
  Matrix.mulVec
    ((signedPascal (n + 1)).transpose * signedPascal (n + 1))
    (pascalLastBasis n)

@[simp]
theorem pascalLastKernel_last (n : ℕ) :
    pascalLastKernel n (Fin.last n) = 1 := by
  rw [pascalLastKernel, pascalLastBasis, Matrix.mulVec_single_one]
  change ((signedPascal (n + 1)).transpose * signedPascal (n + 1))
    (Fin.last n) (Fin.last n) = 1
  rw [pascalInverseFormula_apply_of_le (Fin.last n) (Fin.last n) le_rfl]
  simp

theorem pascalLastKernel_ne_zero (n : ℕ) : pascalLastKernel n ≠ 0 := by
  intro hzero
  have h := congrFun hzero (Fin.last n)
  simp at h

theorem pascalMatrix_mulVec_pascalLastKernel (n : ℕ) :
    Matrix.mulVec (pascalMatrix (n + 1)) (pascalLastKernel n) =
      pascalLastBasis n := by
  rw [pascalLastKernel, Matrix.mulVec_mulVec,
    pascalMatrix_mul_signedGram, Matrix.one_mulVec]

theorem pascalLastEntryPerturbation_mulVec_pascalLastKernel (n : ℕ) :
    Matrix.mulVec (pascalLastEntryPerturbation n) (pascalLastKernel n) =
      -pascalLastBasis n := by
  rw [pascalLastEntryPerturbation, Matrix.single_mulVec,
    pascalLastKernel_last]
  funext i
  by_cases hi : i = Fin.last n
  · subst i
    simp [pascalLastBasis]
  · simp [pascalLastBasis, hi]

/-- Higham, 2nd ed., Section 28.4, p. 520: subtracting one from the final
diagonal entry of every nonempty symmetric Pascal matrix makes it singular.
The conclusion supplies an explicit nonzero kernel vector, rather than
assuming singularity or a determinant identity. -/
theorem pascal_sub_last_entry_has_nonzero_kernel (n : ℕ) :
    ∃ z : RVec (n + 1), z ≠ 0 ∧
      Matrix.mulVec
        (pascalMatrix (n + 1) + pascalLastEntryPerturbation n) z = 0 := by
  refine ⟨pascalLastKernel n, pascalLastKernel_ne_zero n, ?_⟩
  rw [Matrix.add_mulVec, pascalMatrix_mulVec_pascalLastKernel,
    pascalLastEntryPerturbation_mulVec_pascalLastKernel]
  simp

/-- The rank-one perturbation contract is nonvacuous already for the
order-one Pascal matrix: subtracting its sole entry makes it singular. -/
theorem pascal_order_one_has_singular_rankOne_perturbation :
    ∃ E : RSqMat 1, (∀ i j, E i j = (-1 : ℝ) * 1) ∧
      ∃ z ≠ 0, Matrix.mulVec (pascalMatrix 1 + E) z = 0 := by
  apply singular_rankOne_perturbation_of_coordinate_cancellation
    (pascalMatrix 1) (fun _ => -1) (fun _ => 1) (fun _ => 1)
  · intro h
    have := congrFun h (0 : Fin 1)
    norm_num at this
  · intro i
    fin_cases i
    norm_num [pascalMatrix, Fin.sum_univ_succ]

end NumStability
