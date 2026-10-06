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
import NumStability.Analysis.TestMatrices.Companion.Basic

/-!
# NumStability Analysis TestMatrices Companion Contracts

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28Contracts` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open scoped BigOperators

/-- The monic polynomial encoded by the companion matrix: `X^n - sum a_k X^k`. -/
noncomputable def companionCharacteristicFormula
    (n : ℕ) (a : ℕ → ℂ) : Polynomial ℂ :=
  Polynomial.X ^ n -
    ∑ k ∈ Finset.range n, Polynomial.monomial k (a k)

theorem companionCharacteristicFormula_coeff
    (n : ℕ) (a : ℕ → ℂ) (k : ℕ) :
    (companionCharacteristicFormula n a).coeff k =
      if k = n then 1 else if k < n then -a k else 0 := by
  have hsum :
      (∑ b ∈ Finset.range n, Polynomial.monomial b (a b)).coeff k =
        if k < n then a k else 0 := by
    rw [Polynomial.finset_sum_coeff]
    by_cases hk : k < n
    · rw [Finset.sum_eq_single k]
      · simp [hk]
      · intro b hb hbk
        simp [Polynomial.coeff_monomial, hbk]
      · simp [hk]
    · rw [if_neg hk]
      apply Finset.sum_eq_zero
      intro b hb
      rw [Polynomial.coeff_monomial]
      simp only [ite_eq_right_iff]
      intro hbk
      subst b
      exact (hk (Finset.mem_range.mp hb)).elim
  rw [companionCharacteristicFormula, Polynomial.coeff_sub,
    Polynomial.coeff_X_pow, hsum]
  by_cases hkn : k = n
  · subst k
    simp
  · by_cases hk : k < n <;> simp [hkn, hk]

/-- The square minor obtained from rows `1,...,n` and columns `0,...,n-1`
of the scalar-shifted order-`n+1` companion matrix. -/
noncomputable def companionRankMinor
    (n : ℕ) (a : ℕ → ℂ) (lambda : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j =>
    (companionMatrix (n + 1) a - lambda •
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))
      i.succ j.castSucc

theorem companionRankMinor_apply
    (n : ℕ) (a : ℕ → ℂ) (lambda : ℂ) (i j : Fin n) :
    companionRankMinor n a lambda i j =
      if i = j then 1 else if i.val + 1 = j.val then -lambda else 0 := by
  simp only [companionRankMinor, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, Fin.val_succ, Fin.val_castSucc, companionMatrix]
  simp only [Nat.succ_ne_zero, ↓reduceIte]
  by_cases hij : i = j
  · subst j
    have hne : i.succ ≠ i.castSucc := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.val_castSucc] at hv
      omega
    simp [hne]
  · have hvals : i.val ≠ j.val := fun h => hij (Fin.ext h)
    simp only [hij, if_false]
    by_cases hnext : i.val + 1 = j.val
    · have hfin : i.succ = j.castSucc := Fin.ext hnext
      simp [hnext, hfin]
    · have hfin : i.succ ≠ j.castSucc := by
        intro h
        exact hnext (congrArg Fin.val h)
      simp [hnext, hfin, hvals]

theorem companionRankMinor_upperTriangular
    (n : ℕ) (a : ℕ → ℂ) (lambda : ℂ) :
    Matrix.BlockTriangular (companionRankMinor n a lambda) id := by
  intro i j hji
  rw [companionRankMinor_apply]
  have hij : i ≠ j := by
    intro h
    subst j
    exact lt_irrefl _ hji
  have hnext : i.val + 1 ≠ j.val := by
    have hv : j.val < i.val := hji
    omega
  simp [hij, hnext]

/-- The explicit rank minor is upper triangular with unit diagonal. -/
theorem companionRankMinor_det
    (n : ℕ) (a : ℕ → ℂ) (lambda : ℂ) :
    Matrix.det (companionRankMinor n a lambda) = 1 := by
  rw [Matrix.det_of_upperTriangular
    (companionRankMinor_upperTriangular n a lambda)]
  simp [companionRankMinor_apply]

/-- `1 + sum |a_k|^2`, the trace parameter in the two exceptional squared
singular values of a companion matrix. -/
noncomputable def companionSingularAlpha (n : ℕ) (a : ℕ → ℂ) : ℝ :=
  1 + ∑ k ∈ Finset.range n, ‖a k‖ ^ 2

/-- The exact Gram matrix of the companion matrix: a rank-one outer product
of the reversed coefficient vector plus `diag(1,...,1,0)`. -/
noncomputable def companionGramFormula
    (n : ℕ) (a : ℕ → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j =>
    star (a (n - 1 - i.val)) * a (n - 1 - j.val) +
      if i = j ∧ i.val + 1 < n then 1 else 0

/-- Direct entrywise calculation of `Cᴴ C`.  This is the genuine low-rank
producer needed by the singular-value argument. -/
theorem companion_conjTranspose_mul_self
    (n : ℕ) (a : ℕ → ℂ) :
    (companionMatrix n a).conjTranspose * companionMatrix n a =
      companionGramFormula n a := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    companionGramFormula]
  let z : Fin n := ⟨0, Nat.zero_lt_of_lt i.isLt⟩
  rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ z)]
  have hz : z.val = 0 := rfl
  simp only [companionMatrix, hz, if_pos]
  have hclean :
      (∑ x ∈ Finset.univ.erase z,
          star (if x.val = 0 then a (n - 1 - i.val)
            else if x.val = i.val + 1 then 1 else 0) *
          (if x.val = 0 then a (n - 1 - j.val)
            else if x.val = j.val + 1 then 1 else 0)) =
        ∑ x ∈ Finset.univ.erase z,
          (if x.val = i.val + 1 then 1 else 0) *
          (if x.val = j.val + 1 then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxne : x.val ≠ 0 := by
      intro hx0
      have hxz : x = z := Fin.ext (by simpa [hz] using hx0)
      exact (Finset.mem_erase.mp hx).1 hxz
    simp [hxne]
  rw [hclean]
  have hsum :
      (∑ x ∈ Finset.univ.erase z,
          (if x.val = i.val + 1 then 1 else 0) *
          (if x.val = j.val + 1 then 1 else 0) : ℂ) =
        if i = j ∧ i.val + 1 < n then 1 else 0 := by
    by_cases hi : i.val + 1 < n
    · let ip : Fin n := ⟨i.val + 1, hi⟩
      have hip : ∀ x : Fin n, x.val = i.val + 1 ↔ x = ip := by
        intro x
        constructor
        · intro h
          exact Fin.ext h
        · rintro rfl
          rfl
      simp_rw [hip]
      by_cases hj : j.val + 1 < n
      · let jp : Fin n := ⟨j.val + 1, hj⟩
        have hjp : ∀ x : Fin n, x.val = j.val + 1 ↔ x = jp := by
          intro x
          constructor
          · intro h
            exact Fin.ext h
          · rintro rfl
            rfl
        simp_rw [hjp]
        by_cases hij : i = j
        · subst j
          simp [hi, ip, jp, z]
        · have hval : j.val ≠ i.val := by
            intro h
            exact hij (Fin.ext h.symm)
          simp [hij, hi, ip, jp, z, hval]
      · have hjnone : ∀ x : Fin n, x.val ≠ j.val + 1 := by
          intro x h
          omega
        simp_rw [if_neg (hjnone _)]
        have hij : i ≠ j := by
          intro h
          subst j
          exact hj hi
        simp [hij]
    · have hinone : ∀ x : Fin n, x.val ≠ i.val + 1 := by
        intro x h
        omega
      simp_rw [if_neg (hinone _)]
      simp [hi]
  rw [hsum]
  ring

/-- The printed target polynomial for the two exceptional squared singular
values in the source domain `2 ≤ n`; in that domain the other `n-2` Gram roots
are one. The definition is algebraically meaningful outside that domain, but
no singular-value interpretation is claimed there. -/
noncomputable def companionExceptionalSingularSqPolynomial
    (n : ℕ) (a : ℕ → ℂ) : Polynomial ℂ :=
  Polynomial.X ^ 2 -
    Polynomial.C (companionSingularAlpha n a : ℂ) * Polynomial.X +
    Polynomial.C ((‖a 0‖ ^ 2 : ℝ) : ℂ)

end NumStability
