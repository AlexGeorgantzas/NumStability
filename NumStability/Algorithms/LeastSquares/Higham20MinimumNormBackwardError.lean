-- Higham, 2nd ed., Chapter 20, p. 404: minimum-norm backward error.

import NumStability.Algorithms.LeastSquares.Higham20WeightedLimit

namespace NumStability

/-- A least-squares minimizer that has minimum Euclidean norm among all
    least-squares minimizers for the same data. -/
def IsMinimumNormLeastSquaresMinimizer {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) : Prop :=
  IsLeastSquaresMinimizer A b y ∧
    ∀ z : Fin n → ℝ, IsLeastSquaresMinimizer A b z →
      vecNorm2 y ≤ vecNorm2 z

/-- Full column rank makes every least-squares minimizer the unique, hence
    minimum-Euclidean-norm, least-squares minimizer. -/
theorem IsMinimumNormLeastSquaresMinimizer.of_rectMatMulVec_injective
    {m n : ℕ} {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {y : Fin n → ℝ} (hA : Function.Injective (rectMatMulVec A))
    (hy : IsLeastSquaresMinimizer A b y) :
    IsMinimumNormLeastSquaresMinimizer A b y := by
  refine ⟨hy, ?_⟩
  intro z hz
  have hzy : z = y :=
    IsLeastSquaresMinimizer.eq_of_rectMatMulVec_injective hA hz hy
  subst z
  exact le_rfl

/-- Strengthened feasibility from the precise p. 404 literature remark:
    `y` must be a minimum-2-norm least-squares solution of the perturbed
    problem, rather than merely an arbitrary least-squares minimizer. -/
def LSMinimumNormBackwardErrorFeasible {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ) : Prop :=
  IsMinimumNormLeastSquaresMinimizer
    (fun i j => A i j + DeltaA i j)
    (fun i => b i + Deltab i) y

/-- A strengthened feasible perturbation is feasible for the original
    normwise backward-error problem (20.20). -/
theorem LSMinimumNormBackwardErrorFeasible.to_normwise
    {m n : ℕ} {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {y : Fin n → ℝ} {DeltaA : Fin m → Fin n → ℝ}
    {Deltab : Fin m → ℝ}
    (h : LSMinimumNormBackwardErrorFeasible A b y DeltaA Deltab) :
    LSNormwiseBackwardErrorFeasible A b y DeltaA Deltab :=
  h.1

/-- The p. 404 minimum-norm condition is automatic when the perturbed matrix
    has full column rank. -/
theorem LSMinimumNormBackwardErrorFeasible.of_normwise_of_injective
    {m n : ℕ} {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {y : Fin n → ℝ} {DeltaA : Fin m → Fin n → ℝ}
    {Deltab : Fin m → ℝ}
    (hfeas : LSNormwiseBackwardErrorFeasible A b y DeltaA Deltab)
    (hinj : Function.Injective
      (rectMatMulVec (fun i j => A i j + DeltaA i j))) :
    LSMinimumNormBackwardErrorFeasible A b y DeltaA Deltab :=
  IsMinimumNormLeastSquaresMinimizer.of_rectMatMulVec_injective hinj hfeas

/-- Attainable weighted costs when the perturbed problem is additionally
    required to have `y` as its minimum-2-norm least-squares solution. -/
noncomputable def lsMinimumNormBackwardErrorValuesF {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) : Set ℝ :=
  {eta | ∃ (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ),
    LSMinimumNormBackwardErrorFeasible A b y DeltaA Deltab ∧
      eta = lsNormwiseBackwardErrorCostF theta DeltaA Deltab}

/-- Infimum of the strengthened p. 404 attainable-cost set. -/
noncomputable def lsMinimumNormBackwardErrorEtaF {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) : ℝ :=
  sInf (lsMinimumNormBackwardErrorValuesF theta A b y)

theorem lsMinimumNormBackwardErrorValuesF.bddBelow {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    BddBelow (lsMinimumNormBackwardErrorValuesF theta A b y) := by
  refine ⟨0, ?_⟩
  intro eta heta
  rcases heta with ⟨DeltaA, Deltab, _hfeas, rfl⟩
  exact lsNormwiseBackwardErrorCostF_nonneg theta DeltaA Deltab

theorem lsMinimumNormBackwardErrorValuesF.mem_of_feasible {m n : ℕ}
    (theta : ℝ) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (y : Fin n → ℝ) (DeltaA : Fin m → Fin n → ℝ)
    (Deltab : Fin m → ℝ)
    (hfeas : LSMinimumNormBackwardErrorFeasible A b y DeltaA Deltab) :
    lsNormwiseBackwardErrorCostF theta DeltaA Deltab ∈
      lsMinimumNormBackwardErrorValuesF theta A b y := by
  exact ⟨DeltaA, Deltab, hfeas, rfl⟩

/-- The strengthened infimum is no larger than the cost of any strengthened
    feasible perturbation. -/
theorem lsMinimumNormBackwardErrorEtaF_le_costF_of_feasible {m n : ℕ}
    (theta : ℝ) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (y : Fin n → ℝ) (DeltaA : Fin m → Fin n → ℝ)
    (Deltab : Fin m → ℝ)
    (hfeas : LSMinimumNormBackwardErrorFeasible A b y DeltaA Deltab) :
    lsMinimumNormBackwardErrorEtaF theta A b y ≤
      lsNormwiseBackwardErrorCostF theta DeltaA Deltab := by
  unfold lsMinimumNormBackwardErrorEtaF
  exact csInf_le
    (lsMinimumNormBackwardErrorValuesF.bddBelow theta A b y)
    (lsMinimumNormBackwardErrorValuesF.mem_of_feasible
      theta A b y DeltaA Deltab hfeas)

/-- Higham, 2nd ed., Chapter 20, p. 404, the immediate full-rank-at-the-minimum
    subcase of the minimum-norm backward-error invariance remark.

    If an ordinary cost-minimizing perturbation for (20.20) has injective
    perturbed matrix action, its least-squares minimizer is unique. Therefore
    the same perturbation attains the strengthened minimum-norm problem, and
    the two backward-error infima are equal. This theorem deliberately does
    not claim the deeper cited result for rank-deficient minimizing data. -/
theorem lsMinimumNormBackwardErrorEtaF_eq_normwise_of_attained_injective
    {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ)
    (hfeas : LSNormwiseBackwardErrorFeasible A b y DeltaA Deltab)
    (hmin : ∀ (DeltaA' : Fin m → Fin n → ℝ)
        (Deltab' : Fin m → ℝ),
      LSNormwiseBackwardErrorFeasible A b y DeltaA' Deltab' →
        lsNormwiseBackwardErrorCostF theta DeltaA Deltab ≤
          lsNormwiseBackwardErrorCostF theta DeltaA' Deltab')
    (hinj : Function.Injective
      (rectMatMulVec (fun i j => A i j + DeltaA i j))) :
    lsMinimumNormBackwardErrorEtaF theta A b y =
      lsNormwiseBackwardErrorEtaF theta A b y := by
  have hstrong :
      LSMinimumNormBackwardErrorFeasible A b y DeltaA Deltab :=
    LSMinimumNormBackwardErrorFeasible.of_normwise_of_injective hfeas hinj
  have hord_eq :
      lsNormwiseBackwardErrorEtaF theta A b y =
        lsNormwiseBackwardErrorCostF theta DeltaA Deltab :=
    lsNormwiseBackwardErrorEtaF_eq_costF_of_feasible_minimizer
      theta A b y DeltaA Deltab hfeas hmin
  apply le_antisymm
  · rw [hord_eq]
    exact lsMinimumNormBackwardErrorEtaF_le_costF_of_feasible
      theta A b y DeltaA Deltab hstrong
  · unfold lsMinimumNormBackwardErrorEtaF
    apply le_csInf
    · exact ⟨lsNormwiseBackwardErrorCostF theta DeltaA Deltab,
        lsMinimumNormBackwardErrorValuesF.mem_of_feasible
          theta A b y DeltaA Deltab hstrong⟩
    · intro eta heta
      rcases heta with ⟨DeltaA', Deltab', hstrong', rfl⟩
      exact lsNormwiseBackwardErrorEtaF_le_costF_of_feasible
        theta A b y DeltaA' Deltab' hstrong'.to_normwise

/-! ## The square-domain discrepancy in the p. 404 prose claim

The cited Sun result is stated for a strictly tall matrix and matrix-only
perturbations.  Read literally over Chapter 20's square-or-tall domain, the
p. 404 sentence about (20.20) is false.  The scalar instance below proves the
discrepancy without relying on numerical evaluation.
-/

/-- Scalar source matrix in the square counterexample to the unqualified
    p. 404 minimum-norm backward-error invariance claim. -/
def higham20P404SquareA : Fin 1 → Fin 1 → ℝ := fun _ _ => 1

/-- Scalar right-hand side in the p. 404 square counterexample. -/
def higham20P404SquareB : Fin 1 → ℝ := fun _ => 3

/-- Nonzero candidate solution in the p. 404 square counterexample. -/
def higham20P404SquareY : Fin 1 → ℝ := fun _ => 1

private def higham20P404SquareDeltaA (a : ℝ) : Fin 1 → Fin 1 → ℝ :=
  fun _ _ => a

private def higham20P404SquareDeltaB (d : ℝ) : Fin 1 → ℝ :=
  fun _ => d

private theorem higham20_p404_square_cost (a d : ℝ) :
    lsNormwiseBackwardErrorCostF 1 (higham20P404SquareDeltaA a)
        (higham20P404SquareDeltaB d) =
      Real.sqrt (a ^ 2 + d ^ 2) := by
  simp [lsNormwiseBackwardErrorCostF,
    lsNormwiseBackwardErrorWeightedMatrix, frobNormRect, frobNormSqRect,
    higham20P404SquareDeltaB, Fin.append]
  norm_num [Fin.addCases, higham20P404SquareDeltaA]

private theorem higham20_p404_square_ordinary_feasible_at_zero :
    LSNormwiseBackwardErrorFeasible higham20P404SquareA higham20P404SquareB
      higham20P404SquareY (higham20P404SquareDeltaA (-1))
      (higham20P404SquareDeltaB 0) := by
  intro z
  simp [lsObjective, lsResidual, rectMatMulVec, vecNorm2Sq,
    higham20P404SquareA, higham20P404SquareB, higham20P404SquareY,
    higham20P404SquareDeltaA, higham20P404SquareDeltaB]

private theorem higham20_p404_square_strong_feasible_at_two :
    LSMinimumNormBackwardErrorFeasible higham20P404SquareA
      higham20P404SquareB higham20P404SquareY
      (higham20P404SquareDeltaA 1) (higham20P404SquareDeltaB (-1)) := by
  apply LSMinimumNormBackwardErrorFeasible.of_normwise_of_injective
  · intro z
    simp [lsObjective, lsResidual, rectMatMulVec, vecNorm2Sq,
      higham20P404SquareA, higham20P404SquareB, higham20P404SquareY,
      higham20P404SquareDeltaA, higham20P404SquareDeltaB]
    nlinarith [sq_nonneg (z 0 - 1)]
  · intro x z hxz
    funext i
    have h := congrFun hxz 0
    simp [rectMatMulVec, higham20P404SquareA,
      higham20P404SquareDeltaA] at h
    simpa [Subsingleton.elim i 0] using h

private theorem higham20_p404_square_strong_implies_relation (a d : ℝ)
    (h : LSMinimumNormBackwardErrorFeasible higham20P404SquareA
      higham20P404SquareB higham20P404SquareY
      (higham20P404SquareDeltaA a) (higham20P404SquareDeltaB d)) :
    d = a - 2 := by
  have hB : 1 + a ≠ 0 := by
    intro hzero
    have hzmin : IsLeastSquaresMinimizer
        (fun i j => higham20P404SquareA i j +
          higham20P404SquareDeltaA a i j)
        (fun i => higham20P404SquareB i + higham20P404SquareDeltaB d i)
        (fun _ => 0) := by
      intro z
      simp [lsObjective, lsResidual, rectMatMulVec, vecNorm2Sq,
        higham20P404SquareA, higham20P404SquareB,
        higham20P404SquareDeltaA, higham20P404SquareDeltaB, hzero]
    have hnorm := h.2 (fun _ => 0) hzmin
    norm_num [vecNorm2, vecNorm2Sq, higham20P404SquareY] at hnorm
  have horth :=
    (IsLeastSquaresMinimizer.rectLSNormalEquations h.1).residual_orthogonal 0
  simp [lsResidual, rectMatMulVec, higham20P404SquareA,
    higham20P404SquareB, higham20P404SquareY,
    higham20P404SquareDeltaA, higham20P404SquareDeltaB] at horth
  rcases horth with hzero | hrel
  · exact (hB hzero).elim
  · linarith

private theorem higham20_p404_sqrt_two_le_square_strong_cost (a d : ℝ)
    (h : LSMinimumNormBackwardErrorFeasible higham20P404SquareA
      higham20P404SquareB higham20P404SquareY
      (higham20P404SquareDeltaA a) (higham20P404SquareDeltaB d)) :
    Real.sqrt 2 ≤ lsNormwiseBackwardErrorCostF 1
      (higham20P404SquareDeltaA a) (higham20P404SquareDeltaB d) := by
  rw [higham20_p404_square_cost]
  have hd := higham20_p404_square_strong_implies_relation a d h
  rw [hd]
  apply Real.sqrt_le_sqrt
  nlinarith [sq_nonneg (a - 1)]

/-- Higham, 2nd ed., Chapter 20, p. 404: exact square-domain source
    discrepancy for the unqualified minimum-norm backward-error claim.

    For `A = [1]`, `b = [3]`, `y = [1]`, and finite weight `theta = 1`, the
    ordinary backward error is at most `1`, while the strengthened
    minimum-norm backward error is at least `sqrt 2`.  Both `b` and `y` are
    nonzero.  Hence the two infima cannot be equal on the full square-or-tall
    Chapter 20 domain; the cited strict-tall result must not be silently
    generalized to `m = n`. -/
theorem higham20_p404_square_source_discrepancy :
    higham20P404SquareB ≠ 0 ∧
    higham20P404SquareY ≠ 0 ∧
    lsNormwiseBackwardErrorEtaF 1 higham20P404SquareA higham20P404SquareB
        higham20P404SquareY ≤ 1 ∧
    Real.sqrt 2 ≤
      lsMinimumNormBackwardErrorEtaF 1 higham20P404SquareA
        higham20P404SquareB higham20P404SquareY ∧
    lsMinimumNormBackwardErrorEtaF 1 higham20P404SquareA
        higham20P404SquareB higham20P404SquareY ≠
      lsNormwiseBackwardErrorEtaF 1 higham20P404SquareA
        higham20P404SquareB higham20P404SquareY := by
  have hb : higham20P404SquareB ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    norm_num [higham20P404SquareB] at h0
  have hy : higham20P404SquareY ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    norm_num [higham20P404SquareY] at h0
  have hord :
      lsNormwiseBackwardErrorEtaF 1 higham20P404SquareA
          higham20P404SquareB higham20P404SquareY ≤ 1 := by
    have hcost : lsNormwiseBackwardErrorCostF 1
        (higham20P404SquareDeltaA (-1))
        (higham20P404SquareDeltaB 0) = 1 := by
      rw [higham20_p404_square_cost]
      norm_num
    calc
      lsNormwiseBackwardErrorEtaF 1 higham20P404SquareA
          higham20P404SquareB higham20P404SquareY ≤
          lsNormwiseBackwardErrorCostF 1
            (higham20P404SquareDeltaA (-1))
            (higham20P404SquareDeltaB 0) :=
        lsNormwiseBackwardErrorEtaF_le_costF_of_feasible
          1 higham20P404SquareA higham20P404SquareB higham20P404SquareY
          (higham20P404SquareDeltaA (-1))
          (higham20P404SquareDeltaB 0)
          higham20_p404_square_ordinary_feasible_at_zero
      _ = 1 := hcost
  have hstrong : Real.sqrt 2 ≤
      lsMinimumNormBackwardErrorEtaF 1 higham20P404SquareA
        higham20P404SquareB higham20P404SquareY := by
    unfold lsMinimumNormBackwardErrorEtaF
    apply le_csInf
    · exact ⟨lsNormwiseBackwardErrorCostF 1
          (higham20P404SquareDeltaA 1) (higham20P404SquareDeltaB (-1)),
        lsMinimumNormBackwardErrorValuesF.mem_of_feasible
          1 higham20P404SquareA higham20P404SquareB higham20P404SquareY
          (higham20P404SquareDeltaA 1) (higham20P404SquareDeltaB (-1))
          higham20_p404_square_strong_feasible_at_two⟩
    · intro eta heta
      rcases heta with ⟨aM, dbv, hfeas, rfl⟩
      let a : ℝ := aM 0 0
      let d : ℝ := dbv 0
      have haM : aM = higham20P404SquareDeltaA a := by
        funext i j
        simp [a, higham20P404SquareDeltaA, Subsingleton.elim i 0,
          Subsingleton.elim j 0]
      have hdbv : dbv = higham20P404SquareDeltaB d := by
        funext i
        simp [d, higham20P404SquareDeltaB, Subsingleton.elim i 0]
      rw [haM, hdbv]
      exact higham20_p404_sqrt_two_le_square_strong_cost a d
        (by simpa [haM, hdbv] using hfeas)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsqrt_gt : 1 < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  refine ⟨hb, hy, hord, hstrong, ?_⟩
  intro heq
  rw [heq] at hstrong
  linarith

end NumStability
