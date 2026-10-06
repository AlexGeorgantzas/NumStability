-- Higham, 2nd ed., Chapter 20, equation (20.26): weighting limit.

import NumStability.Algorithms.LeastSquares.LSE

namespace NumStability

open scoped BigOperators

/-- A nonzero weight preserves the full-column-rank condition of the stacked
matrix `[A; B]`. -/
theorem lseWeightedMatrix_injective_of_lseStackedFullColumnRank
    {m n p : ℕ} {mu : ℝ}
    {A : Fin m → Fin n → ℝ} {B : Fin p → Fin n → ℝ}
    (hmu : mu ≠ 0) (hstack : LSEStackedFullColumnRank A B) :
    Function.Injective (rectMatMulVec (lseWeightedMatrix mu A B)) := by
  intro x y hxy
  apply hstack
  ext i
  refine Fin.addCases
    (motive := fun i : Fin (m + p) =>
      rectMatMulVec (lseStackedMatrix A B) x i =
        rectMatMulVec (lseStackedMatrix A B) y i)
    ?left ?right i
  · intro i
    have hi := congrFun hxy (Fin.castAdd p i)
    rw [lseWeightedMatrix_mulVec, lseWeightedMatrix_mulVec] at hi
    simpa [lseStackedMatrix_mulVec, Fin.append_left] using hi
  · intro i
    have hi := congrFun hxy (Fin.natAdd m i)
    rw [lseWeightedMatrix_mulVec, lseWeightedMatrix_mulVec] at hi
    have hBi : rectMatMulVec B x i = rectMatMulVec B y i := by
      apply mul_left_cancel₀ hmu
      simpa [Fin.append_right] using hi
    simpa [lseStackedMatrix_mulVec, Fin.append_right] using hBi

/-- The canonical exact solution of the weighted problem (20.26), obtained
from the nonsingular Gram inverse of `[A; mu B]`.  Its definition is total;
the source rank assumptions and `mu ≠ 0` prove that it is the unique
least-squares solution. -/
noncomputable def higham20WeightedSolution {m n p : ℕ}
    (mu : ℝ) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (d : Fin p → ℝ) : Fin n → ℝ :=
  let W := lseWeightedMatrix mu A B
  lsAugmentedInverseActionBottom
    (lsAplusOfGramNonsingInv W) (lsGramNonsingInv W)
    (lseWeightedRhs mu b d) 0

/-- The canonical Gram-inverse branch solves the weighted least-squares
problem for every nonzero weight under the source stacked-rank hypothesis. -/
theorem higham20WeightedSolution_isLeastSquaresMinimizer
    {m n p : ℕ} {mu : ℝ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (d : Fin p → ℝ)
    (hmu : mu ≠ 0) (hstack : LSEStackedFullColumnRank A B) :
    IsLeastSquaresMinimizer
      (lseWeightedMatrix mu A B) (lseWeightedRhs mu b d)
      (higham20WeightedSolution mu A b B d) := by
  let W := lseWeightedMatrix mu A B
  let rhs := lseWeightedRhs mu b d
  have hinj : Function.Injective (rectMatMulVec W) := by
    exact lseWeightedMatrix_injective_of_lseStackedFullColumnRank hmu hstack
  have haug :=
    LSAugmentedSystem.of_eq20_6_full_column_rank W rhs (0 : Fin n → ℝ) hinj
  exact LSAugmentedSystem.isLeastSquaresMinimizer_of_zero_rhs
    W rhs _ (higham20WeightedSolution mu A b B d) (by
      simpa [higham20WeightedSolution, W, rhs] using haug)

/-- Full column rank makes the squared least-squares minimizer unique. -/
theorem IsLeastSquaresMinimizer.eq_of_rectMatMulVec_injective
    {m n : ℕ} {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {x y : Fin n → ℝ}
    (hA : Function.Injective (rectMatMulVec A))
    (hx : IsLeastSquaresMinimizer A b x)
    (hy : IsLeastSquaresMinimizer A b y) :
    x = y := by
  let v : Fin n → ℝ := fun j => x j - y j
  have hx_eq : x = fun j => y j + v j := by
    ext j
    dsimp [v]
    ring
  have hobj : lsObjective A b x = lsObjective A b y :=
    le_antisymm (hx y) (hy x)
  have horth := (IsLeastSquaresMinimizer.rectLSNormalEquations hy).residual_orthogonal
  have hcross :
      (∑ j : Fin n,
        v j * (∑ i : Fin m, A i j * lsResidual A b y i)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [horth j]
    ring
  have hexp := lsObjective_add_direction_eq A b y v
  rw [← hx_eq, hcross] at hexp
  have hAvSq : vecNorm2Sq (rectMatMulVec A v) = 0 := by
    linarith
  have hAvNorm : vecNorm2 (rectMatMulVec A v) = 0 := by
    have hsquare : vecNorm2 (rectMatMulVec A v) ^ 2 = 0 := by
      rw [vecNorm2_sq, hAvSq]
    exact sq_eq_zero_iff.mp hsquare
  have hAv : rectMatMulVec A v = 0 := by
    ext i
    exact (vecNorm2_eq_zero_iff (rectMatMulVec A v)).mp hAvNorm i
  have hv : v = 0 := by
    apply hA
    calc
      rectMatMulVec A v = 0 := hAv
      _ = rectMatMulVec A 0 := by
        ext i
        simp [rectMatMulVec]
  ext j
  have hj := congrFun hv j
  dsimp [v] at hj
  linarith

/-- Each nonzero-weight problem in (20.26) has the canonical solution as its
unique minimizer under the source stacked-rank condition. -/
theorem higham20WeightedSolution_existsUnique_isLeastSquaresMinimizer
    {m n p : ℕ} {mu : ℝ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (d : Fin p → ℝ)
    (hmu : mu ≠ 0) (hstack : LSEStackedFullColumnRank A B) :
    ∃! x : Fin n → ℝ,
      IsLeastSquaresMinimizer
        (lseWeightedMatrix mu A B) (lseWeightedRhs mu b d) x := by
  let x := higham20WeightedSolution mu A b B d
  have hx : IsLeastSquaresMinimizer
      (lseWeightedMatrix mu A B) (lseWeightedRhs mu b d) x := by
    exact higham20WeightedSolution_isLeastSquaresMinimizer
      A b B d hmu hstack
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact IsLeastSquaresMinimizer.eq_of_rectMatMulVec_injective
    (lseWeightedMatrix_injective_of_lseStackedFullColumnRank hmu hstack)
    hy hx

/-- The basic penalty-energy estimate.  It is derived from weighted
optimality against the feasible LSE solution and the source Lagrange normal
equations; no boundedness or convergence hypothesis on the weighted branch is
used. -/
theorem lseWeightedMinimizer_energy_le_lagrange
    {m n p : ℕ} {mu : ℝ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {B : Fin p → Fin n → ℝ} {d : Fin p → ℝ}
    {x_mu y : Fin n → ℝ} {lambda : Fin p → ℝ}
    (hmin : IsLeastSquaresMinimizer
      (lseWeightedMatrix mu A B) (lseWeightedRhs mu b d) x_mu)
    (hy : IsLSEMinimizer A b B d y)
    (hlambda : ∀ j : Fin n,
      ∑ i : Fin m, A i j * lsResidualHigham A b y i =
        ∑ r : Fin p, B r j * lambda r) :
    vecNorm2 (rectMatMulVec A (fun j => x_mu j - y j)) ^ 2 +
        mu ^ 2 * vecNorm2 (rectMatMulVec B (fun j => x_mu j - y j)) ^ 2 ≤
      2 * vecNorm2 lambda *
        vecNorm2 (rectMatMulVec B (fun j => x_mu j - y j)) := by
  let v : Fin n → ℝ := fun j => x_mu j - y j
  have hx_eq : x_mu = fun j => y j + v j := by
    ext j
    dsimp [v]
    ring
  have hconstraint :
      lseConstraintResidual B d x_mu = rectMatMulVec B v := by
    ext r
    unfold lseConstraintResidual
    rw [congrFun (rectMatMulVec_sub B x_mu y) r, hy.1 r]
  have hhigham :
      (∑ j : Fin n,
        v j * (∑ i : Fin m, A i j * lsResidualHigham A b y i)) =
        ∑ r : Fin p, lambda r * rectMatMulVec B v r := by
    calc
      (∑ j : Fin n,
        v j * (∑ i : Fin m, A i j * lsResidualHigham A b y i)) =
          ∑ j : Fin n, v j * (∑ r : Fin p, B r j * lambda r) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [hlambda j]
      _ = ∑ j : Fin n, ∑ r : Fin p,
            v j * (B r j * lambda r) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
      _ = ∑ r : Fin p, ∑ j : Fin n,
            v j * (B r j * lambda r) := by
            rw [Finset.sum_comm]
      _ = ∑ r : Fin p, lambda r * rectMatMulVec B v r := by
            apply Finset.sum_congr rfl
            intro r _
            unfold rectMatMulVec
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
  have hcross :
      (∑ j : Fin n,
        v j * (∑ i : Fin m, A i j * lsResidual A b y i)) =
        -(∑ r : Fin p, lambda r * rectMatMulVec B v r) := by
    have hsign :
        (∑ j : Fin n,
          v j * (∑ i : Fin m, A i j * lsResidual A b y i)) =
          -(∑ j : Fin n,
            v j * (∑ i : Fin m, A i j * lsResidualHigham A b y i)) := by
      calc
        (∑ j : Fin n,
          v j * (∑ i : Fin m, A i j * lsResidual A b y i)) =
            ∑ j : Fin n,
              v j * (- (∑ i : Fin m,
                A i j * lsResidualHigham A b y i)) := by
                apply Finset.sum_congr rfl
                intro j _
                congr 1
                rw [lsResidualHigham_eq_neg_lsResidual A b y]
                simp
        _ = -(∑ j : Fin n,
            v j * (∑ i : Fin m, A i j * lsResidualHigham A b y i)) := by
              rw [← Finset.sum_neg_distrib]
              apply Finset.sum_congr rfl
              intro j _
              ring
    rw [hsign, hhigham]
  have hobj :
      lsObjective A b x_mu +
          mu ^ 2 * vecNorm2Sq (lseConstraintResidual B d x_mu) ≤
        lsObjective A b y := by
    calc
      lsObjective A b x_mu +
          mu ^ 2 * vecNorm2Sq (lseConstraintResidual B d x_mu) =
          lsObjective (lseWeightedMatrix mu A B)
            (lseWeightedRhs mu b d) x_mu :=
        (lseWeightedObjective_eq mu A b B d x_mu).symm
      _ ≤ lsObjective (lseWeightedMatrix mu A B)
            (lseWeightedRhs mu b d) y := hmin y
      _ = lsObjective A b y :=
        lseWeightedObjective_eq_of_feasible mu A b B d y hy.1
  have hexp := lsObjective_add_direction_eq A b y v
  rw [← hx_eq] at hexp
  rw [hexp, hcross, hconstraint] at hobj
  have hraw :
      vecNorm2Sq (rectMatMulVec A v) +
          mu ^ 2 * vecNorm2Sq (rectMatMulVec B v) ≤
        2 * (∑ r : Fin p, lambda r * rectMatMulVec B v r) := by
    linarith
  have hdot :
      (∑ r : Fin p, lambda r * rectMatMulVec B v r) ≤
        vecNorm2 lambda * vecNorm2 (rectMatMulVec B v) :=
    (le_abs_self _).trans
      (abs_vecInnerProduct_le_vecNorm2_mul lambda (rectMatMulVec B v))
  have hraw' := hraw.trans (mul_le_mul_of_nonneg_left hdot (by norm_num))
  simpa only [← vecNorm2_sq, v, mul_assoc] using hraw'

/-- The Euclidean square of the stacked action splits into the two row-block
squares. -/
theorem vecNorm2Sq_lseStackedMatrix_mulVec {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (x : Fin n → ℝ) :
    vecNorm2Sq (rectMatMulVec (lseStackedMatrix A B) x) =
      vecNorm2Sq (rectMatMulVec A x) + vecNorm2Sq (rectMatMulVec B x) := by
  rw [lseStackedMatrix_mulVec]
  unfold vecNorm2Sq
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

/-- Finite-weight convergence estimate for (20.26).  For `mu² ≥ 1`,
weighted optimality and the LSE multiplier give an explicit distance bound in
terms of the source stacked-rank lower margin. -/
theorem lseWeightedMinimizer_distance_le_sqrt_inv_sq
    {m n p : ℕ} {mu : ℝ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {B : Fin p → Fin n → ℝ} {d : Fin p → ℝ}
    {x_mu y : Fin n → ℝ} {lambda : Fin p → ℝ}
    (hstack : LSEStackedFullColumnRank A B)
    (hmin : IsLeastSquaresMinimizer
      (lseWeightedMatrix mu A B) (lseWeightedRhs mu b d) x_mu)
    (hy : IsLSEMinimizer A b B d y)
    (hlambda : ∀ j : Fin n,
      ∑ i : Fin m, A i j * lsResidualHigham A b y i =
        ∑ r : Fin p, B r j * lambda r)
    (hmuSq : 1 ≤ mu ^ 2) :
    vecNorm2 (fun j => x_mu j - y j) ≤
      Real.sqrt (4 * vecNorm2 lambda ^ 2 / mu ^ 2) /
        hstack.vecNorm2LowerMargin := by
  let v : Fin n → ℝ := fun j => x_mu j - y j
  let a : ℝ := vecNorm2 (rectMatMulVec A v)
  let c : ℝ := vecNorm2 (rectMatMulVec B v)
  let L : ℝ := vecNorm2 lambda
  have ha : 0 ≤ a := vecNorm2_nonneg _
  have hc : 0 ≤ c := vecNorm2_nonneg _
  have hL : 0 ≤ L := vecNorm2_nonneg _
  have hmuPos : 0 < mu ^ 2 := lt_of_lt_of_le zero_lt_one hmuSq
  have henergy : a ^ 2 + mu ^ 2 * c ^ 2 ≤ 2 * L * c := by
    simpa [a, c, L, v] using
      (lseWeightedMinimizer_energy_le_lagrange hmin hy hlambda)
  have hpenalty : mu ^ 2 * c ^ 2 ≤ 2 * L * c := by
    nlinarith [sq_nonneg a]
  have hc_bound : c ≤ 2 * L / mu ^ 2 := by
    by_cases hc0 : c = 0
    · rw [hc0]
      exact div_nonneg (mul_nonneg (by norm_num) hL) (le_of_lt hmuPos)
    · have hcPos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
      apply (le_div_iff₀ hmuPos).2
      have hcancel : c * (mu ^ 2 * c) ≤ c * (2 * L) := by
        simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hpenalty
      have hsmall := le_of_mul_le_mul_left hcancel hcPos
      simpa [mul_comm] using hsmall
  have hc_sq_weighted : c ^ 2 ≤ mu ^ 2 * c ^ 2 := by
    have := mul_le_mul_of_nonneg_right hmuSq (sq_nonneg c)
    simpa using this
  have hstack_energy : a ^ 2 + c ^ 2 ≤ 2 * L * c :=
    (add_le_add (le_refl (a ^ 2)) hc_sq_weighted).trans henergy
  have hupper : 2 * L * c ≤ 4 * L ^ 2 / mu ^ 2 := by
    calc
      2 * L * c ≤ 2 * L * (2 * L / mu ^ 2) :=
        mul_le_mul_of_nonneg_left hc_bound (mul_nonneg (by norm_num) hL)
      _ = 4 * L ^ 2 / mu ^ 2 := by ring
  have hsq : a ^ 2 + c ^ 2 ≤ 4 * L ^ 2 / mu ^ 2 :=
    hstack_energy.trans hupper
  have hstackNorm :
      vecNorm2 (rectMatMulVec (lseStackedMatrix A B) v) ≤
        Real.sqrt (4 * L ^ 2 / mu ^ 2) := by
    unfold vecNorm2
    apply Real.sqrt_le_sqrt
    rw [vecNorm2Sq_lseStackedMatrix_mulVec]
    simpa only [← vecNorm2_sq, a, c]
  have hlower := hstack.vecNorm2LowerMargin_lower_bound v
  apply (le_div_iff₀ hstack.vecNorm2LowerMargin_pos).2
  calc
    vecNorm2 v * hstack.vecNorm2LowerMargin =
        hstack.vecNorm2LowerMargin * vecNorm2 v := by ring
    _ ≤ vecNorm2 (rectMatMulVec (lseStackedMatrix A B) v) := hlower
    _ ≤ Real.sqrt (4 * L ^ 2 / mu ^ 2) := hstackNorm

/-- Source-facing closure of the limiting assertion following (20.26).

Under exactly the rank conditions (20.24), the concrete Gram-inverse formula
defines an exact weighted least-squares minimizer for every nonzero weight.
If the inverse squared weights tend to zero, this canonical branch converges
to the unique equality-constrained least-squares minimizer.  In particular,
branch existence, boundedness, and convergence are conclusions, not inputs. -/
theorem higham20_eq20_26_canonical_weighted_branch_tendsto_unique_lse
    {ι : Type*} {l : Filter ι} {r p q : ℕ}
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ) (d : Fin p → ℝ)
    (mu : ι → ℝ)
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B)
    (hmu : ∀ i, mu i ≠ 0)
    (hInvSq : Filter.Tendsto (fun i => (mu i ^ 2)⁻¹) l (nhds 0)) :
    (∀ i, IsLeastSquaresMinimizer
      (lseWeightedMatrix (mu i) A B) (lseWeightedRhs (mu i) b d)
      (higham20WeightedSolution (mu i) A b B d)) ∧
      ∃! y : Fin (p + q) → ℝ,
        IsLSEMinimizer A b B d y ∧
          Filter.Tendsto
            (fun i => higham20WeightedSolution (mu i) A b B d)
            l (nhds y) := by
  have hbranch : ∀ i, IsLeastSquaresMinimizer
      (lseWeightedMatrix (mu i) A B) (lseWeightedRhs (mu i) b d)
      (higham20WeightedSolution (mu i) A b B d) := by
    intro i
    exact higham20WeightedSolution_isLeastSquaresMinimizer
      A b B d (hmu i) hstack
  rcases exists_unique_lse_minimizer_of_fullRowRank_stackedFullColumnRank
      (A := A) (B := B) (b := b) (d := d) hB hstack with
    ⟨y, hy, hyuniq⟩
  rcases hy.exists_lagrange_normal_equations_of_fullRowRank hB with
    ⟨lambda, _hyfeas, hlambda⟩
  let C : ℝ := 4 * vecNorm2 lambda ^ 2
  let margin : ℝ := hstack.vecNorm2LowerMargin
  have hinside :
      Filter.Tendsto (fun i => C / mu i ^ 2) l (nhds 0) := by
    simpa [div_eq_mul_inv] using hInvSq.const_mul C
  have hsqrt :
      Filter.Tendsto (fun i => Real.sqrt (C / mu i ^ 2)) l (nhds 0) := by
    simpa using (Real.continuous_sqrt.tendsto 0).comp hinside
  have hboundlim :
      Filter.Tendsto
        (fun i => Real.sqrt (C / mu i ^ 2) / margin) l (nhds 0) := by
    simpa using hsqrt.div_const margin
  have hinvEventually : ∀ᶠ i in l, (mu i ^ 2)⁻¹ ≤ 1 := by
    have hdist := (Metric.tendsto_nhds.mp hInvSq) 1 (by norm_num)
    filter_upwards [hdist] with i hi
    have hnonneg : 0 ≤ (mu i ^ 2)⁻¹ :=
      inv_nonneg.mpr (sq_nonneg (mu i))
    have habs : |(mu i ^ 2)⁻¹| < 1 := by
      simpa [Real.dist_eq, abs_of_nonneg hnonneg] using hi
    exact le_of_lt ((le_abs_self _).trans_lt habs)
  have hmuSqEventually : ∀ᶠ i in l, 1 ≤ mu i ^ 2 := by
    filter_upwards [hinvEventually] with i hi
    exact (inv_le_one₀ (sq_pos_of_ne_zero (hmu i))).mp hi
  have hdistanceEventually : ∀ᶠ i in l,
      vecNorm2
          (fun j => higham20WeightedSolution (mu i) A b B d j - y j) ≤
        Real.sqrt (C / mu i ^ 2) / margin := by
    filter_upwards [hmuSqEventually] with i hi
    simpa [C, margin] using
      (lseWeightedMinimizer_distance_le_sqrt_inv_sq
        hstack (hbranch i) hy hlambda hi)
  have hnorm :
      Filter.Tendsto
        (fun i => vecNorm2
          (fun j => higham20WeightedSolution (mu i) A b B d j - y j))
        l (nhds 0) := by
    exact squeeze_zero'
      (Filter.Eventually.of_forall (fun _ => vecNorm2_nonneg _))
      hdistanceEventually hboundlim
  have hlim :
      Filter.Tendsto
        (fun i => higham20WeightedSolution (mu i) A b B d)
        l (nhds y) := by
    rw [tendsto_pi_nhds]
    intro j
    have habs :
        Filter.Tendsto
          (fun i =>
            |higham20WeightedSolution (mu i) A b B d j - y j|)
          l (nhds 0) := by
      refine squeeze_zero ?_ ?_ hnorm
      · intro i
        exact abs_nonneg _
      · intro i
        exact abs_coord_le_vecNorm2
          (fun k => higham20WeightedSolution (mu i) A b B d k - y k) j
    have hdiff :
        Filter.Tendsto
          (fun i => higham20WeightedSolution (mu i) A b B d j - y j)
          l (nhds 0) :=
      (tendsto_zero_iff_abs_tendsto_zero
        (f := fun i =>
          higham20WeightedSolution (mu i) A b B d j - y j)).2 (by
            simpa [Function.comp_def] using habs)
    simpa using hdiff.add_const (y j)
  refine ⟨hbranch, y, ⟨hy, hlim⟩, ?_⟩
  intro z hz
  exact hyuniq z hz.1

/-- Existential branch form of the preceding canonical theorem.  This is the
literal existence-and-limit statement asserted in the prose following
(20.26). -/
theorem higham20_eq20_26_exists_weighted_minimizer_branch_tendsto_unique_lse
    {ι : Type*} {l : Filter ι} {r p q : ℕ}
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ) (d : Fin p → ℝ)
    (mu : ι → ℝ)
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B)
    (hmu : ∀ i, mu i ≠ 0)
    (hInvSq : Filter.Tendsto (fun i => (mu i ^ 2)⁻¹) l (nhds 0)) :
    ∃ x_mu : ι → Fin (p + q) → ℝ,
      (∀ i, IsLeastSquaresMinimizer
        (lseWeightedMatrix (mu i) A B) (lseWeightedRhs (mu i) b d)
        (x_mu i)) ∧
      ∃! y : Fin (p + q) → ℝ,
        IsLSEMinimizer A b B d y ∧ Filter.Tendsto x_mu l (nhds y) := by
  refine ⟨fun i => higham20WeightedSolution (mu i) A b B d, ?_⟩
  exact higham20_eq20_26_canonical_weighted_branch_tendsto_unique_lse
    A b B d mu hB hstack hmu hInvSq

end NumStability
