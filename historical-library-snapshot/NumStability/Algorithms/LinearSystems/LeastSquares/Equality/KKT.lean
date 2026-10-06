import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.LeastSquares.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.Equality.Basic
import NumStability.Analysis.MatrixAlgebra

namespace NumStability

open scoped BigOperators

/-!
# KKT

Canonical reusable module extracted without change from LSE.
-/

/-- Source augmented KKT system for the equality-constrained least-squares
    operator in Higham, 2nd ed., Chapter 20, equations (20.23)-(20.25).

    The unknowns are a residual-like vector `dr`, a solution difference `dx`,
    and a multiplier difference `dlambda`; the right-hand sides are the data,
    stationarity, and constraint rows of the source augmented system. -/
def LSEKKTSystem {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (f : Fin m → ℝ) (g : Fin n → ℝ) (c : Fin p → ℝ)
    (dr : Fin m → ℝ) (dx : Fin n → ℝ) (dlambda : Fin p → ℝ) : Prop :=
  (∀ i : Fin m, dr i + rectMatMulVec A dx i = f i) ∧
  (∀ j : Fin n,
    (∑ i : Fin m, A i j * dr i) -
      (∑ r : Fin p, B r j * dlambda r) = g j) ∧
  (∀ r : Fin p, rectMatMulVec B dx r = c r)
/-- The square linear operator behind `LSEKKTSystem`.

    It maps `(dr, dx, dlambda)` to the three source augmented KKT rows:
    `dr + A*dx`, `A^T*dr - B^T*dlambda`, and `B*dx`. -/
noncomputable def LSEKKTLinearMap {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ) :
    ((Fin m → ℝ) × (Fin n → ℝ) × (Fin p → ℝ)) →ₗ[ℝ]
      ((Fin m → ℝ) × (Fin n → ℝ) × (Fin p → ℝ)) where
  toFun z :=
    (fun i : Fin m => z.1 i + rectMatMulVec A z.2.1 i,
      fun j : Fin n =>
        (∑ i : Fin m, A i j * z.1 i) -
          (∑ r : Fin p, B r j * z.2.2 r),
      fun r : Fin p => rectMatMulVec B z.2.1 r)
  map_add' := by
    intro u v
    apply Prod.ext
    · ext i
      dsimp
      have hmul :
          rectMatMulVec A (u.2.1 + v.2.1) i =
            rectMatMulVec A u.2.1 i + rectMatMulVec A v.2.1 i := by
        simpa using congrFun (rectMatMulVec_add A u.2.1 v.2.1) i
      rw [hmul]
      ring
    · apply Prod.ext
      · ext j
        dsimp
        have hAadd :
            (∑ i : Fin m, A i j * (u.1 i + v.1 i)) =
              (∑ i : Fin m, A i j * u.1 i) +
                (∑ i : Fin m, A i j * v.1 i) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring
        have hBadd :
            (∑ r : Fin p, B r j * (u.2.2 r + v.2.2 r)) =
              (∑ r : Fin p, B r j * u.2.2 r) +
                (∑ r : Fin p, B r j * v.2.2 r) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro r _
          ring
        rw [hAadd, hBadd]
        ring
      · ext r
        dsimp
        have hmul :
            rectMatMulVec B (u.2.1 + v.2.1) r =
              rectMatMulVec B u.2.1 r + rectMatMulVec B v.2.1 r := by
          simpa using congrFun (rectMatMulVec_add B u.2.1 v.2.1) r
        exact hmul
  map_smul' := by
    intro a u
    apply Prod.ext
    · ext i
      dsimp
      have hmul :
          rectMatMulVec A (a • u.2.1) i =
            a * rectMatMulVec A u.2.1 i := by
        simpa using congrFun (rectMatMulVec_smul A a u.2.1) i
      rw [hmul]
      ring
    · apply Prod.ext
      · ext j
        dsimp
        have hAsmul :
            (∑ i : Fin m, A i j * (a * u.1 i)) =
              a * (∑ i : Fin m, A i j * u.1 i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        have hBsmul :
            (∑ r : Fin p, B r j * (a * u.2.2 r)) =
              a * (∑ r : Fin p, B r j * u.2.2 r) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r _
          ring
        rw [hAsmul, hBsmul]
        ring
      · ext r
        dsimp
        have hmul :
            rectMatMulVec B (a • u.2.1) r =
              a * rectMatMulVec B u.2.1 r := by
          simpa using congrFun (rectMatMulVec_smul B a u.2.1) r
        exact hmul
/-- Component form of the source KKT linear-map equation. -/
theorem LSEKKTSystem.iff_linearMap_eq {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (f : Fin m → ℝ) (g : Fin n → ℝ) (c : Fin p → ℝ)
    (dr : Fin m → ℝ) (dx : Fin n → ℝ) (dlambda : Fin p → ℝ) :
    LSEKKTSystem A B f g c dr dx dlambda ↔
      LSEKKTLinearMap A B (dr, dx, dlambda) = (f, g, c) := by
  constructor
  · intro hsys
    rcases hsys with ⟨htop, hstat, hconstr⟩
    apply Prod.ext
    · ext i
      exact htop i
    · apply Prod.ext
      · ext j
        exact hstat j
      · ext r
        exact hconstr r
  · intro hmap
    constructor
    · intro i
      exact congrFun (congrArg Prod.fst hmap) i
    · constructor
      · intro j
        exact congrFun (congrArg Prod.fst (congrArg Prod.snd hmap)) j
      · intro r
        exact congrFun (congrArg Prod.snd (congrArg Prod.snd hmap)) r
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    KKT difference equations for the Cox--Higham augmented-system route.

    Source and perturbed LSE minimizers have Lagrange multipliers whose
    difference satisfies the source augmented-system equations.  The right-hand
    sides are exactly the data, constraint, and stationarity perturbation terms
    that the block inverse in the Cox--Higham proof acts on. -/
theorem IsLSEMinimizer.exists_lagrange_kkt_difference_system_of_fullRowRank
    {m n p : ℕ}
    {A DeltaA : Fin m → Fin n → ℝ} {b Deltab : Fin m → ℝ}
    {B DeltaB : Fin p → Fin n → ℝ} {d Deltad : Fin p → ℝ}
    {x y : Fin n → ℝ}
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hB : LSEFullRowRank B)
    (hBpert : LSEFullRowRank (fun i j => B i j + DeltaB i j)) :
    ∃ lambda mu : Fin p → ℝ,
      (∀ i : Fin m,
        lsResidualHigham (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i) y i -
            lsResidualHigham A b x i +
          rectMatMulVec A (fun j => y j - x j) i =
        Deltab i - rectMatMulVec DeltaA y i) ∧
      (∀ j : Fin n,
        (∑ i : Fin m,
            A i j *
              (lsResidualHigham (fun i j => A i j + DeltaA i j)
                  (fun i => b i + Deltab i) y i -
                lsResidualHigham A b x i)) -
          (∑ r : Fin p, B r j * (mu r - lambda r)) =
        (∑ r : Fin p, DeltaB r j * mu r) -
          (∑ i : Fin m,
            DeltaA i j *
              lsResidualHigham (fun i j => A i j + DeltaA i j)
                (fun i => b i + Deltab i) y i)) ∧
      (∀ r : Fin p,
        rectMatMulVec B (fun j => y j - x j) r =
          Deltad r - rectMatMulVec DeltaB y r) := by
  rcases hx.exists_lagrange_normal_equations_of_fullRowRank hB with
    ⟨lambda, hxfeas, hlambda⟩
  rcases hy.exists_lagrange_normal_equations_of_fullRowRank hBpert with
    ⟨mu, hyfeas, hmu⟩
  refine ⟨lambda, mu, ?_, ?_, ?_⟩
  · intro i
    unfold lsResidualHigham
    rw [congrFun (rectMatMulVec_mat_add A DeltaA y) i]
    rw [congrFun (rectMatMulVec_sub A y x) i]
    ring
  · intro j
    let s : Fin m → ℝ :=
      lsResidualHigham (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) y
    let rsrc : Fin m → ℝ := lsResidualHigham A b x
    have hmu_expand :
        (∑ i : Fin m, A i j * s i) +
            (∑ i : Fin m, DeltaA i j * s i) =
          (∑ r : Fin p, B r j * mu r) +
            (∑ r : Fin p, DeltaB r j * mu r) := by
      calc
        (∑ i : Fin m, A i j * s i) +
            (∑ i : Fin m, DeltaA i j * s i)
            = ∑ i : Fin m, (A i j + DeltaA i j) * s i := by
                rw [← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro i _
                ring
        _ = ∑ r : Fin p, (B r j + DeltaB r j) * mu r := hmu j
        _ = (∑ r : Fin p, B r j * mu r) +
              (∑ r : Fin p, DeltaB r j * mu r) := by
                rw [← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro r _
                ring
    have hlambda_j :
        (∑ i : Fin m, A i j * rsrc i) =
          ∑ r : Fin p, B r j * lambda r := hlambda j
    have hsumA :
        (∑ i : Fin m, A i j * (s i - rsrc i)) =
          (∑ i : Fin m, A i j * s i) -
            (∑ i : Fin m, A i j * rsrc i) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hsumB :
        (∑ r : Fin p, B r j * (mu r - lambda r)) =
          (∑ r : Fin p, B r j * mu r) -
            (∑ r : Fin p, B r j * lambda r) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro r _
      ring
    change
      (∑ i : Fin m, A i j * (s i - rsrc i)) -
          (∑ r : Fin p, B r j * (mu r - lambda r)) =
        (∑ r : Fin p, DeltaB r j * mu r) -
          (∑ i : Fin m, DeltaA i j * s i)
    rw [hsumA, hsumB]
    linarith
  · intro r
    have hpert_r := hyfeas r
    have hsrc_r := hxfeas r
    rw [congrFun (rectMatMulVec_mat_add B DeltaB y) r] at hpert_r
    rw [congrFun (rectMatMulVec_sub B y x) r]
    linarith
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    package the Cox--Higham KKT difference equations as one source augmented
    KKT system.  This is the system to which the later block inverse/norm bound
    is applied. -/
theorem IsLSEMinimizer.exists_lagrange_kkt_difference_source_system_of_fullRowRank
    {m n p : ℕ}
    {A DeltaA : Fin m → Fin n → ℝ} {b Deltab : Fin m → ℝ}
    {B DeltaB : Fin p → Fin n → ℝ} {d Deltad : Fin p → ℝ}
    {x y : Fin n → ℝ}
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hB : LSEFullRowRank B)
    (hBpert : LSEFullRowRank (fun i j => B i j + DeltaB i j)) :
    ∃ lambda mu : Fin p → ℝ,
      LSEKKTSystem A B
        (fun i => Deltab i - rectMatMulVec DeltaA y i)
        (fun j =>
          (∑ r : Fin p, DeltaB r j * mu r) -
            (∑ i : Fin m,
              DeltaA i j *
                lsResidualHigham (fun i j => A i j + DeltaA i j)
                  (fun i => b i + Deltab i) y i))
        (fun r => Deltad r - rectMatMulVec DeltaB y r)
        (fun i =>
          lsResidualHigham (fun i j => A i j + DeltaA i j)
              (fun i => b i + Deltab i) y i -
            lsResidualHigham A b x i)
        (fun j => y j - x j)
        (fun r => mu r - lambda r) := by
  rcases hx.exists_lagrange_kkt_difference_system_of_fullRowRank hy hB hBpert with
    ⟨lambda, mu, htop, hstat, hconstr⟩
  exact ⟨lambda, mu, htop, hstat, hconstr⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    the Cox--Higham KKT difference system together with the source normal
    equations for the same source Lagrange multiplier.  This exposes the
    certificate needed to bound the source multiplier from the source residual
    rather than postulating its scale separately. -/
theorem
    IsLSEMinimizer.exists_lagrange_kkt_difference_source_system_of_fullRowRank_sourceNormal
    {m n p : ℕ}
    {A DeltaA : Fin m → Fin n → ℝ} {b Deltab : Fin m → ℝ}
    {B DeltaB : Fin p → Fin n → ℝ} {d Deltad : Fin p → ℝ}
    {x y : Fin n → ℝ}
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hB : LSEFullRowRank B)
    (hBpert : LSEFullRowRank (fun i j => B i j + DeltaB i j)) :
    ∃ lambda mu : Fin p → ℝ,
      (∀ j : Fin n,
        ∑ i : Fin m, A i j * lsResidualHigham A b x i =
          ∑ r : Fin p, B r j * lambda r) ∧
      LSEKKTSystem A B
        (fun i => Deltab i - rectMatMulVec DeltaA y i)
        (fun j =>
          (∑ r : Fin p, DeltaB r j * mu r) -
            (∑ i : Fin m,
              DeltaA i j *
                lsResidualHigham (fun i j => A i j + DeltaA i j)
                  (fun i => b i + Deltab i) y i))
        (fun r => Deltad r - rectMatMulVec DeltaB y r)
        (fun i =>
          lsResidualHigham (fun i j => A i j + DeltaA i j)
              (fun i => b i + Deltab i) y i -
            lsResidualHigham A b x i)
        (fun j => y j - x j)
        (fun r => mu r - lambda r) := by
  rcases hx.exists_lagrange_normal_equations_of_fullRowRank hB with
    ⟨lambda, hxfeas, hlambda⟩
  rcases hy.exists_lagrange_normal_equations_of_fullRowRank hBpert with
    ⟨mu, hyfeas, hmu⟩
  refine ⟨lambda, mu, hlambda, ?_, ?_, ?_⟩
  · intro i
    unfold lsResidualHigham
    dsimp
    rw [congrFun (rectMatMulVec_mat_add A DeltaA y) i]
    rw [congrFun (rectMatMulVec_sub A y x) i]
    ring
  · intro j
    let s : Fin m → ℝ :=
      lsResidualHigham (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) y
    let rsrc : Fin m → ℝ := lsResidualHigham A b x
    have hmu_expand :
        (∑ i : Fin m, A i j * s i) +
            (∑ i : Fin m, DeltaA i j * s i) =
          (∑ r : Fin p, B r j * mu r) +
            (∑ r : Fin p, DeltaB r j * mu r) := by
      calc
        (∑ i : Fin m, A i j * s i) +
            (∑ i : Fin m, DeltaA i j * s i)
            = ∑ i : Fin m, (A i j + DeltaA i j) * s i := by
                rw [← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro i _
                ring
        _ = ∑ r : Fin p, (B r j + DeltaB r j) * mu r := hmu j
        _ = (∑ r : Fin p, B r j * mu r) +
              (∑ r : Fin p, DeltaB r j * mu r) := by
                rw [← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro r _
                ring
    have hlambda_j :
        (∑ i : Fin m, A i j * rsrc i) =
          ∑ r : Fin p, B r j * lambda r := hlambda j
    have hsumA :
        (∑ i : Fin m, A i j * (s i - rsrc i)) =
          (∑ i : Fin m, A i j * s i) -
            (∑ i : Fin m, A i j * rsrc i) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hsumB :
        (∑ r : Fin p, B r j * (mu r - lambda r)) =
          (∑ r : Fin p, B r j * mu r) -
            (∑ r : Fin p, B r j * lambda r) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro r _
      ring
    change
      (∑ i : Fin m, A i j * (s i - rsrc i)) -
          (∑ r : Fin p, B r j * (mu r - lambda r)) =
        (∑ r : Fin p, DeltaB r j * mu r) -
          (∑ i : Fin m, DeltaA i j * s i)
    rw [hsumA, hsumB]
    linarith
  · intro r
    have hpert_r := hyfeas r
    have hsrc_r := hxfeas r
    rw [congrFun (rectMatMulVec_mat_add B DeltaB y) r] at hpert_r
    rw [congrFun (rectMatMulVec_sub B y x) r]
    linarith

end NumStability
