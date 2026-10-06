/-
Chapter 11, Algorithm 11.2: the source-honest bridge from the actual selected
two-by-two GEPP solve to equation (11.5).

The older `FlMixedPivots` interface contains an additional exact absolute
coupling

  |w_i| |c_j| <= |w_i| |E| |w_j|.

That inequality is true for an exact solve `E w_j = c_j`, but it is not a
consequence of Higham's rounded-solve premise `(E + Delta E) w_j = c_j`.
This file records the implication that *is* valid, transports it to the actual
finite selector/GEPP producer, and gives a concrete small-unit-roundoff witness
showing why the stronger coupling cannot be used as the recursive handoff.
-/
import NumStability.Algorithms.Cholesky.Higham11BunchKaufmanExactTrace

open scoped BigOperators

namespace NumStability

/-! ## The exact consequence of equation (11.5) -/

/-- The absolute matrix-vector row envelope appearing in the componentwise
residual consequence of (11.5). -/
noncomputable def higham11_5_twoByTwoAbsRow
    (E : Fin 2 -> Fin 2 -> Real) (y : Fin 2 -> Real) (p : Fin 2) : Real :=
  ∑ q : Fin 2, |E p q| * |y q|

/-- Absolute bilinear envelope `|x|^T |E| |y|`. -/
noncomputable def higham11_5_twoByTwoAbsBilinear
    (x : Fin 2 -> Real) (E : Fin 2 -> Fin 2 -> Real)
    (y : Fin 2 -> Real) : Real :=
  ∑ p : Fin 2, ∑ q : Fin 2, |x p| * |E p q| * |y q|

/-- A componentwise backward-stable two-by-two solve gives the corresponding
componentwise residual bound.  This is the source-honest bridge from
`(E + Delta E)y = f`, `|Delta E| <= c u |E|` to (11.5)'s residual form. -/
theorem higham11_5_twoByTwoPivotSolveStable_residual
    (u c : Real) (E DeltaE : Fin 2 -> Fin 2 -> Real)
    (y f : Fin 2 -> Real)
    (hstable : higham11_5_twoByTwoPivotSolveStable u c E DeltaE)
    (heq : ∀ p : Fin 2, ∑ q : Fin 2, (E p q + DeltaE p q) * y q = f p) :
    ∀ p : Fin 2,
      |(∑ q : Fin 2, E p q * y q) - f p| <=
        c * u * higham11_5_twoByTwoAbsRow E y p := by
  intro p
  have hres :
      (∑ q : Fin 2, E p q * y q) - f p =
        -(∑ q : Fin 2, DeltaE p q * y q) := by
    rw [← heq p]
    simp_rw [add_mul, Finset.sum_add_distrib]
    ring
  rw [hres, abs_neg]
  calc
    |∑ q : Fin 2, DeltaE p q * y q| <=
        ∑ q : Fin 2, |DeltaE p q * y q| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ q : Fin 2, |DeltaE p q| * |y q| := by
      apply Finset.sum_congr rfl
      intro q _
      rw [abs_mul]
    _ <= ∑ q : Fin 2, (c * u * |E p q|) * |y q| := by
      apply Finset.sum_le_sum
      intro q _
      exact mul_le_mul_of_nonneg_right (hstable p q) (abs_nonneg _)
    _ = c * u * higham11_5_twoByTwoAbsRow E y p := by
      simp only [higham11_5_twoByTwoAbsRow, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring

/-- The corrected additive absolute coupling.  A rounded solve gives

`|x|^T |f| <= |x|^T |E| |y| + |x|^T |Delta E| |y|`,

not the same statement with the second term deleted. -/
theorem higham11_5_twoByTwoSolve_abs_coupling_additive
    (E DeltaE : Fin 2 -> Fin 2 -> Real) (x y f : Fin 2 -> Real)
    (heq : ∀ p : Fin 2, ∑ q : Fin 2, (E p q + DeltaE p q) * y q = f p) :
    (∑ p : Fin 2, |x p| * |f p|) <=
      higham11_5_twoByTwoAbsBilinear x E y +
        higham11_5_twoByTwoAbsBilinear x DeltaE y := by
  calc
    (∑ p : Fin 2, |x p| * |f p|) <=
        ∑ p : Fin 2, |x p| *
          (higham11_5_twoByTwoAbsRow E y p +
            higham11_5_twoByTwoAbsRow DeltaE y p) := by
      apply Finset.sum_le_sum
      intro p _
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      rw [← heq p]
      simp_rw [add_mul, Finset.sum_add_distrib]
      calc
        |(∑ q : Fin 2, E p q * y q) +
            ∑ q : Fin 2, DeltaE p q * y q| <=
            |∑ q : Fin 2, E p q * y q| +
              |∑ q : Fin 2, DeltaE p q * y q| := abs_add_le _ _
        _ <= (∑ q : Fin 2, |E p q * y q|) +
            ∑ q : Fin 2, |DeltaE p q * y q| :=
          add_le_add (Finset.abs_sum_le_sum_abs _ _)
            (Finset.abs_sum_le_sum_abs _ _)
        _ = higham11_5_twoByTwoAbsRow E y p +
            higham11_5_twoByTwoAbsRow DeltaE y p := by
          simp only [higham11_5_twoByTwoAbsRow, abs_mul]
    _ = higham11_5_twoByTwoAbsBilinear x E y +
        higham11_5_twoByTwoAbsBilinear x DeltaE y := by
      simp only [higham11_5_twoByTwoAbsRow,
        higham11_5_twoByTwoAbsBilinear, mul_add, Finset.sum_add_distrib]
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro p _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _
        ring
      · apply Finset.sum_congr rfl
        intro p _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _
        ring

/-- The perturbation term in the corrected coupling is controlled by the
componentwise (11.5) perturbation budget. -/
theorem higham11_5_twoByTwoAbsBilinear_perturbation_le
    (u c : Real) (E DeltaE : Fin 2 -> Fin 2 -> Real)
    (x y : Fin 2 -> Real)
    (hstable : higham11_5_twoByTwoPivotSolveStable u c E DeltaE) :
    higham11_5_twoByTwoAbsBilinear x DeltaE y <=
      c * u * higham11_5_twoByTwoAbsBilinear x E y := by
  calc
    higham11_5_twoByTwoAbsBilinear x DeltaE y <=
        ∑ p : Fin 2, ∑ q : Fin 2,
          |x p| * (c * u * |E p q|) * |y q| := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro q _
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hstable p q) (abs_nonneg _))
        (abs_nonneg _)
    _ = c * u * higham11_5_twoByTwoAbsBilinear x E y := by
      simp only [higham11_5_twoByTwoAbsBilinear, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      ring

/-- Source-valid multiplicative form of the corrected absolute coupling. -/
theorem higham11_5_twoByTwoPivotSolveStable_abs_coupling
    (u c : Real) (E DeltaE : Fin 2 -> Fin 2 -> Real)
    (x y f : Fin 2 -> Real)
    (hstable : higham11_5_twoByTwoPivotSolveStable u c E DeltaE)
    (heq : ∀ p : Fin 2, ∑ q : Fin 2, (E p q + DeltaE p q) * y q = f p) :
    (∑ p : Fin 2, |x p| * |f p|) <=
      (1 + c * u) * higham11_5_twoByTwoAbsBilinear x E y := by
  calc
    (∑ p : Fin 2, |x p| * |f p|) <=
        higham11_5_twoByTwoAbsBilinear x E y +
          higham11_5_twoByTwoAbsBilinear x DeltaE y :=
      higham11_5_twoByTwoSolve_abs_coupling_additive E DeltaE x y f heq
    _ <= higham11_5_twoByTwoAbsBilinear x E y +
        c * u * higham11_5_twoByTwoAbsBilinear x E y :=
      add_le_add_right
        (higham11_5_twoByTwoAbsBilinear_perturbation_le
          u c E DeltaE x y hstable)
        (higham11_5_twoByTwoAbsBilinear x E y)
    _ = (1 + c * u) * higham11_5_twoByTwoAbsBilinear x E y := by ring

/-! ## Actual Algorithm 11.2 case-(4) producer -/

/-- The actual selected GEPP solve at a case-(4) node satisfies the residual
form of equation (11.5), with the produced constant `36`.  No residual or
perturbation conclusion is assumed: both come from the executable solve. -/
theorem higham11_2_flSelectedTwoByTwoSolve_residual
    (fp : FPModel) (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2)
    {n : Nat} (hn : 0 < n) (A : Fin n -> Fin n -> Real)
    (hA : IsSymmetricFiniteMatrix A)
    (hbranch : higham11_2_bunchKaufmanFirstBranch hn
      higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case4)
    (hsecond : higham11_2_flSelectedTwoByTwoSecondPivot fp hn A ≠ 0)
    (z : Fin n -> Real) :
    ∀ p : Fin 2,
      |(∑ q : Fin 2,
          higham11_2_bunchKaufmanSelectedTwoBlock hn A p q *
            higham11_2_flSelectedTwoByTwoSolve fp hn A z q) -
        z (Fin.cases (higham11_2_firstIndex hn)
          (fun _ => higham11_2_bunchKaufmanMaxRow hn A) p)| <=
      36 * fp.u *
        higham11_5_twoByTwoAbsRow
          (higham11_2_bunchKaufmanSelectedTwoBlock hn A)
          (higham11_2_flSelectedTwoByTwoSolve fp hn A z) p := by
  obtain ⟨DeltaE, hstable, heq⟩ :=
    higham11_2_flSelectedTwoByTwoSolve_higham115 fp hval9 hsmall9
      hn A hA z hbranch hsecond
  exact higham11_5_twoByTwoPivotSolveStable_residual
    fp.u 36 (higham11_2_bunchKaufmanSelectedTwoBlock hn A) DeltaE
    (higham11_2_flSelectedTwoByTwoSolve fp hn A z)
    (fun p => z (Fin.cases (higham11_2_firstIndex hn)
      (fun _ => higham11_2_bunchKaufmanMaxRow hn A) p))
    hstable heq

/-- The actual selected GEPP solve supplies the corrected absolute coupling,
including the unavoidable `(1 + 36 u)` factor. -/
theorem higham11_2_flSelectedTwoByTwoSolve_abs_coupling
    (fp : FPModel) (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2)
    {n : Nat} (hn : 0 < n) (A : Fin n -> Fin n -> Real)
    (hA : IsSymmetricFiniteMatrix A)
    (hbranch : higham11_2_bunchKaufmanFirstBranch hn
      higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case4)
    (hsecond : higham11_2_flSelectedTwoByTwoSecondPivot fp hn A ≠ 0)
    (z : Fin n -> Real) (x : Fin 2 -> Real) :
    (∑ p : Fin 2, |x p| *
      |z (Fin.cases (higham11_2_firstIndex hn)
        (fun _ => higham11_2_bunchKaufmanMaxRow hn A) p)|) <=
      (1 + 36 * fp.u) *
        higham11_5_twoByTwoAbsBilinear x
          (higham11_2_bunchKaufmanSelectedTwoBlock hn A)
          (higham11_2_flSelectedTwoByTwoSolve fp hn A z) := by
  obtain ⟨DeltaE, hstable, heq⟩ :=
    higham11_2_flSelectedTwoByTwoSolve_higham115 fp hval9 hsmall9
      hn A hA z hbranch hsecond
  exact higham11_5_twoByTwoPivotSolveStable_abs_coupling
    fp.u 36 (higham11_2_bunchKaufmanSelectedTwoBlock hn A) DeltaE x
    (higham11_2_flSelectedTwoByTwoSolve fp hn A z)
    (fun p => z (Fin.cases (higham11_2_firstIndex hn)
      (fun _ => higham11_2_bunchKaufmanMaxRow hn A) p))
    hstable heq

/-- Residual-form certificate at every selected two-by-two node of an exact
Algorithm 11.2 selector trace.  This predicate deliberately records the local
rounded solve theorem, not the stronger `FlMixedPivots` absolute coupling. -/
noncomputable def Higham11ExactBunchKaufmanTrace.allSelectedTwoResidualsBounded
    (fp : FPModel) : {n : Nat} ->
    {A : Higham11BunchKaufmanMatrix n} ->
    Higham11ExactBunchKaufmanTrace A -> Prop
  | _, _, .nil _ => True
  | _, _, .noAction _ _ _ tail => tail.allSelectedTwoResidualsBounded fp
  | _, _, .case1 _ _ _ tail => tail.allSelectedTwoResidualsBounded fp
  | _, _, .case2 _ _ _ tail => tail.allSelectedTwoResidualsBounded fp
  | _, _, .case3 _ _ _ tail => tail.allSelectedTwoResidualsBounded fp
  | _, _, .case4 A _ _ tail =>
      (∀ z : Fin (_ + 2) -> Real, ∀ p : Fin 2,
        |(∑ q : Fin 2,
            higham11_2_bunchKaufmanSelectedTwoBlock (by omega) A p q *
              higham11_2_flSelectedTwoByTwoSolve fp (by omega) A z q) -
          z (Fin.cases (higham11_2_firstIndex (by omega))
            (fun _ => higham11_2_bunchKaufmanMaxRow (by omega) A) p)| <=
        36 * fp.u *
          higham11_5_twoByTwoAbsRow
            (higham11_2_bunchKaufmanSelectedTwoBlock (by omega) A)
            (higham11_2_flSelectedTwoByTwoSolve fp (by omega) A z) p) ∧
      tail.allSelectedTwoResidualsBounded fp

/-- The actual recursive selector trace produces the source-valid residual
certificate at every case-(4) node under the genuine GEPP run domain. -/
theorem Higham11ExactBunchKaufmanTrace.allSelectedTwoResidualsBounded_of_runDomain
    (fp : FPModel) (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2) :
    ∀ {n : Nat} {A : Higham11BunchKaufmanMatrix n}
      (trace : Higham11ExactBunchKaufmanTrace A),
      trace.twoSolveRunDomain fp -> trace.allSelectedTwoResidualsBounded fp := by
  intro n A trace
  induction trace with
  | nil => simp [Higham11ExactBunchKaufmanTrace.twoSolveRunDomain,
      Higham11ExactBunchKaufmanTrace.allSelectedTwoResidualsBounded]
  | noAction A hA hbranch tail ih =>
      simpa [Higham11ExactBunchKaufmanTrace.twoSolveRunDomain,
        Higham11ExactBunchKaufmanTrace.allSelectedTwoResidualsBounded] using ih
  | case1 A hA hbranch tail ih =>
      simpa [Higham11ExactBunchKaufmanTrace.twoSolveRunDomain,
        Higham11ExactBunchKaufmanTrace.allSelectedTwoResidualsBounded] using ih
  | case2 A hA hbranch tail ih =>
      simpa [Higham11ExactBunchKaufmanTrace.twoSolveRunDomain,
        Higham11ExactBunchKaufmanTrace.allSelectedTwoResidualsBounded] using ih
  | case3 A hA hbranch tail ih =>
      simpa [Higham11ExactBunchKaufmanTrace.twoSolveRunDomain,
        Higham11ExactBunchKaufmanTrace.allSelectedTwoResidualsBounded] using ih
  | case4 A hA hbranch tail ih =>
      intro hrun
      rcases hrun with ⟨hsecond, htail⟩
      refine ⟨?_, ih htail⟩
      intro z p
      exact higham11_2_flSelectedTwoByTwoSolve_residual
        fp hval9 hsmall9 (by omega) A hA hbranch hsecond z p

/-- Corrected absolute-coupling certificate at every selected two-by-two node
of the recursive exact selector trace.  The factor `(1 + 36 u)` is essential:
the exact coefficient-one coupling in `FlMixedPivots` is not a consequence of
the rounded solve model. -/
noncomputable def Higham11ExactBunchKaufmanTrace.allSelectedTwoCouplingsBounded
    (fp : FPModel) : {n : Nat} ->
    {A : Higham11BunchKaufmanMatrix n} ->
    Higham11ExactBunchKaufmanTrace A -> Prop
  | _, _, .nil _ => True
  | _, _, .noAction _ _ _ tail => tail.allSelectedTwoCouplingsBounded fp
  | _, _, .case1 _ _ _ tail => tail.allSelectedTwoCouplingsBounded fp
  | _, _, .case2 _ _ _ tail => tail.allSelectedTwoCouplingsBounded fp
  | _, _, .case3 _ _ _ tail => tail.allSelectedTwoCouplingsBounded fp
  | _, _, .case4 A _ _ tail =>
      (∀ z : Fin (_ + 2) -> Real, ∀ x : Fin 2 -> Real,
        (∑ p : Fin 2, |x p| *
          |z (Fin.cases (higham11_2_firstIndex (by omega))
            (fun _ => higham11_2_bunchKaufmanMaxRow (by omega) A) p)|) <=
          (1 + 36 * fp.u) *
            higham11_5_twoByTwoAbsBilinear x
              (higham11_2_bunchKaufmanSelectedTwoBlock (by omega) A)
              (higham11_2_flSelectedTwoByTwoSolve fp (by omega) A z)) ∧
      tail.allSelectedTwoCouplingsBounded fp

/-- The actual recursive selector trace produces the corrected `(1 + 36 u)`
absolute coupling at every case-(4) node under the genuine GEPP run domain. -/
theorem Higham11ExactBunchKaufmanTrace.allSelectedTwoCouplingsBounded_of_runDomain
    (fp : FPModel) (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2) :
    ∀ {n : Nat} {A : Higham11BunchKaufmanMatrix n}
      (trace : Higham11ExactBunchKaufmanTrace A),
      trace.twoSolveRunDomain fp -> trace.allSelectedTwoCouplingsBounded fp := by
  intro n A trace
  induction trace with
  | nil => simp [Higham11ExactBunchKaufmanTrace.twoSolveRunDomain,
      Higham11ExactBunchKaufmanTrace.allSelectedTwoCouplingsBounded]
  | noAction A hA hbranch tail ih =>
      simpa [Higham11ExactBunchKaufmanTrace.twoSolveRunDomain,
        Higham11ExactBunchKaufmanTrace.allSelectedTwoCouplingsBounded] using ih
  | case1 A hA hbranch tail ih =>
      simpa [Higham11ExactBunchKaufmanTrace.twoSolveRunDomain,
        Higham11ExactBunchKaufmanTrace.allSelectedTwoCouplingsBounded] using ih
  | case2 A hA hbranch tail ih =>
      simpa [Higham11ExactBunchKaufmanTrace.twoSolveRunDomain,
        Higham11ExactBunchKaufmanTrace.allSelectedTwoCouplingsBounded] using ih
  | case3 A hA hbranch tail ih =>
      simpa [Higham11ExactBunchKaufmanTrace.twoSolveRunDomain,
        Higham11ExactBunchKaufmanTrace.allSelectedTwoCouplingsBounded] using ih
  | case4 A hA hbranch tail ih =>
      intro hrun
      rcases hrun with ⟨hsecond, htail⟩
      refine ⟨?_, ih htail⟩
      intro z x
      exact higham11_2_flSelectedTwoByTwoSolve_abs_coupling
        fp hval9 hsmall9 (by omega) A hA hbranch hsecond z x

/-! ## Why the old exact absolute coupling is not a consequence of (11.5) -/

/-- Even with `u = 1/1000`, a solve can satisfy the literal componentwise
equation-(11.5) perturbation model while the exact absolute coupling used by
`FlMixedPivots` fails.  Here `E = I`, `Delta E = u I`,
`y = (1000/1001,0)`, and `f = (1,0)`.

Thus a producer of Higham's (11.5) premise cannot honestly discharge that
field without an additive `|w_i||Delta E||w_j|` allowance. -/
theorem higham11_5_stable_solve_does_not_imply_exact_abs_coupling :
    ∃ (u c : Real) (E DeltaE : Fin 2 -> Fin 2 -> Real)
      (y f : Fin 2 -> Real),
      u = 1 / 1000 ∧ c = 1 ∧
      higham11_5_twoByTwoPivotSolveStable u c E DeltaE ∧
      (∀ p : Fin 2, ∑ q : Fin 2, (E p q + DeltaE p q) * y q = f p) ∧
      ¬ (|y 0| * |f 0| + |y 1| * |f 1| <=
        ∑ p : Fin 2, ∑ q : Fin 2, |y p| * |E p q| * |y q|) := by
  let E : Fin 2 -> Fin 2 -> Real := fun i j => if i = j then 1 else 0
  let DeltaE : Fin 2 -> Fin 2 -> Real :=
    fun i j => if i = j then 1 / 1000 else 0
  let y : Fin 2 -> Real := fun i => if i = 0 then 1000 / 1001 else 0
  let f : Fin 2 -> Real := fun i => if i = 0 then 1 else 0
  refine ⟨1 / 1000, 1, E, DeltaE, y, f, rfl, rfl, ?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [E, DeltaE]
  · intro p
    fin_cases p <;>
      norm_num [E, DeltaE, y, f, Fin.sum_univ_two] <;> rfl
  · norm_num [E, y, f, Fin.sum_univ_two]

end NumStability
