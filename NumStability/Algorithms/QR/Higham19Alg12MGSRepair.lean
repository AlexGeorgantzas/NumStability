import NumStability.Algorithms.QR.Higham19Alg12MGSRounded

/-!
# Quantitative polar repair for rounded modified Gram--Schmidt

This module closes the local-to-global bridge for the literal floating-point
implementation of Higham Algorithm 19.12.  The repair coefficient below is
not defined from the realized repair residual.  It is the sum of two explicit
majorants:

* the telescoped local update/projection/division budget recorded by
  `ModifiedGramSchmidtRoundedState`; and
* a supplied bound on the computed right-Gram defect, multiplied by the
  computed `R`-column norm.

Thus a separate orthogonality analysis may discharge the Gram-defect premise
without assuming the desired global repair conclusion.
-/

namespace NumStability

open scoped BigOperators

noncomputable section

/-- Primitive per-column numerator for the polar repair.  The first summand
is determined by the local rounded MGS trace.  The second is the action bound
obtained from `||I - Qhat^T Qhat||_F <= gramCoeff * u` and the polar resolvent.
-/
noncomputable def mgsRoundedLocalGramRepairColumnBudget {m n : Nat}
    (fp : FPModel) (Qhat : Fin m -> Fin n -> Real)
    (Rhat : Fin n -> Fin n -> Real)
    (V : Nat -> Fin n -> Fin m -> Real)
    (gramCoeff : Real) (j : Fin n) : Real :=
  vecNorm2 (mgsRoundedProductEntryBudget fp Qhat V j) +
    (gramCoeff * fp.u) * columnFrob Rhat j

/-- Source-relative coefficient obtained from the explicit local/Gram
numerators.  Source-column positivity is required by the producer because a
relative columnwise bound cannot divide by a zero source column. -/
noncomputable def mgsRoundedLocalGramRepairRelativeBudget {m n : Nat}
    (fp : FPModel) (A Qhat : Fin m -> Fin n -> Real)
    (Rhat : Fin n -> Fin n -> Real)
    (V : Nat -> Fin n -> Fin m -> Real)
    (gramCoeff : Real) : Real :=
  Finset.univ.sum fun j : Fin n =>
    mgsRoundedLocalGramRepairColumnBudget fp Qhat Rhat V gramCoeff j /
      columnFrob A j

/-- The concrete polar perturbation is bounded by the local rounded-state
accumulation budget plus the primitive Gram-defect coefficient acting on the
computed `Rhat` column. -/
theorem ModifiedGramSchmidtRoundedState.globalRepairDelta_columnFrob_le_localGram
    {m n : Nat} {fp : FPModel}
    {A Qhat : Fin m -> Fin n -> Real}
    {Rhat : Fin n -> Fin n -> Real}
    {V : Nat -> Fin n -> Fin m -> Real}
    (hstate : ModifiedGramSchmidtRoundedState fp A Qhat Rhat V)
    (hdiag : forall k : Fin n, Ne (Rhat k k) 0)
    (hnm : n <= m) (gramCoeff : Real)
    (hgram : mgsRoundedPolarSensitivityBudget Qhat <= gramCoeff * fp.u)
    (j : Fin n) :
    columnFrob (mgsRoundedGlobalRepairDelta A Qhat Rhat hnm) j <=
      mgsRoundedLocalGramRepairColumnBudget fp Qhat Rhat V gramCoeff j := by
  calc
    columnFrob (mgsRoundedGlobalRepairDelta A Qhat Rhat hnm) j <=
        columnFrob (mgsRoundedProductResidual A Qhat Rhat) j +
          columnFrob
            (matMulRect m n n (mgsRoundedPolarCorrection Qhat hnm) Rhat) j :=
      mgsRoundedGlobalRepairDelta_columnFrob_le A Qhat Rhat hnm j
    _ <= vecNorm2 (mgsRoundedProductEntryBudget fp Qhat V j) +
        mgsRoundedPolarSensitivityBudget Qhat * columnFrob Rhat j :=
      add_le_add
        (hstate.product_residual_column_bound hdiag j)
        (mgsRoundedPolarCorrection_product_column_bound Qhat Rhat hnm j)
    _ <= vecNorm2 (mgsRoundedProductEntryBudget fp Qhat V j) +
        (gramCoeff * fp.u) * columnFrob Rhat j :=
      add_le_add le_rfl
        (mul_le_mul_of_nonneg_right hgram (columnFrob_nonneg Rhat j))
    _ = mgsRoundedLocalGramRepairColumnBudget
        fp Qhat Rhat V gramCoeff j := rfl

theorem mgsRoundedLocalGramRepairColumnBudget_nonneg {m n : Nat}
    (fp : FPModel) (Qhat : Fin m -> Fin n -> Real)
    (Rhat : Fin n -> Fin n -> Real)
    (V : Nat -> Fin n -> Fin m -> Real)
    {gramCoeff : Real} (hgramCoeff : 0 <= gramCoeff) (j : Fin n) :
    0 <= mgsRoundedLocalGramRepairColumnBudget
      fp Qhat Rhat V gramCoeff j := by
  exact add_nonneg (vecNorm2_nonneg _)
    (mul_nonneg (mul_nonneg hgramCoeff fp.u_nonneg)
      (columnFrob_nonneg Rhat j))

theorem mgsRoundedLocalGramRepairRelativeBudget_nonneg {m n : Nat}
    (fp : FPModel) (A Qhat : Fin m -> Fin n -> Real)
    (Rhat : Fin n -> Fin n -> Real)
    (V : Nat -> Fin n -> Fin m -> Real)
    {gramCoeff : Real} (hgramCoeff : 0 <= gramCoeff) :
    0 <= mgsRoundedLocalGramRepairRelativeBudget
      fp A Qhat Rhat V gramCoeff := by
  apply Finset.sum_nonneg
  intro j _hj
  exact div_nonneg
    (mgsRoundedLocalGramRepairColumnBudget_nonneg
      fp Qhat Rhat V hgramCoeff j)
    (columnFrob_nonneg A j)

/-- Each repaired column satisfies the source-relative coefficient assembled
from explicit local accumulation and Gram-defect budgets. -/
theorem ModifiedGramSchmidtRoundedState.globalRepairDelta_columnwise_localGram
    {m n : Nat} {fp : FPModel}
    {A Qhat : Fin m -> Fin n -> Real}
    {Rhat : Fin n -> Fin n -> Real}
    {V : Nat -> Fin n -> Fin m -> Real}
    (hstate : ModifiedGramSchmidtRoundedState fp A Qhat Rhat V)
    (hdiag : forall k : Fin n, Ne (Rhat k k) 0)
    (hnm : n <= m) {gramCoeff : Real}
    (hgramCoeff : 0 <= gramCoeff)
    (hgram : mgsRoundedPolarSensitivityBudget Qhat <= gramCoeff * fp.u)
    (hsource : forall j : Fin n, 0 < columnFrob A j) :
    forall j,
      columnFrob (mgsRoundedGlobalRepairDelta A Qhat Rhat hnm) j <=
        mgsRoundedLocalGramRepairRelativeBudget
            fp A Qhat Rhat V gramCoeff * columnFrob A j := by
  intro j
  let c := mgsRoundedLocalGramRepairColumnBudget
    fp Qhat Rhat V gramCoeff j
  have hc : 0 <= c :=
    mgsRoundedLocalGramRepairColumnBudget_nonneg
      fp Qhat Rhat V hgramCoeff j
  have hratio :
      c / columnFrob A j <=
        mgsRoundedLocalGramRepairRelativeBudget
          fp A Qhat Rhat V gramCoeff := by
    exact Finset.single_le_sum
      (fun k _hk => div_nonneg
        (mgsRoundedLocalGramRepairColumnBudget_nonneg
          fp Qhat Rhat V hgramCoeff k)
        (columnFrob_nonneg A k))
      (Finset.mem_univ j)
  have hmul := mul_le_mul_of_nonneg_right hratio (le_of_lt (hsource j))
  have hc_eq : (c / columnFrob A j) * columnFrob A j = c := by
    field_simp [ne_of_gt (hsource j)]
  calc
    columnFrob (mgsRoundedGlobalRepairDelta A Qhat Rhat hnm) j <= c :=
      hstate.globalRepairDelta_columnFrob_le_localGram
        hdiag hnm gramCoeff hgram j
    _ = (c / columnFrob A j) * columnFrob A j := hc_eq.symm
    _ <= mgsRoundedLocalGramRepairRelativeBudget
          fp A Qhat Rhat V gramCoeff * columnFrob A j := hmul

/-- Quantitative, non-circular polar-repair bridge for a rounded MGS state.
The Gram premise is a bound on the computed matrix `Qhat^T Qhat - I`, not a
restatement of the desired repair residual. -/
theorem ModifiedGramSchmidtRoundedState.toGlobalRepairWithLocalGramBudget
    {m n : Nat} {fp : FPModel}
    {A Qhat : Fin m -> Fin n -> Real}
    {Rhat : Fin n -> Fin n -> Real}
    {V : Nat -> Fin n -> Fin m -> Real}
    (hstate : ModifiedGramSchmidtRoundedState fp A Qhat Rhat V)
    (hdiag : forall k : Fin n, Ne (Rhat k k) 0)
    (hnm : n <= m) {gramCoeff : Real}
    (hgramCoeff : 0 <= gramCoeff)
    (hgram : mgsRoundedPolarSensitivityBudget Qhat <= gramCoeff * fp.u)
    (hsource : forall j : Fin n, 0 < columnFrob A j) :
    ModifiedGramSchmidtGlobalRepair m n A Rhat
      (mgsRoundedLocalGramRepairRelativeBudget
        fp A Qhat Rhat V gramCoeff) := by
  let Qrepair := mgsRoundedPolarRepairQ Qhat hnm
  let dA := mgsRoundedGlobalRepairDelta A Qhat Rhat hnm
  refine { repair := ?_ }
  refine Exists.intro Qrepair ?_
  refine Exists.intro dA ?_
  refine And.intro (mgsRoundedPolarRepairQ_orthonormal Qhat hnm) ?_
  refine And.intro ?_ ?_
  · intro i j
    have hlin := congrFun
      (congrFun
        (matMulRect_sub_left_square_right
          (mgsRoundedPolarRepairQ Qhat hnm) Qhat Rhat) i) j
    change
      A i j +
          (matMulRect m n n Qhat Rhat i j - A i j +
            matMulRect m n n
              (fun a b => mgsRoundedPolarRepairQ Qhat hnm a b - Qhat a b)
              Rhat i j) =
        matMulRect m n n (mgsRoundedPolarRepairQ Qhat hnm) Rhat i j
    rw [hlin]
    ring
  · exact hstate.globalRepairDelta_columnwise_localGram
      hdiag hnm hgramCoeff hgram hsource

/-- Implementation-facing producer for the literal `FPModel` MGS loop.  Its
remaining numerical premise is precisely an explicit bound on the computed
Gram defect; the repair budget itself is expanded into local trace data,
`gramCoeff * u`, the computed `Rhat`, and source column norms. -/
theorem fl_modifiedGramSchmidt_globalRepairWithLocalGramBudget {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (hnm : n <= m)
    (hm : gammaValid fp (2 * (m + 1)))
    (hpivot : forall k : Fin n,
      Ne (fl_modifiedGramSchmidtR fp A k k) 0)
    {gramCoeff : Real} (hgramCoeff : 0 <= gramCoeff)
    (hgram : mgsRoundedPolarSensitivityBudget
        (fl_modifiedGramSchmidtQ fp A) <= gramCoeff * fp.u)
    (hsource : forall j : Fin n, 0 < columnFrob A j) :
    ModifiedGramSchmidtGlobalRepair m n A
      (fl_modifiedGramSchmidtR fp A)
      (mgsRoundedLocalGramRepairRelativeBudget fp A
        (fl_modifiedGramSchmidtQ fp A)
        (fl_modifiedGramSchmidtR fp A)
        (flMGSVectors fp A) gramCoeff) := by
  exact
    (fl_modifiedGramSchmidt_roundedState fp A hm hpivot).toGlobalRepairWithLocalGramBudget
      hpivot hnm hgramCoeff hgram hsource

end

end NumStability
