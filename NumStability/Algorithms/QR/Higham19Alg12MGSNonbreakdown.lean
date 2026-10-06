import NumStability.Algorithms.QR.Higham19Alg12MGSSourceRate

/-!
# Higham Theorem 19.13: operational nonbreakdown boundary

The printed theorem assumes only that the source matrix has full column rank.
For the repository's abstract relative-error `FPModel`, that assumption does
not force the literal rounded MGS executor to reach every pivot.  This module
records the honest success-or-breakdown endpoint and a concrete full-rank
two-by-two execution whose second computed pivot is zero.
-/

namespace NumStability

open scoped BigOperators

noncomputable section

/-- The source-facing outcome available without assuming operational MGS
nonbreakdown.  On a successful execution it contains the full canonical
Theorem 19.13 certificate; otherwise it identifies an actual zero pivot. -/
inductive LiteralMGSTheorem1913CanonicalOutcome
    (m n : Nat) (fp : FPModel) (A : Fin m -> Fin n -> Real) : Prop
  | success :
      LiteralMGSTheorem1913SourceRateCertificate m n fp A
        (lsAplusOfGramNonsingInv A)
        (mgsSourceProductGlobalCoeff m n)
        (mgsSourceRepairCoeff m n) ->
      LiteralMGSTheorem1913CanonicalOutcome m n fp A
  | breakdown (k : Fin n) :
      fl_modifiedGramSchmidtR fp A k k = 0 ->
      LiteralMGSTheorem1913CanonicalOutcome m n fp A

/-- Corrected rank-only surface for the literal rounded MGS algorithm.  The
source smallness assumptions imply the printed bounds whenever the actual
executor succeeds; without an operational nonbreakdown theorem, the other
possible outcome is an exhibited zero computed pivot. -/
theorem higham19_13_literal_mgs_source_rate_canonical_success_or_breakdown
    {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (hnm : n <= m)
    (hfull : Function.Injective (rectMatMulVec A))
    (hm : gammaValid fp (2 * (m + 1)))
    (hmodelSmall :
      (((2 * (m + 1) : Nat) : Real) * fp.u <= 1 / 2))
    (hconditionSmall :
      Real.sqrt (n : Real) * mgsSourceRepairCoeff m n * fp.u *
          mgsSourceKappa2 A < 1) :
    LiteralMGSTheorem1913CanonicalOutcome m n fp A := by
  classical
  by_cases hpivot : forall k : Fin n,
      fl_modifiedGramSchmidtR fp A k k ≠ 0
  · exact LiteralMGSTheorem1913CanonicalOutcome.success
      (higham19_13_literal_mgs_source_rate_canonical_closed
        fp A hnm hfull hm hpivot hmodelSmall hconditionSmall)
  · push_neg at hpivot
    obtain ⟨k, hk⟩ := hpivot
    exact LiteralMGSTheorem1913CanonicalOutcome.breakdown k hk

/-! ## A full-rank literal-MGS breakdown execution -/

/-- A standard-model instance with `u = 1/16`.  Addition, subtraction,
multiplication, and square root are exact.  Division is exact except at the
two first-column numerators used below; both exceptional relative errors are
strictly within `u`. -/
noncomputable def higham19MGSBreakdownFP : FPModel where
  u := 1 / 16
  u_nonneg := by norm_num
  fl_add := fun x y => x + y
  fl_sub := fun x y => x - y
  fl_mul := fun x y => x * y
  fl_div := fun x y =>
    if x = 3 then (x / y) * (1 + 82 / 1623)
    else if x = 4 then (x / y) * (1 - 16 / 541)
    else x / y
  fl_sqrt := fun x => Real.sqrt x
  fl_add_zero := by intro x; ring
  model_add := by
    intro x y
    refine ⟨0, by norm_num, ?_⟩
    ring
  model_sub := by
    intro x y
    refine ⟨0, by norm_num, ?_⟩
    ring
  model_mul := by
    intro x y
    refine ⟨0, by norm_num, ?_⟩
    ring
  model_div := by
    intro x y _hy
    by_cases hx3 : x = 3
    · refine ⟨82 / 1623, by norm_num, ?_⟩
      subst x
      norm_num
    · by_cases hx4 : x = 4
      · refine ⟨-(16 / 541), by norm_num, ?_⟩
        subst x
        norm_num
      · refine ⟨0, by norm_num, ?_⟩
        simp [hx3, hx4]
  model_sqrt := by
    intro x _hx
    refine ⟨0, by norm_num, ?_⟩
    ring

/-- The counterexample columns are `(3,4)^T` and
`(341/541,420/541)^T`. -/
def higham19MGSBreakdownA : Fin 2 -> Fin 2 -> Real :=
  fun i j =>
    if i = 0 then
      if j = 0 then 3 else 341 / 541
    else
      if j = 0 then 4 else 420 / 541

theorem higham19MGSBreakdownA_injective :
    Function.Injective (rectMatMulVec higham19MGSBreakdownA) := by
  intro x y hxy
  have h0 := congrFun hxy (0 : Fin 2)
  have h1 := congrFun hxy (1 : Fin 2)
  simp [rectMatMulVec, Fin.sum_univ_two, higham19MGSBreakdownA] at h0 h1
  have hx1 : x (1 : Fin 2) = y (1 : Fin 2) := by
    linear_combination (541 / 104 : Real) * (4 * h0 - 3 * h1)
  have hx0 : x (0 : Fin 2) = y (0 : Fin 2) := by
    linarith [h0, hx1]
  funext j
  fin_cases j
  · simpa using hx0
  · simpa using hx1

theorem higham19MGSBreakdown_first_norm :
    flMGSColumnNorm higham19MGSBreakdownFP
      (flMGSVectors higham19MGSBreakdownFP higham19MGSBreakdownA 0)
      (0 : Fin 2) = 5 := by
  norm_num [flMGSColumnNorm, flMGSVectors, gsColumn, fl_norm2, fl_norm2Sq,
    fl_dotProduct, Fin.foldl_succ,
    higham19MGSBreakdownFP, higham19MGSBreakdownA]
  rw [show (25 : Real) = (5 : Real) ^ 2 by norm_num,
    Real.sqrt_sq_eq_abs]
  norm_num

/-- The two admissible division roundings make the first computed normalized
column equal exactly to the second source column. -/
theorem higham19MGSBreakdown_first_q_eq_second_source_column :
    flMGSNormalizedColumn higham19MGSBreakdownFP
      (flMGSVectors higham19MGSBreakdownFP higham19MGSBreakdownA 0)
      (0 : Fin 2) =
        gsColumn higham19MGSBreakdownA (1 : Fin 2) := by
  funext i
  unfold flMGSNormalizedColumn
  rw [higham19MGSBreakdown_first_norm]
  fin_cases i <;>
    norm_num [flMGSVectors, gsColumn, higham19MGSBreakdownFP,
      higham19MGSBreakdownA]

theorem higham19MGSBreakdown_first_projection_eq_one :
    flMGSProjection higham19MGSBreakdownFP
      (flMGSVectors higham19MGSBreakdownFP higham19MGSBreakdownA 0)
      (0 : Fin 2) (1 : Fin 2) = 1 := by
  rw [flMGSProjection,
    higham19MGSBreakdown_first_q_eq_second_source_column]
  norm_num [flMGSVectors, gsColumn, fl_dotProduct, Fin.foldl_succ,
    higham19MGSBreakdownFP, higham19MGSBreakdownA]
  rfl

theorem higham19MGSBreakdown_second_stage_column_eq_zero :
    flMGSVectors higham19MGSBreakdownFP higham19MGSBreakdownA 1
      (1 : Fin 2) = 0 := by
  change flMGSVectors higham19MGSBreakdownFP higham19MGSBreakdownA
    ((0 : Fin 2).val + 1) (1 : Fin 2) = 0
  rw [flMGSVectors_succ_later higham19MGSBreakdownFP
    higham19MGSBreakdownA (show (0 : Fin 2) < (1 : Fin 2) by decide)]
  simp only [Fin.val_zero]
  rw [higham19MGSBreakdown_first_projection_eq_one,
    higham19MGSBreakdown_first_q_eq_second_source_column]
  funext i
  fin_cases i <;>
    norm_num [flMGSVectors, gsColumn, higham19MGSBreakdownFP,
      higham19MGSBreakdownA] <;> rfl

theorem higham19MGSBreakdown_second_pivot_eq_zero :
    fl_modifiedGramSchmidtR higham19MGSBreakdownFP
      higham19MGSBreakdownA (1 : Fin 2) (1 : Fin 2) = 0 := by
  rw [fl_modifiedGramSchmidtR_diag]
  change fl_norm2 higham19MGSBreakdownFP 2
    (flMGSVectors higham19MGSBreakdownFP higham19MGSBreakdownA 1
      (1 : Fin 2)) = 0
  rw [higham19MGSBreakdown_second_stage_column_eq_zero]
  norm_num [fl_norm2, fl_norm2Sq, fl_dotProduct, Fin.foldl_succ,
    higham19MGSBreakdownFP]

theorem higham19MGSBreakdown_gammaValid :
    gammaValid higham19MGSBreakdownFP (2 * (2 + 1)) := by
  norm_num [gammaValid, higham19MGSBreakdownFP]

theorem higham19MGSBreakdown_modelSmall :
    (((2 * (2 + 1) : Nat) : Real) * higham19MGSBreakdownFP.u <= 1 / 2) := by
  norm_num [higham19MGSBreakdownFP]

/-- Full column rank plus the routine gamma/model smallness conditions do not
imply operational nonbreakdown of literal MGS for the abstract `FPModel`.
Consequently `hpivot` cannot simply be erased from the existing successful
Theorem 19.13 endpoint. -/
theorem higham19_theorem19_13_rank_only_does_not_force_nonbreakdown :
    exists (fp : FPModel) (A : Fin 2 -> Fin 2 -> Real),
      Function.Injective (rectMatMulVec A) /\
      gammaValid fp (2 * (2 + 1)) /\
      (((2 * (2 + 1) : Nat) : Real) * fp.u <= 1 / 2) /\
      exists k : Fin 2, fl_modifiedGramSchmidtR fp A k k = 0 := by
  exact ⟨higham19MGSBreakdownFP, higham19MGSBreakdownA,
    higham19MGSBreakdownA_injective, higham19MGSBreakdown_gammaValid,
    higham19MGSBreakdown_modelSmall, (1 : Fin 2),
    higham19MGSBreakdown_second_pivot_eq_zero⟩

end

end NumStability
