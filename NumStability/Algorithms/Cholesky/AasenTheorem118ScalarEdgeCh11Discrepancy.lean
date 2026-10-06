/-
Algorithms/Cholesky/AasenTheorem118ScalarEdgeCh11Discrepancy.lean

Higham, 2nd ed., Theorem 11.8 (Chapter 11, printed p. 224) prints no lower
bound on the order `n`, but its
normwise radius contains `(n - 1)^2`.  At `n = 1` that radius is zero, while
the only solve operation is a rounded scalar division.  This file records the
resulting source discrepancy for the actual scalar Aasen factors and proves
the sharp faithful correction at the failing order.
-/
import NumStability.Algorithms.Cholesky.AasenDirect118Ch11Closure

open scoped BigOperators

namespace NumStability.Ch11Closure.AasenScalarEdge

open NumStability
open NumStability.Ch11Closure.AasenDirect

/-- A legal standard-model arithmetic in which only division takes the
maximal positive relative error. -/
noncomputable def divBiasedModel (u : Real) (hu : 0 <= u) : FPModel where
  u := u
  u_nonneg := hu
  fl_add := fun x y => x + y
  fl_sub := fun x y => x - y
  fl_mul := fun x y => x * y
  fl_div := fun x y => (x / y) * (1 + u)
  fl_sqrt := fun x => Real.sqrt x
  fl_add_zero := by
    intro x
    ring
  model_add := by
    intro x y
    refine ⟨0, by simpa using hu, ?_⟩
    ring
  model_sub := by
    intro x y
    refine ⟨0, by simpa using hu, ?_⟩
    ring
  model_mul := by
    intro x y
    refine ⟨0, by simpa using hu, ?_⟩
    ring
  model_div := by
    intro x y _hy
    exact ⟨u, by simp [abs_of_nonneg hu], rfl⟩
  model_sqrt := by
    intro x _hx
    refine ⟨0, by simpa using hu, ?_⟩
    ring

/-- The scalar coefficient and right-hand side used by the edge example. -/
def scalarT : Fin 1 -> Fin 1 -> Real := fun _ _ => 1
def scalarB : Fin 1 -> Real := fun _ => 1

/-- The actual scalar solve is the repository's executable back-substitution
kernel at order one.  Unfolding the kernel leaves exactly one rounded
division by the scalar coefficient. -/
noncomputable def scalarComputedX (u : Real) (hu : 0 <= u) : Fin 1 -> Real :=
  fl_backSub (divBiasedModel u hu) 1 scalarT scalarB

@[simp] theorem scalarComputedX_apply (u : Real) (hu : 0 <= u) (i : Fin 1) :
    scalarComputedX u hu i = 1 + u := by
  fin_cases i
  simp [scalarComputedX, fl_backSub, fl_backSub_steps, scalarT, scalarB,
    divBiasedModel]

/-- At order one the repository's actual coupled Aasen executor produces the
identity lower factor and the scalar input as its tridiagonal factor.  Thus the
counterexample below is an Aasen execution, not an unrelated scalar system. -/
theorem scalar_flAasen_factors (u : Real) (hu : 0 <= u) :
    (flAasen (divBiasedModel u hu) 1 scalarT).Lhat = scalarT /\
    (flAasen (divBiasedModel u hu) 1 scalarT).That = scalarT := by
  constructor <;>
    funext i j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [flAasen, flAasenIter, flAasenStep, flAasenInit,
      aTdiag, aHdiag, aHsub, aUpperH, aHcol, aLcol,
      scalarT, divBiasedModel, fl_dotProduct, Fin.foldl_succ]

/-- **Theorem 11.8 source edge.**  At order one, all printed gamma-validity
requirements may hold, but the printed `(n-1)^2` norm radius is zero and
cannot contain the backward error of the actual rounded scalar solve. -/
theorem higham11_8_printed_norm_clause_false_at_n_one
    (u : Real) (hu : 0 < u) (hsmall : 40 * u < 1) :
    let fp := divBiasedModel u hu.le
    gammaValid fp 40 /\
      ¬ (Exists fun DeltaT : Fin 1 -> Fin 1 -> Real =>
        (forall i : Fin 1,
          (∑ j : Fin 1,
            (scalarT i j + DeltaT i j) * scalarComputedX u hu.le j) = scalarB i) /\
        infNorm DeltaT <=
          (((1 - 1 : Nat) : Real) ^ 2) * gamma fp 40 * infNorm scalarT) := by
  dsimp only
  constructor
  . simpa [gammaValid, divBiasedModel] using hsmall
  . rintro ⟨DeltaT, hsource, hnorm⟩
    have hnorm0 : infNorm DeltaT <= 0 := by
      simpa using hnorm
    have hrow : |DeltaT 0 0| <= infNorm DeltaT := by
      simpa [Fin.sum_univ_one] using row_sum_le_infNorm DeltaT (0 : Fin 1)
    have habs : |DeltaT 0 0| = 0 := by
      apply le_antisymm
      . exact hrow.trans hnorm0
      . exact abs_nonneg _
    have hdelta : DeltaT 0 0 = 0 := abs_eq_zero.mp habs
    have heq := hsource (0 : Fin 1)
    simp [scalarT, scalarB, scalarComputedX_apply, hdelta] at heq
    nlinarith

/-- The complete theorem-level source-discrepancy certificate: actual coupled
Aasen at `n = 1` produces `Lhat = I` and `That = A = [1]`, all printed gamma
validity holds, yet no perturbation satisfying the printed zero radius can make
the actual rounded scalar solve exact. -/
theorem higham11_8_printed_norm_clause_false_for_actual_n_one_aasen
    (u : Real) (hu : 0 < u) (hsmall : 40 * u < 1) :
    let fp := divBiasedModel u hu.le
    (flAasen fp 1 scalarT).Lhat = scalarT /\
      (flAasen fp 1 scalarT).That = scalarT /\
      gammaValid fp 40 /\
      ¬ (Exists fun DeltaT : Fin 1 -> Fin 1 -> Real =>
        (forall i : Fin 1,
          (∑ j : Fin 1,
            (scalarT i j + DeltaT i j) * scalarComputedX u hu.le j) = scalarB i) /\
        infNorm DeltaT <=
          (((1 - 1 : Nat) : Real) ^ 2) * gamma fp 40 * infNorm scalarT) := by
  dsimp only
  obtain ⟨hL, hT⟩ := scalar_flAasen_factors u hu.le
  obtain ⟨hvalid, hfalse⟩ :=
    higham11_8_printed_norm_clause_false_at_n_one u hu hsmall
  exact ⟨hL, hT, hvalid, hfalse⟩

/-- The exact scalar perturbation forced by the rounded division. -/
noncomputable def scalarDeltaT (u : Real) : Fin 1 -> Fin 1 -> Real :=
  fun _ _ => -u / (1 + u)

/-- The strongest faithful order-one correction: the actual scalar solve is
the exact solution of `(T + DeltaT)x = b` for
`DeltaT = -u/(1+u)`, whose infinity norm is exactly `u/(1+u)` and is bounded
by `gamma_1 ||T||_infinity` when `0 < u < 1`. -/
theorem higham11_8_n_one_sharp_corrected_bound
    (u : Real) (hu : 0 < u) (hu1 : u < 1) :
    let fp := divBiasedModel u hu.le
    (forall i : Fin 1,
      (∑ j : Fin 1,
        (scalarT i j + scalarDeltaT u i j) * scalarComputedX u hu.le j) =
          scalarB i) /\
    infNorm (scalarDeltaT u) = u / (1 + u) /\
    infNorm (scalarDeltaT u) <= gamma fp 1 * infNorm scalarT := by
  dsimp only
  have h1u : 0 < 1 + u := by linarith
  have h1mu : 0 < 1 - u := by linarith
  constructor
  . intro i
    fin_cases i
    simp [scalarT, scalarB, scalarDeltaT,
      scalarComputedX_apply]
    field_simp
    ring
  . have hentry : |(-u / (1 + u) : Real)| = u / (1 + u) := by
      rw [abs_div, abs_neg, abs_of_pos hu, abs_of_pos h1u]
    have hnormUpper : infNorm (scalarDeltaT u) <= u / (1 + u) := by
      apply infNorm_le_of_row_sum_le
      . intro i
        fin_cases i
        simp [scalarDeltaT, hentry]
      . exact div_nonneg hu.le h1u.le
    have hnormLower : u / (1 + u) <= infNorm (scalarDeltaT u) := by
      have hrow := row_sum_le_infNorm (scalarDeltaT u) (0 : Fin 1)
      simpa [Fin.sum_univ_one, scalarDeltaT, hentry] using hrow
    have hnormEq : infNorm (scalarDeltaT u) = u / (1 + u) :=
      le_antisymm hnormUpper hnormLower
    refine ⟨hnormEq, ?_⟩
    have hTnorm : infNorm scalarT = 1 := by
      apply le_antisymm
      . apply infNorm_le_of_row_sum_le
        . intro i
          fin_cases i
          norm_num [Fin.sum_univ_one, scalarT]
        . norm_num
      . have hrow := row_sum_le_infNorm scalarT (0 : Fin 1)
        norm_num [Fin.sum_univ_one, scalarT] at hrow
        exact hrow
    rw [hnormEq, hTnorm, mul_one]
    simp only [gamma, divBiasedModel]
    norm_num only [Nat.cast_one, one_mul]
    change u / (1 + u) <= u / (1 - u)
    apply (div_le_div_iff₀ h1u h1mu).2
    nlinarith

end NumStability.Ch11Closure.AasenScalarEdge
