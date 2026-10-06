/-
Chapter 11 rook-pivoting executor adapter.

This file deliberately closes only the structural part of the bridge from the
literal recursive mixed-pivot executor to `Higham11RookSourceClosure`.  The
named executor `Mixed.flMixedD` is block diagonal by construction; the partner
map below is computed from the same `PivotSchedule`, so its support certificate
does not need to be assumed.

This is not a full Algorithm 11.5 closure.  In particular, the existing
`higham11_5_RookMultiplierOrigin` constructors describe exact algebraic
multipliers, whereas `Mixed.flMixedL` contains rounded multiplications,
additions, and divisions.  Also, the mixed executor currently proves the
printed `|A| + |L||D||L^T|` residual envelope, not the product-only
`BlockLDLTBackwardError` consumed by the final transfer theorem.
-/

import NumStability.Algorithms.Cholesky.Higham11RookSourceClosure
import NumStability.Algorithms.Cholesky.BlockLDLTMixedPivotCh11Closure

namespace NumStability

namespace Higham11RookExecutorAdapter

open Ch11Closure.Mixed

/-- Partner index computed from the literal mixed-pivot schedule.  A scalar
pivot is its own partner; the two indices of a `2 x 2` pivot are partners; and
the recursive trailing partner map is shifted by the pivot width. -/
def mixedSchedulePartner : {n : Nat} -> PivotSchedule n -> Fin n -> Fin n
  | 0, .nil, i => Fin.elim0 i
  | _ + 1, .consOne s, i =>
      Fin.cases 0 (fun j => (mixedSchedulePartner s j).succ) i
  | _ + 2, .consTwo s, i =>
      Fin.cases (Fin.succ 0)
        (fun i' => Fin.cases 0
          (fun j => (mixedSchedulePartner s j).succ.succ) i') i

@[simp] theorem mixedSchedulePartner_consOne_zero {n : Nat}
    (s : PivotSchedule n) :
    mixedSchedulePartner s.consOne 0 = 0 := rfl

@[simp] theorem mixedSchedulePartner_consOne_succ {n : Nat}
    (s : PivotSchedule n) (i : Fin n) :
    mixedSchedulePartner s.consOne i.succ = (mixedSchedulePartner s i).succ := rfl

@[simp] theorem mixedSchedulePartner_consTwo_zero {n : Nat}
    (s : PivotSchedule n) :
    mixedSchedulePartner s.consTwo 0 = Fin.succ 0 := rfl

@[simp] theorem mixedSchedulePartner_consTwo_one {n : Nat}
    (s : PivotSchedule n) :
    mixedSchedulePartner s.consTwo (Fin.succ 0) = 0 := rfl

@[simp] theorem mixedSchedulePartner_consTwo_succ_succ {n : Nat}
    (s : PivotSchedule n) (i : Fin n) :
    mixedSchedulePartner s.consTwo i.succ.succ =
      (mixedSchedulePartner s i).succ.succ := rfl

/-- The block support hypothesis in the public rook product theorem is derived
for the actual named `D` emitted by the mixed-pivot executor. -/
theorem flMixedD_rookBlockDiagonalSupport (fp : FPModel) :
    forall {n : Nat} (s : PivotSchedule n)
      (A : Fin n -> Fin n -> Real),
      higham11_5_RookBlockDiagonalSupport
        (flMixedD fp s A) (mixedSchedulePartner s) := by
  intro n s
  induction s with
  | nil =>
      intro A i
      exact Fin.elim0 i
  | @consOne n s ih =>
      intro A i j hji hjpartner
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
      · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
        · exact False.elim (hji rfl)
        · simp
      · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
        · simp
        · simp only [flMixedD_consOne_ss]
          apply ih (flSchurCompl n fp A) i' j'
          · intro h
            apply hji
            exact congrArg Fin.succ h
          · intro h
            apply hjpartner
            simpa using congrArg Fin.succ h
  | @consTwo n s ih =>
      intro A i j hji hjpartner
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
      · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
        · exact False.elim (hji rfl)
        · rcases Fin.eq_zero_or_eq_succ j' with rfl | ⟨j'', rfl⟩
          · exact False.elim (hjpartner rfl)
          · simp
      · rcases Fin.eq_zero_or_eq_succ i' with rfl | ⟨i'', rfl⟩
        · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
          · exact False.elim (hjpartner rfl)
          · rcases Fin.eq_zero_or_eq_succ j' with rfl | ⟨j'', rfl⟩
            · exact False.elim (hji rfl)
            · exact flMixedD_consTwo_1t fp s A j''
        · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
          · simp
          · rcases Fin.eq_zero_or_eq_succ j' with rfl | ⟨j'', rfl⟩
            · exact flMixedD_consTwo_t1 fp s A i''
            · simp only [flMixedD_consTwo_tt]
              apply ih (flSchurCompl2 n fp A) i'' j''
              · intro h
                apply hji
                exact congrArg Fin.succ (congrArg Fin.succ h)
              · intro h
                apply hjpartner
                simpa using congrArg Fin.succ (congrArg Fin.succ h)

/-- Product-bound adapter for the named mixed executor.  This removes the
formerly free `D`-support hypothesis and leaves exactly the two genuinely open
numeric bridges: a rounded-multiplier bound/origin replacement and pivot-growth
control tied to the recursively updated active matrices. -/
theorem higham11_5_rook_theorem11_4_product_bound_of_mixedExecutor
    {n : Nat} (hn : 0 < n) (fp : FPModel) (s : PivotSchedule n)
    (A : Fin n -> Fin n -> Real) (rho Amax : Real)
    (hrho : 0 <= rho) (hAmax : 0 <= Amax)
    (horigin : forall i j,
      higham11_5_RookMultiplierOrigin higham11_1_bunchParlettAlpha
        (flMixedL fp s A i j))
    (hDgrowth : forall k1 k2 : Fin n,
      |flMixedD fp s A k1 k2| <= rho * Amax) :
    higham11_4_bunchKaufmanMaxEntryProductBound n
      (higham11_4_bunchKaufmanProductMax n hn
        (flMixedL fp s A) (flMixedD fp s A)) rho Amax := by
  exact higham11_5_rook_theorem11_4_product_bound hn
    (flMixedL fp s A) (flMixedD fp s A) (mixedSchedulePartner s)
    rho Amax hrho hAmax horigin
    (flMixedD_rookBlockDiagonalSupport fp s A) hDgrowth

end Higham11RookExecutorAdapter

end NumStability
