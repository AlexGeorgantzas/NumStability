-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
-- Chapter 21, corrected MGS formation on printed page 413.

import NumStability.Algorithms.RankOneUpdate
import NumStability.Algorithms.Underdetermined.Higham21MGS
import NumStability.Algorithms.Underdetermined.Higham21RowwiseMeasure

namespace NumStability

open scoped BigOperators

noncomputable section

/-! ## A rounded corrected-MGS step -/

/-- Rounded corrected MGS update in the printed operation order:
rounded dot product, rounded subtraction of `y_k`, rounded multiplication by
`q_k`, and rounded componentwise subtraction from `x`. -/
noncomputable def higham21FlMGSCorrectedStep (fp : FPModel) {m n : Nat}
    (Q : Fin n -> Fin m -> Real) (y : Fin m -> Real) (k : Fin m)
    (x : Fin n -> Real) : Fin n -> Real :=
  let q := gsColumn Q k
  let t := fl_dotProduct fp n q x
  let s := fp.fl_sub t (y k)
  fun i => fp.fl_sub (x i) (fp.fl_mul s (q i))

/-- The exact corrected step is a rank-one update followed by `y_k q_k`. -/
theorem higham21_mgs_corrected_step_eq_rankOneUpdate_add {m n : Nat}
    (Q : Fin n -> Fin m -> Real) (y : Fin m -> Real) (k : Fin m)
    (x : Fin n -> Real) :
    higham21MGSCorrectedStep Q y k x =
      fun i =>
        rankOneUpdateExact n (gsColumn Q k) (gsColumn Q k) x i +
          y k * gsColumn Q k i := by
  funext i
  unfold higham21MGSCorrectedStep rankOneUpdateExact gsDot gsColumn
  ring

/-- Error budget for subtracting `y` from an approximation `t` to `d`. -/
noncomputable def higham21FlSubAfterApproxBudget
    (fp : FPModel) (E T : Real) : Real :=
  E + T * fp.u

/-- Reusable certificate for rounded subtraction after an approximate input. -/
theorem higham21_fl_sub_after_approx_error_bound
    (fp : FPModel) (t d y E T : Real)
    (hT : 0 <= T) (htd : |t - d| <= E) (hty : |t - y| <= T) :
    |fp.fl_sub t y - (d - y)| <=
      higham21FlSubAfterApproxBudget fp E T := by
  obtain ⟨delta, hdelta, hsub⟩ := fp.model_sub t y
  have hrewrite :
      fp.fl_sub t y - (d - y) = (t - d) + (t - y) * delta := by
    rw [hsub]
    ring
  rw [hrewrite]
  calc
    |(t - d) + (t - y) * delta| <=
        |t - d| + |(t - y) * delta| := abs_add_le _ _
    _ = |t - d| + |t - y| * |delta| := by rw [abs_mul]
    _ <= E + T * fp.u :=
      add_le_add htd (mul_le_mul hty hdelta (abs_nonneg delta) hT)
    _ = higham21FlSubAfterApproxBudget fp E T := rfl

/-- Error budget for multiplying an approximate scalar `shat` by `q`. -/
noncomputable def higham21FlMulAfterApproxBudget
    (fp : FPModel) (q E S : Real) : Real :=
  |q| * E * (1 + fp.u) + |q| * S * fp.u

/-- Reusable certificate for rounded multiplication after an approximate
scalar input. -/
theorem higham21_fl_mul_after_approx_error_bound
    (fp : FPModel) (shat s q E S : Real)
    (hE : 0 <= E) (hS : 0 <= S)
    (hshat : |shat - s| <= E) (hs : |s| <= S) :
    |fp.fl_mul shat q - s * q| <=
      higham21FlMulAfterApproxBudget fp q E S := by
  obtain ⟨delta, hdelta, hmul⟩ := fp.model_mul shat q
  have hone : |1 + delta| <= 1 + fp.u := by
    calc
      |1 + delta| <= |(1 : Real)| + |delta| := abs_add_le _ _
      _ <= 1 + fp.u := by simpa using add_le_add_left hdelta 1
  have hrewrite :
      fp.fl_mul shat q - s * q =
        q * (shat - s) * (1 + delta) + s * q * delta := by
    rw [hmul]
    ring
  rw [hrewrite]
  calc
    |q * (shat - s) * (1 + delta) + s * q * delta| <=
        |q * (shat - s) * (1 + delta)| + |s * q * delta| :=
      abs_add_le _ _
    _ = |q| * |shat - s| * |1 + delta| + |s| * |q| * |delta| := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul]
    _ <= |q| * E * (1 + fp.u) + S * |q| * fp.u := by
      exact add_le_add
        (mul_le_mul
          (mul_le_mul_of_nonneg_left hshat (abs_nonneg q)) hone
          (abs_nonneg (1 + delta))
          (mul_nonneg (abs_nonneg q) hE))
        (mul_le_mul
          (mul_le_mul_of_nonneg_right hs (abs_nonneg q)) hdelta
          (abs_nonneg delta)
          (mul_nonneg hS (abs_nonneg q)))
    _ = higham21FlMulAfterApproxBudget fp q E S := by
      unfold higham21FlMulAfterApproxBudget
      ring

/-- Error budget for the final rounded subtraction `fl(x-what)`. -/
noncomputable def higham21FlFinalSubBudget
    (fp : FPModel) (x W E : Real) : Real :=
  E + (|x| + W + E) * fp.u

/-- Reusable certificate for the final subtraction with an approximate
subtrahend. -/
theorem higham21_fl_final_sub_error_bound
    (fp : FPModel) (x what w W E : Real)
    (hW : 0 <= W) (hE : 0 <= E)
    (hwhat : |what - w| <= E) (hw : |w| <= W) :
    |fp.fl_sub x what - (x - w)| <=
      higham21FlFinalSubBudget fp x W E := by
  obtain ⟨delta, hdelta, hsub⟩ := fp.model_sub x what
  have hwhatAbs : |what| <= W + E := by
    calc
      |what| = |w + (what - w)| := by ring_nf
      _ <= |w| + |what - w| := abs_add_le _ _
      _ <= W + E := add_le_add hw hwhat
  have hdiffAbs : |x - what| <= |x| + W + E := by
    calc
      |x - what| <= |x| + |what| := abs_sub _ _
      _ <= |x| + (W + E) := add_le_add_right hwhatAbs _
      _ = |x| + W + E := by ring
  have hdiffNonneg : 0 <= |x| + W + E :=
    add_nonneg (add_nonneg (abs_nonneg x) hW) hE
  have hrewrite :
      fp.fl_sub x what - (x - w) =
        -(what - w) + (x - what) * delta := by
    rw [hsub]
    ring
  rw [hrewrite]
  calc
    |-(what - w) + (x - what) * delta| <=
        |-(what - w)| + |(x - what) * delta| :=
      abs_add_le _ _
    _ = |what - w| + |x - what| * |delta| := by
      rw [abs_mul, abs_neg]
    _ <= E + (|x| + W + E) * fp.u :=
      add_le_add hwhat
        (mul_le_mul hdiffAbs hdelta (abs_nonneg delta) hdiffNonneg)
    _ = higham21FlFinalSubBudget fp x W E := rfl

/-- Per-component local budget for the printed rounded corrected-MGS step. -/
noncomputable def higham21FlMGSCorrectedLocalBudget
    (fp : FPModel) {m n : Nat}
    (Q : Fin n -> Fin m -> Real) (y : Fin m -> Real) (k : Fin m)
    (x : Fin n -> Real) : Fin n -> Real :=
  let q := gsColumn Q k
  let S := Finset.univ.sum fun j : Fin n => |q j| * |x j|
  let Edot := gamma fp n * S
  let T := S + Edot + |y k|
  let Es := higham21FlSubAfterApproxBudget fp Edot T
  let Sscalar := S + |y k|
  fun i =>
    let Ew := higham21FlMulAfterApproxBudget fp (q i) Es Sscalar
    let W := |q i| * Sscalar
    higham21FlFinalSubBudget fp (x i) W Ew

/-- The concrete printed-order rounded step satisfies its local componentwise
budget. -/
theorem higham21_fl_mgs_corrected_step_componentwise_error_bound
    (fp : FPModel) {m n : Nat}
    (Q : Fin n -> Fin m -> Real) (y : Fin m -> Real) (k : Fin m)
    (x : Fin n -> Real) (hvalid : gammaValid fp (n + 3)) :
    forall i : Fin n,
      |higham21FlMGSCorrectedStep fp Q y k x i -
          higham21MGSCorrectedStep Q y k x i| <=
        higham21FlMGSCorrectedLocalBudget fp Q y k x i := by
  intro i
  let q : Fin n -> Real := gsColumn Q k
  let d : Real := gsDot q x
  let t : Real := fl_dotProduct fp n q x
  let S : Real := Finset.univ.sum fun j : Fin n => |q j| * |x j|
  let Edot : Real := gamma fp n * S
  let T : Real := S + Edot + |y k|
  let s : Real := d - y k
  let shat : Real := fp.fl_sub t (y k)
  let Es : Real := higham21FlSubAfterApproxBudget fp Edot T
  let Sscalar : Real := S + |y k|
  let Ew : Real := higham21FlMulAfterApproxBudget fp (q i) Es Sscalar
  let W : Real := |q i| * Sscalar
  have hn : gammaValid fp n := gammaValid_mono fp (by omega) hvalid
  have hgamma : 0 <= gamma fp n := gamma_nonneg fp hn
  have hS : 0 <= S :=
    Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hEdot : 0 <= Edot := mul_nonneg hgamma hS
  have hdotError : |t - d| <= Edot := by
    simpa [q, d, t, S, Edot, gsDot] using
      dotProduct_error_bound fp n q x hn
  have hdotAbs : |d| <= S := by
    calc
      |d| = |Finset.univ.sum fun j : Fin n => q j * x j| := by
        rfl
      _ <= Finset.univ.sum fun j : Fin n => |q j * x j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = S := by simp [S, abs_mul]
  have htAbs : |t| <= S + Edot := by
    calc
      |t| = |d + (t - d)| := by ring_nf
      _ <= |d| + |t - d| := abs_add_le _ _
      _ <= S + Edot := add_le_add hdotAbs hdotError
  have hT : 0 <= T :=
    add_nonneg (add_nonneg hS hEdot) (abs_nonneg (y k))
  have hty : |t - y k| <= T := by
    calc
      |t - y k| <= |t| + |y k| := abs_sub _ _
      _ <= (S + Edot) + |y k| := add_le_add_left htAbs _
      _ = T := rfl
  have hsError : |shat - s| <= Es := by
    simpa [shat, s, Es] using
      higham21_fl_sub_after_approx_error_bound
        fp t d (y k) Edot T hT hdotError hty
  have hSscalar : 0 <= Sscalar := add_nonneg hS (abs_nonneg (y k))
  have hsAbs : |s| <= Sscalar := by
    calc
      |s| = |d - y k| := rfl
      _ <= |d| + |y k| := abs_sub _ _
      _ <= S + |y k| := add_le_add_left hdotAbs _
      _ = Sscalar := rfl
  have hEs : 0 <= Es := by
    simp only [Es, higham21FlSubAfterApproxBudget]
    exact add_nonneg hEdot (mul_nonneg hT fp.u_nonneg)
  have hmulError :
      |fp.fl_mul shat (q i) - s * q i| <= Ew := by
    simpa [Ew] using higham21_fl_mul_after_approx_error_bound
      fp shat s (q i) Es Sscalar hEs hSscalar hsError hsAbs
  have hW : 0 <= W := mul_nonneg (abs_nonneg (q i)) hSscalar
  have hw : |s * q i| <= W := by
    simpa [W, abs_mul, mul_comm] using
      mul_le_mul_of_nonneg_right hsAbs (abs_nonneg (q i))
  have hEw : 0 <= Ew := by
    simp only [Ew, higham21FlMulAfterApproxBudget]
    exact add_nonneg
      (mul_nonneg (mul_nonneg (abs_nonneg (q i)) hEs)
        (add_nonneg zero_le_one fp.u_nonneg))
      (mul_nonneg (mul_nonneg (abs_nonneg (q i)) hSscalar) fp.u_nonneg)
  have hfinal := higham21_fl_final_sub_error_bound
    fp (x i) (fp.fl_mul shat (q i)) (s * q i) W Ew
      hW hEw hmulError hw
  simpa [higham21FlMGSCorrectedStep, higham21MGSCorrectedStep,
    higham21FlMGSCorrectedLocalBudget, q, d, t, S, Edot, T, s, shat,
    Es, Sscalar, Ew, W] using hfinal

/-! ## The backward loop and its repaired-action majorant -/

/-- At distance `d+1` from the terminal state, the next column is
`m-(d+1)`. -/
def higham21MGSBackwardIndex {m : Nat} (d : Nat) (hd : d + 1 <= m) : Fin m :=
  ⟨m - (d + 1), by omega⟩

/-- State after `d` rounded steps, starting from zero and visiting columns
`m-1,m-2,...`. -/
noncomputable def higham21FlMGSCorrectedStateAtDistance
    (fp : FPModel) {m n : Nat}
    (Q : Fin n -> Fin m -> Real) (y : Fin m -> Real) :
    (d : Nat) -> d <= m -> Fin n -> Real
  | 0, _ => 0
  | d + 1, hd =>
      higham21FlMGSCorrectedStep fp Q y
        (higham21MGSBackwardIndex d hd)
        (higham21FlMGSCorrectedStateAtDistance fp Q y d (by omega))

/-- Terminal equation of the concrete rounded backward recurrence. -/
theorem higham21_fl_mgs_corrected_state_terminal
    (fp : FPModel) {m n : Nat}
    (Q : Fin n -> Fin m -> Real) (y : Fin m -> Real)
    (h0 : 0 <= m) :
    higham21FlMGSCorrectedStateAtDistance fp Q y 0 h0 =
      (0 : Fin n -> Real) := by
  rfl

/-- Successor equation: distance `d+1` applies column `m-(d+1)` to the
state after `d` later-column updates. -/
theorem higham21_fl_mgs_corrected_state_succ
    (fp : FPModel) {m n : Nat}
    (Q : Fin n -> Fin m -> Real) (y : Fin m -> Real)
    (d : Nat) (hd : d + 1 <= m) :
    higham21FlMGSCorrectedStateAtDistance fp Q y (d + 1) hd =
      higham21FlMGSCorrectedStep fp Q y
        (higham21MGSBackwardIndex d hd)
        (higham21FlMGSCorrectedStateAtDistance fp Q y d (by omega)) := by
  rfl

/-- Actual output of the rounded corrected-MGS backward recurrence. -/
noncomputable def higham21FlMGSCorrectedOutput
    (fp : FPModel) {m n : Nat}
    (Q : Fin n -> Fin m -> Real) (y : Fin m -> Real) : Fin n -> Real :=
  higham21FlMGSCorrectedStateAtDistance fp Q y m le_rfl

/-- Absolute majorant for applying `I-q*q^T` to a vector already bounded by
`B`. -/
noncomputable def higham21MGSRankOneMajorant {n : Nat}
    (q B : Fin n -> Real) : Fin n -> Real :=
  fun i => B i + |q i| * (Finset.univ.sum fun j : Fin n => |q j| * B j)

/-- A rank-one update transports a componentwise majorant as expected. -/
theorem higham21_rankOneUpdateExact_abs_le_majorant {n : Nat}
    (q e B : Fin n -> Real)
    (he : forall j, |e j| <= B j) :
    forall i,
      |rankOneUpdateExact n q q e i| <=
        higham21MGSRankOneMajorant q B i := by
  intro i
  have hsum :
      |Finset.univ.sum fun j : Fin n => q j * e j| <=
        Finset.univ.sum fun j : Fin n => |q j| * B j := by
    calc
      |Finset.univ.sum fun j : Fin n => q j * e j| <=
          Finset.univ.sum fun j : Fin n => |q j * e j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= Finset.univ.sum fun j : Fin n => |q j| * B j := by
        exact Finset.sum_le_sum fun j _ => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (he j) (abs_nonneg (q j))
  calc
    |rankOneUpdateExact n q q e i| <=
        |e i| + |q i| *
          |Finset.univ.sum fun j : Fin n => q j * e j| := by
      unfold rankOneUpdateExact
      calc
        |e i - q i * (Finset.univ.sum fun j : Fin n => q j * e j)| <=
            |e i| + |q i * (Finset.univ.sum fun j : Fin n => q j * e j)| :=
          abs_sub _ _
        _ = |e i| + |q i| *
            |Finset.univ.sum fun j : Fin n => q j * e j| := by
          rw [abs_mul]
    _ <= B i + |q i| *
        (Finset.univ.sum fun j : Fin n => |q j| * B j) :=
      add_le_add (he i) (mul_le_mul_of_nonneg_left hsum (abs_nonneg (q i)))
    _ = higham21MGSRankOneMajorant q B i := rfl

/-- The affine corrected step has rank-one linear part. -/
theorem higham21_mgs_corrected_step_sub {m n : Nat}
    (Q : Fin n -> Fin m -> Real) (y : Fin m -> Real) (k : Fin m)
    (x t : Fin n -> Real) :
    (fun i =>
      higham21MGSCorrectedStep Q y k x i -
        higham21MGSCorrectedStep Q y k t i) =
      rankOneUpdateExact n (gsColumn Q k) (gsColumn Q k)
        (fun j => x j - t j) := by
  funext i
  have hsum :
      (Finset.univ.sum fun j : Fin n =>
          gsColumn Q k j * (x j - t j)) =
        (Finset.univ.sum fun j : Fin n => gsColumn Q k j * x j) -
          (Finset.univ.sum fun j : Fin n => gsColumn Q k j * t j) := by
    rw [<- Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold higham21MGSCorrectedStep rankOneUpdateExact gsDot
  rw [hsum]
  unfold gsColumn
  ring_nf

/-- Propagated componentwise budget against a fixed reference vector.  The
middle term measures the exact corrected-step defect of that reference; for a
Chapter 19 repair the reference is `Qrepair*y`. -/
noncomputable def higham21FlMGSComparisonBudgetAtDistance
    (fp : FPModel) {m n : Nat}
    (Q : Fin n -> Fin m -> Real) (y : Fin m -> Real)
    (target : Fin n -> Real) :
    (d : Nat) -> d <= m -> Fin n -> Real
  | 0, _ => fun i => |target i|
  | d + 1, hd =>
      let hd' : d <= m := by omega
      let k := higham21MGSBackwardIndex d hd
      let x := higham21FlMGSCorrectedStateAtDistance fp Q y d hd'
      let B := higham21FlMGSComparisonBudgetAtDistance fp Q y target d hd'
      fun i =>
        higham21MGSRankOneMajorant (gsColumn Q k) B i +
          |higham21MGSCorrectedStep Q y k target i - target i| +
          higham21FlMGSCorrectedLocalBudget fp Q y k x i

/-- The propagated budget bounds every intermediate rounded state. -/
theorem higham21_fl_mgs_state_componentwise_reference_error
    (fp : FPModel) {m n : Nat}
    (Q : Fin n -> Fin m -> Real) (y : Fin m -> Real)
    (target : Fin n -> Real) (hvalid : gammaValid fp (n + 3)) :
    forall (d : Nat) (hd : d <= m) (i : Fin n),
      |higham21FlMGSCorrectedStateAtDistance fp Q y d hd i - target i| <=
        higham21FlMGSComparisonBudgetAtDistance fp Q y target d hd i := by
  intro d
  induction d with
  | zero =>
      intro hd i
      simp [higham21FlMGSCorrectedStateAtDistance,
        higham21FlMGSComparisonBudgetAtDistance]
  | succ d ih =>
      intro hd i
      let hd' : d <= m := by omega
      let k : Fin m := higham21MGSBackwardIndex d hd
      let x := higham21FlMGSCorrectedStateAtDistance fp Q y d hd'
      let B := higham21FlMGSComparisonBudgetAtDistance fp Q y target d hd'
      have hprev : forall j : Fin n, |x j - target j| <= B j := by
        intro j
        simpa [x, B] using ih hd' j
      have hmiddle :
          |higham21MGSCorrectedStep Q y k x i -
              higham21MGSCorrectedStep Q y k target i| <=
            higham21MGSRankOneMajorant (gsColumn Q k) B i := by
        rw [congrFun (higham21_mgs_corrected_step_sub Q y k x target) i]
        exact higham21_rankOneUpdateExact_abs_le_majorant
          (gsColumn Q k) (fun j => x j - target j) B hprev i
      have hlocal :=
        higham21_fl_mgs_corrected_step_componentwise_error_bound
          fp Q y k x hvalid i
      have hsplit :
          higham21FlMGSCorrectedStep fp Q y k x i - target i =
            (higham21FlMGSCorrectedStep fp Q y k x i -
              higham21MGSCorrectedStep Q y k x i) +
            (higham21MGSCorrectedStep Q y k x i -
              higham21MGSCorrectedStep Q y k target i) +
            (higham21MGSCorrectedStep Q y k target i - target i) := by
        ring
      change
        |higham21FlMGSCorrectedStep fp Q y k x i - target i| <= _
      rw [hsplit]
      calc
        |(higham21FlMGSCorrectedStep fp Q y k x i -
              higham21MGSCorrectedStep Q y k x i) +
            (higham21MGSCorrectedStep Q y k x i -
              higham21MGSCorrectedStep Q y k target i) +
            (higham21MGSCorrectedStep Q y k target i - target i)| <=
            |higham21FlMGSCorrectedStep fp Q y k x i -
                higham21MGSCorrectedStep Q y k x i| +
              |higham21MGSCorrectedStep Q y k x i -
                higham21MGSCorrectedStep Q y k target i| +
              |higham21MGSCorrectedStep Q y k target i - target i| := by
          exact le_trans (abs_add_le _ _)
            (add_le_add (abs_add_le _ _) le_rfl)
        _ <= higham21FlMGSCorrectedLocalBudget fp Q y k x i +
              higham21MGSRankOneMajorant (gsColumn Q k) B i +
              |higham21MGSCorrectedStep Q y k target i - target i| :=
          add_le_add (add_le_add hlocal hmiddle) le_rfl
        _ = higham21MGSRankOneMajorant (gsColumn Q k) B i +
              |higham21MGSCorrectedStep Q y k target i - target i| +
              higham21FlMGSCorrectedLocalBudget fp Q y k x i := by ring
        _ = higham21FlMGSComparisonBudgetAtDistance
              fp Q y target (d + 1) hd i := by
          simp [higham21FlMGSComparisonBudgetAtDistance, k, x, B]

/-- Final propagated budget against the repaired action. -/
noncomputable def higham21FlMGSRepairedActionBudget
    (fp : FPModel) {m n : Nat}
    (Qhat Qrepair : Fin n -> Fin m -> Real) (y : Fin m -> Real) :
    Fin n -> Real :=
  higham21FlMGSComparisonBudgetAtDistance fp Qhat y
    (higham21MGSNaiveFormation Qrepair y) m le_rfl

/-- Componentwise relation between the actual rounded recurrence and the
selected orthonormal Chapter 19 repair action. -/
theorem higham21_fl_mgs_corrected_output_repaired_action_componentwise
    (fp : FPModel) {m n : Nat}
    (Qhat Qrepair : Fin n -> Fin m -> Real) (y : Fin m -> Real)
    (hvalid : gammaValid fp (n + 3)) :
    forall i : Fin n,
      |higham21FlMGSCorrectedOutput fp Qhat y i -
          higham21MGSNaiveFormation Qrepair y i| <=
        higham21FlMGSRepairedActionBudget fp Qhat Qrepair y i := by
  intro i
  exact higham21_fl_mgs_state_componentwise_reference_error
    fp Qhat y (higham21MGSNaiveFormation Qrepair y) hvalid m le_rfl i

/-! ## A rowwise action certificate for a fixed triangular-solve vector -/

/-- Least-Frobenius rank-one correction whose action on `y` is `e`. -/
noncomputable def higham21MGSFixedVectorActionCorrection {m n : Nat}
    (y : Fin m -> Real) (e : Fin n -> Real) : Fin n -> Fin m -> Real :=
  fun i j => (1 / vecNorm2Sq y) * (e i * y j)

private theorem higham21_vecNorm2_ne_zero_of_fun_ne_zero {m : Nat}
    {y : Fin m -> Real} (hy : y ≠ 0) : vecNorm2 y ≠ 0 := by
  intro hnorm
  exact hy (funext ((vecNorm2_eq_zero_iff y).mp hnorm))

private theorem higham21_vecNorm2Sq_ne_zero_of_fun_ne_zero {m : Nat}
    {y : Fin m -> Real} (hy : y ≠ 0) : vecNorm2Sq y ≠ 0 := by
  intro hsq
  apply higham21_vecNorm2_ne_zero_of_fun_ne_zero hy
  unfold vecNorm2
  simp [hsq]

/-- The fixed-vector rank-one correction has exactly the requested action. -/
theorem higham21_mgs_fixedVectorActionCorrection_action {m n : Nat}
    (y : Fin m -> Real) (e : Fin n -> Real) (hy : y ≠ 0) :
    rectMatMulVec (higham21MGSFixedVectorActionCorrection y e) y = e := by
  have hsq := higham21_vecNorm2Sq_ne_zero_of_fun_ne_zero hy
  ext i
  unfold rectMatMulVec higham21MGSFixedVectorActionCorrection
  calc
    (Finset.univ.sum fun j : Fin m =>
        (1 / vecNorm2Sq y) * (e i * y j) * y j) =
        (1 / vecNorm2Sq y) * e i *
          (Finset.univ.sum fun j : Fin m => y j ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (1 / vecNorm2Sq y) * e i * vecNorm2Sq y := rfl
    _ = e i := by field_simp [hsq]

/-- Exact row norm of the fixed-vector rank-one action correction. -/
theorem higham21_mgs_fixedVectorActionCorrection_rowNorm {m n : Nat}
    (y : Fin m -> Real) (e : Fin n -> Real) (hy : y ≠ 0)
    (i : Fin n) :
    rectRowNorm2 (higham21MGSFixedVectorActionCorrection y e) i =
      |e i| / vecNorm2 y := by
  have hynorm := higham21_vecNorm2_ne_zero_of_fun_ne_zero hy
  have hsqNonneg : 0 <= vecNorm2Sq y := vecNorm2Sq_nonneg y
  have hsq : vecNorm2Sq y = vecNorm2 y ^ 2 := (vecNorm2_sq y).symm
  change
    vecNorm2 (fun j : Fin m => (1 / vecNorm2Sq y) * (e i * y j)) =
      |e i| / vecNorm2 y
  have hfun :
      (fun j : Fin m => (1 / vecNorm2Sq y) * (e i * y j)) =
        fun j => ((1 / vecNorm2Sq y) * e i) * y j := by
    funext j
    ring
  rw [hfun, vecNorm2_smul, abs_mul,
    abs_of_nonneg (one_div_nonneg.mpr hsqNonneg), hsq]
  field_simp [hynorm]

/-- Componentwise forward error becomes a rowwise perturbation of the action
matrix for the fixed nonzero vector `y`. -/
theorem higham21_fl_mgs_corrected_output_repaired_action_rowwise
    (fp : FPModel) {m n : Nat}
    (Qhat Qrepair : Fin n -> Fin m -> Real) (y : Fin m -> Real)
    (hvalid : gammaValid fp (n + 3)) (hy : y ≠ 0) :
    exists DeltaQ : Fin n -> Fin m -> Real,
      higham21FlMGSCorrectedOutput fp Qhat y =
        rectMatMulVec (fun i j => Qrepair i j + DeltaQ i j) y /\
      (forall i,
        rectRowNorm2 DeltaQ i <=
          higham21FlMGSRepairedActionBudget fp Qhat Qrepair y i /
            vecNorm2 y) := by
  let e : Fin n -> Real := fun i =>
    higham21FlMGSCorrectedOutput fp Qhat y i -
      higham21MGSNaiveFormation Qrepair y i
  let DeltaQ := higham21MGSFixedVectorActionCorrection y e
  have he : forall i,
      |e i| <= higham21FlMGSRepairedActionBudget fp Qhat Qrepair y i := by
    intro i
    exact higham21_fl_mgs_corrected_output_repaired_action_componentwise
      fp Qhat Qrepair y hvalid i
  have hyPos : 0 < vecNorm2 y :=
    lt_of_le_of_ne (vecNorm2_nonneg y)
      (Ne.symm (higham21_vecNorm2_ne_zero_of_fun_ne_zero hy))
  refine ⟨DeltaQ, ?_, ?_⟩
  . have hDelta := higham21_mgs_fixedVectorActionCorrection_action y e hy
    ext i
    have haction := congrFun
      (rectMatMulVec_mat_add Qrepair DeltaQ y) i
    rw [hDelta] at haction
    have heq :
        rectMatMulVec (fun r c => Qrepair r c + DeltaQ r c) y i =
          higham21MGSNaiveFormation Qrepair y i + e i := by
      simpa [higham21MGSNaiveFormation] using haction
    rw [heq]
    simp [e]
  . intro i
    rw [higham21_mgs_fixedVectorActionCorrection_rowNorm y e hy i]
    exact (div_le_div_iff_of_pos_right hyPos).2 (he i)

/-! ## Explicit rank-one system corrections -/

/-- Rowwise rank-one correction that makes `x` feasible for `B*x=b` when
`x` is nonzero. -/
noncomputable def higham21MGSFeasibilityCorrection {m n : Nat}
    (B : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (x : Fin n -> Real) : Fin m -> Fin n -> Real :=
  higham21MGSFixedVectorActionCorrection x
    (fun i => b i - rectMatMulVec B x i)

/-- The feasibility correction makes the corrected system solve exactly. -/
theorem higham21_mgs_feasibilityCorrection_solves {m n : Nat}
    (B : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (x : Fin n -> Real) (hx : x ≠ 0) :
    rectMatMulVec
      (fun i j => B i j + higham21MGSFeasibilityCorrection B b x i j) x =
        b := by
  let e : Fin m -> Real := fun i => b i - rectMatMulVec B x i
  have hcorr := higham21_mgs_fixedVectorActionCorrection_action x e hx
  calc
    rectMatMulVec
        (fun i j => B i j + higham21MGSFeasibilityCorrection B b x i j) x =
        fun i => rectMatMulVec B x i +
          rectMatMulVec (higham21MGSFeasibilityCorrection B b x) x i :=
      rectMatMulVec_mat_add B (higham21MGSFeasibilityCorrection B b x) x
    _ = fun i => rectMatMulVec B x i + e i := by
      rw [show higham21MGSFeasibilityCorrection B b x =
          higham21MGSFixedVectorActionCorrection x e by
        rfl, hcorr]
    _ = b := by
      funext i
      simp [e]

/-- Exact row norm of the feasibility correction. -/
theorem higham21_mgs_feasibilityCorrection_rowNorm {m n : Nat}
    (B : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (x : Fin n -> Real) (hx : x ≠ 0) (i : Fin m) :
    rectRowNorm2 (higham21MGSFeasibilityCorrection B b x) i =
      |b i - rectMatMulVec B x i| / vecNorm2 x := by
  simpa [higham21MGSFeasibilityCorrection] using
    higham21_mgs_fixedVectorActionCorrection_rowNorm x
      (fun r => b r - rectMatMulVec B x r) hx i

/-- Transposed rank-one correction that puts `x` in the transpose range of
`B` through a fixed nonzero dual vector `z`. -/
noncomputable def higham21MGSRangeCorrection {m n : Nat}
    (B : Fin m -> Fin n -> Real) (x : Fin n -> Real)
    (z : Fin m -> Real) : Fin m -> Fin n -> Real :=
  finiteTranspose
    (higham21MGSFixedVectorActionCorrection z
      (fun j => x j - rectTransposeMulVec B z j))

/-- The transpose action of the range correction is the exact range
residual. -/
theorem higham21_mgs_rangeCorrection_action {m n : Nat}
    (B : Fin m -> Fin n -> Real) (x : Fin n -> Real)
    (z : Fin m -> Real) (hz : z ≠ 0) :
    rectTransposeMulVec (higham21MGSRangeCorrection B x z) z =
      fun j => x j - rectTransposeMulVec B z j := by
  let e : Fin n -> Real := fun j => x j - rectTransposeMulVec B z j
  have hcorr := higham21_mgs_fixedVectorActionCorrection_action z e hz
  ext j
  have hj := congrFun hcorr j
  simpa [higham21MGSRangeCorrection, e, rectTransposeMulVec,
    rectMatMulVec, finiteTranspose] using hj

/-- Adding the range correction makes the transpose representation exact. -/
theorem higham21_mgs_rangeCorrection_represents {m n : Nat}
    (B : Fin m -> Fin n -> Real) (x : Fin n -> Real)
    (z : Fin m -> Real) (hz : z ≠ 0) :
    rectTransposeMulVec
      (fun i j => B i j + higham21MGSRangeCorrection B x z i j) z = x := by
  have hcorr := higham21_mgs_rangeCorrection_action B x z hz
  ext j
  have hj := congrFun hcorr j
  unfold rectTransposeMulVec
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  change rectTransposeMulVec B z j +
      rectTransposeMulVec (higham21MGSRangeCorrection B x z) z j = x j
  rw [hj]
  ring

/-- Exact row norm of the explicit transpose-range correction. -/
theorem higham21_mgs_rangeCorrection_rowNorm {m n : Nat}
    (B : Fin m -> Fin n -> Real) (x : Fin n -> Real)
    (z : Fin m -> Real) (i : Fin m) :
    rectRowNorm2 (higham21MGSRangeCorrection B x z) i =
      |(1 / vecNorm2Sq z) * z i| *
        vecNorm2 (fun j => x j - rectTransposeMulVec B z j) := by
  let e : Fin n -> Real := fun j => x j - rectTransposeMulVec B z j
  change vecNorm2 (fun j : Fin n =>
      higham21MGSRangeCorrection B x z i j) =
    |(1 / vecNorm2Sq z) * z i| * vecNorm2 e
  have hfun :
      (fun j : Fin n => higham21MGSRangeCorrection B x z i j) =
        fun j => ((1 / vecNorm2Sq z) * z i) * e j := by
    funext j
    simp [higham21MGSRangeCorrection,
      higham21MGSFixedVectorActionCorrection, finiteTranspose, e]
    ring
  rw [hfun, vecNorm2_smul]

/-! ## The Problem 19.12 repair and the triangular-solve perturbation -/

/-- The pure Problem 19.12 correction map gives the exact action split
`Qrepair*y = P21*y + F*(P11*y)`. -/
theorem higham21_mgs_problem1912_repaired_action_eq {m n : Nat}
    (P11 : Fin n -> Fin n -> Real)
    (P21 Qrepair F : Fin m -> Fin n -> Real)
    (hrepair : MGSProblem1912CorrectionMapData m n P11 P21 Qrepair F)
    (y : Fin n -> Real) :
    higham21MGSNaiveFormation Qrepair y =
      fun i => higham21MGSNaiveFormation P21 y i +
        rectMatMulVec F (rectMatMulVec P11 y) i := by
  rw [hrepair.add_factor_eq]
  unfold higham21MGSNaiveFormation
  calc
    rectMatMulVec
        (fun i j => P21 i j + matMulRect m n n F P11 i j) y =
        fun i => rectMatMulVec P21 y i +
          rectMatMulVec (matMulRect m n n F P11) y i :=
      rectMatMulVec_mat_add P21 (matMulRect m n n F P11) y
    _ = fun i => rectMatMulVec P21 y i +
        rectMatMulVec F (rectMatMulVec P11 y) i := by
      rw [matMulRect_eq_rectMatMul, rectMatMulVec_rectMatMul]

/-- Fold the computed triangular-solve perturbation into the repaired economy
factor perturbation. -/
noncomputable def higham21MGSFoldedDeltaAT {m n : Nat}
    (Qrepair : Fin n -> Fin m -> Real)
    (DeltaAT : Fin n -> Fin m -> Real)
    (DeltaR : Fin m -> Fin m -> Real) : Fin n -> Fin m -> Real :=
  fun i j => DeltaAT i j + matMulRect n m m Qrepair DeltaR i j

/-- Exact economy-factor identity after folding `DeltaR` into `Rhat`. -/
theorem higham21_mgs_folded_deltaAT_factor {m n : Nat}
    (AT DeltaAT : Fin n -> Fin m -> Real)
    (Qrepair : Fin n -> Fin m -> Real)
    (Rhat DeltaR : Fin m -> Fin m -> Real)
    (hfactor : forall i j,
      AT i j + DeltaAT i j = matMulRect n m m Qrepair Rhat i j) :
    forall i j,
      AT i j + higham21MGSFoldedDeltaAT Qrepair DeltaAT DeltaR i j =
        matMulRect n m m Qrepair
          (fun a b => Rhat a b + DeltaR a b) i j := by
  intro i j
  have hadd := congrFun (congrFun
    (matMulRect_add_right n m m Qrepair Rhat DeltaR) i) j
  unfold higham21MGSFoldedDeltaAT
  calc
    AT i j +
        (DeltaAT i j + matMulRect n m m Qrepair DeltaR i j) =
        (AT i j + DeltaAT i j) +
          matMulRect n m m Qrepair DeltaR i j := by ring
    _ = matMulRect n m m Qrepair Rhat i j +
          matMulRect n m m Qrepair DeltaR i j := by rw [hfactor i j]
    _ = matMulRect n m m Qrepair
          (fun a b => Rhat a b + DeltaR a b) i j := hadd.symm

/-- Economy matrices with orthonormal columns preserve Euclidean norm. -/
theorem higham21_mgs_orthonormal_columns_action_norm_eq {m n : Nat}
    (Q : Fin n -> Fin m -> Real) (hQ : GramSchmidtOrthonormalColumns Q)
    (x : Fin m -> Real) :
    vecNorm2 (rectMatMulVec Q x) = vecNorm2 x := by
  have hforward := hQ.rectOpNorm2Le_one x
  have hQT : rectOpNorm2Le (finiteTranspose Q) 1 :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le Q (by norm_num)
      hQ.rectOpNorm2Le_one
  have hback := hQT (rectMatMulVec Q x)
  have hid := higham21_mgs_naive_transpose_action_of_orthonormal Q x hQ
  unfold higham21MGSNaiveFormation at hid
  rw [hid] at hback
  apply le_antisymm
  . simpa using hforward
  . simpa using hback

/-- Column form of the economy isometry. -/
theorem higham21_mgs_orthonormal_columns_matMulRect_columnFrob {m n : Nat}
    (Q : Fin n -> Fin m -> Real) (R : Fin m -> Fin m -> Real)
    (hQ : GramSchmidtOrthonormalColumns Q) (j : Fin m) :
    columnFrob (matMulRect n m m Q R) j = columnFrob R j := by
  rw [columnFrob_eq_vecNorm2, columnFrob_eq_vecNorm2]
  change
    vecNorm2 (rectMatMulVec Q (fun i : Fin m => R i j)) =
      vecNorm2 (fun i : Fin m => R i j)
  exact higham21_mgs_orthonormal_columns_action_norm_eq
    Q hQ (fun i : Fin m => R i j)

set_option maxHeartbeats 800000 in
/-- Economy analogue of the Theorem 21.4 lifted-`DeltaR` estimate. -/
theorem higham21_mgs_folded_deltaAT_column_bound {m n : Nat}
    (AT DeltaAT : Fin n -> Fin m -> Real)
    (Qrepair : Fin n -> Fin m -> Real)
    (Rhat DeltaR : Fin m -> Fin m -> Real)
    {etaQR etaR : Real}
    (hQ : GramSchmidtOrthonormalColumns Qrepair)
    (hfactor : forall i j,
      AT i j + DeltaAT i j = matMulRect n m m Qrepair Rhat i j)
    (_hetaQR : 0 <= etaQR)
    (hDeltaAT : forall j,
      columnFrob DeltaAT j <= etaQR * columnFrob AT j)
    (hetaR : 0 <= etaR)
    (hDeltaR : forall i j, |DeltaR i j| <= etaR * |Rhat i j|) :
    forall j,
      columnFrob (higham21MGSFoldedDeltaAT Qrepair DeltaAT DeltaR) j <=
        (etaQR + etaR * (1 + etaQR)) * columnFrob AT j := by
  intro j
  have hmat :
      matMulRect n m m Qrepair Rhat =
        fun i j => AT i j + DeltaAT i j := by
    ext i r
    exact (hfactor i r).symm
  have hRhat :
      columnFrob Rhat j <= (1 + etaQR) * columnFrob AT j := by
    calc
      columnFrob Rhat j =
          columnFrob (matMulRect n m m Qrepair Rhat) j :=
        (higham21_mgs_orthonormal_columns_matMulRect_columnFrob
          Qrepair Rhat hQ j).symm
      _ = columnFrob (fun i r => AT i r + DeltaAT i r) j := by rw [hmat]
      _ <= columnFrob AT j + columnFrob DeltaAT j :=
        columnFrob_add_le AT DeltaAT j
      _ <= columnFrob AT j + etaQR * columnFrob AT j :=
        add_le_add_right (hDeltaAT j) _
      _ = (1 + etaQR) * columnFrob AT j := by ring
  have hDeltaRCol :
      columnFrob DeltaR j <= etaR * columnFrob Rhat j :=
    higham21_columnFrob_le_of_entrywise_relative_bound
      Rhat DeltaR hetaR hDeltaR j
  have hQDeltaR :
      columnFrob (matMulRect n m m Qrepair DeltaR) j <=
        columnFrob DeltaR j := by
    have h := columnFrob_matMulRect_le_rectOpNorm2_mul_columnFrob
      Qrepair DeltaR hQ.rectOpNorm2Le_one j
    simpa using h
  calc
    columnFrob (higham21MGSFoldedDeltaAT Qrepair DeltaAT DeltaR) j <=
        columnFrob DeltaAT j +
          columnFrob (matMulRect n m m Qrepair DeltaR) j :=
      columnFrob_add_le DeltaAT (matMulRect n m m Qrepair DeltaR) j
    _ <= etaQR * columnFrob AT j + columnFrob DeltaR j :=
      add_le_add (hDeltaAT j) hQDeltaR
    _ <= etaQR * columnFrob AT j + etaR * columnFrob Rhat j :=
      add_le_add_right hDeltaRCol _
    _ <= etaQR * columnFrob AT j +
        etaR * ((1 + etaQR) * columnFrob AT j) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hRhat hetaR) _
    _ = (etaQR + etaR * (1 + etaQR)) * columnFrob AT j := by ring

/-- A selected witness from the Chapter 19 MGS `r_factor` channel. -/
structure Higham21MGSSelectedRepair {m n : Nat}
    (A : Fin m -> Fin n -> Real) (Rhat : Fin m -> Fin m -> Real)
    (Qrepair DeltaAT : Fin n -> Fin m -> Real) (etaQR : Real) : Prop where
  upper : IsUpperTrapezoidal m m Rhat
  orthonormal : GramSchmidtOrthonormalColumns Qrepair
  factor : forall i j,
    finiteTranspose A i j + DeltaAT i j =
      matMulRect n m m Qrepair Rhat i j
  column_bound : forall j,
    columnFrob DeltaAT j <= etaQR * columnFrob (finiteTranspose A) j
  eta_nonneg : 0 <= etaQR

/-- Chapter 19's MGS theorem supplies a selected repair witness. -/
theorem higham21_mgs_selected_repair_exists_of_mgs
    {m n : Nat} {A : Fin m -> Fin n -> Real}
    {Qhat : Fin n -> Fin m -> Real} {Rhat : Fin m -> Fin m -> Real}
    {c1 c2 c3 u normA kappaA higherOrder : Real}
    (hMGS : ModifiedGramSchmidtBackwardError n m
      (finiteTranspose A) Qhat Rhat
      c1 c2 c3 u normA kappaA higherOrder)
    (heta : 0 <= c3 * u) :
    exists Qrepair : Fin n -> Fin m -> Real,
      exists DeltaAT : Fin n -> Fin m -> Real,
        Higham21MGSSelectedRepair A Rhat Qrepair DeltaAT (c3 * u) := by
  rcases hMGS.r_factor with
    ⟨Qrepair, DeltaAT, hQ, hfactor, hcolumn⟩
  exact ⟨Qrepair, DeltaAT,
    { upper := hMGS.upper
      orthonormal := hQ
      factor := hfactor
      column_bound := hcolumn
      eta_nonneg := heta }⟩

/-! ## Actual-output Theorem 21.4 handoff -/

/-- The remaining action-to-system transfer needed by Lemma 21.2.

The concrete output is fixed in this structure.  `DeltaA1` makes that output
solve a nearby system, while `DeltaA2` puts it in the transpose range of a
nearby system.  The rounded recurrence and its repaired-action row certificate
above do not, by themselves, imply these two row-scaled matrix bounds. -/
structure Higham21MGSRoundedSystemTransfer
    (fp : FPModel) {m n : Nat}
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (Qhat : Fin n -> Fin m -> Real) (y : Fin m -> Real)
    (DeltaBase : Fin m -> Fin n -> Real) (etaAction : Real) : Type where
  DeltaA1 : Fin m -> Fin n -> Real
  DeltaA2 : Fin m -> Fin n -> Real
  dual : Fin m -> Real
  first_system :
    rectMatMulVec
      (fun i j => A i j + DeltaBase i j + DeltaA1 i j)
      (higham21FlMGSCorrectedOutput fp Qhat y) = b
  second_system :
    higham21FlMGSCorrectedOutput fp Qhat y =
      rectTransposeMulVec
        (fun i j => A i j + DeltaBase i j + DeltaA2 i j) dual
  row_bound1 : forall i,
    rectRowNorm2 DeltaA1 i <= etaAction * rectRowNorm2 A i
  row_bound2 : forall i,
    rectRowNorm2 DeltaA2 i <= etaAction * rectRowNorm2 A i
  eta_nonneg : 0 <= etaAction

/-- Build the Lemma 21.2 transfer from the explicit rank-one feasibility and
transpose-range corrections.  The remaining numerical obligations are now
only the two displayed row bounds (and nonzero `x`/`z`). -/
noncomputable def Higham21MGSRoundedSystemTransfer.of_rankOneCorrections
    (fp : FPModel) {m n : Nat}
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (Qhat : Fin n -> Fin m -> Real) (y : Fin m -> Real)
    (DeltaBase : Fin m -> Fin n -> Real) (etaAction : Real)
    (z : Fin m -> Real)
    (hx : higham21FlMGSCorrectedOutput fp Qhat y ≠ 0)
    (hz : z ≠ 0)
    (heta : 0 <= etaAction)
    (hrow1 : forall i,
      rectRowNorm2
        (higham21MGSFeasibilityCorrection
          (fun r c => A r c + DeltaBase r c) b
          (higham21FlMGSCorrectedOutput fp Qhat y)) i <=
        etaAction * rectRowNorm2 A i)
    (hrow2 : forall i,
      rectRowNorm2
        (higham21MGSRangeCorrection
          (fun r c => A r c + DeltaBase r c)
          (higham21FlMGSCorrectedOutput fp Qhat y) z) i <=
        etaAction * rectRowNorm2 A i) :
    Higham21MGSRoundedSystemTransfer
      fp A b Qhat y DeltaBase etaAction := by
  let B : Fin m -> Fin n -> Real :=
    fun r c => A r c + DeltaBase r c
  let x : Fin n -> Real := higham21FlMGSCorrectedOutput fp Qhat y
  let DeltaA1 := higham21MGSFeasibilityCorrection B b x
  let DeltaA2 := higham21MGSRangeCorrection B x z
  refine
    { DeltaA1 := DeltaA1
      DeltaA2 := DeltaA2
      dual := z
      first_system := ?_
      second_system := ?_
      row_bound1 := ?_
      row_bound2 := ?_
      eta_nonneg := heta }
  . simpa [B, x, DeltaA1, add_assoc] using
      higham21_mgs_feasibilityCorrection_solves B b x hx
  . simpa [B, x, DeltaA2, add_assoc] using
      (higham21_mgs_rangeCorrection_represents B x z hz).symm
  . simpa [B, x, DeltaA1] using hrow1
  . simpa [B, x, DeltaA2] using hrow2

/-- Actual rounded-output rowwise theorem.  This is the economy-MGS form of
the Lemma 21.2 handoff used in Theorem 21.4. -/
theorem higham21_mgs_rounded_actual_output_rowwise_backward_stable
    (fp : FPModel) {m n : Nat}
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (Qhat : Fin n -> Fin m -> Real) (y : Fin m -> Real)
    (DeltaBase : Fin m -> Fin n -> Real)
    {etaBase etaAction : Real}
    (hetaBase : 0 <= etaBase)
    (hbase : forall i,
      rectRowNorm2 DeltaBase i <= etaBase * rectRowNorm2 A i)
    (htransfer : Higham21MGSRoundedSystemTransfer
      fp A b Qhat y DeltaBase etaAction)
    (Aplus : Fin n -> Fin m -> Real)
    (hRight : rectMatMul A Aplus = idMatrix m)
    (hsmall :
      3 * ((etaBase + etaAction) * Real.sqrt (n : Real) *
        higham21Cond2With A Aplus) < 1) :
    UndetRowwiseBackwardErrorBounded m n A b
      (higham21FlMGSCorrectedOutput fp Qhat y)
      (Real.sqrt 2 * (etaBase + etaAction)) := by
  let Delta1 : Fin m -> Fin n -> Real :=
    fun i j => DeltaBase i j + htransfer.DeltaA1 i j
  let Delta2 : Fin m -> Fin n -> Real :=
    fun i j => DeltaBase i j + htransfer.DeltaA2 i j
  let eta := etaBase + etaAction
  let rho := eta * Real.sqrt (n : Real) * higham21Cond2With A Aplus
  have heta : 0 <= eta := add_nonneg hetaBase htransfer.eta_nonneg
  have hrow1 : forall i,
      rectRowNorm2 Delta1 i <= eta * rectRowNorm2 A i := by
    intro i
    simpa [Delta1, eta] using
      higham21_rectRowNorm2_add_le_of_row_bounds
        DeltaBase htransfer.DeltaA1 A hbase htransfer.row_bound1 i
  have hrow2 : forall i,
      rectRowNorm2 Delta2 i <= eta * rectRowNorm2 A i := by
    intro i
    simpa [Delta2, eta] using
      higham21_rectRowNorm2_add_le_of_row_bounds
        DeltaBase htransfer.DeltaA2 A hbase htransfer.row_bound2 i
  have hfirst :
      rectMatMulVec (fun i j => A i j + Delta1 i j)
        (higham21FlMGSCorrectedOutput fp Qhat y) = b := by
    simpa [Delta1, add_assoc] using htransfer.first_system
  have hsecond :
      higham21FlMGSCorrectedOutput fp Qhat y =
        rectTransposeMulVec (fun i j => A i j + Delta2 i j)
          htransfer.dual := by
    simpa [Delta2, add_assoc] using htransfer.second_system
  have hprod1 : rectOpNorm2Le (rectMatMul Aplus Delta1) rho := by
    simpa [rho, eta] using
      higham21_rectOpNorm2Le_pseudoinverse_product_of_row_bounds
        A Delta1 Aplus eta heta hrow1
  have hprod2 : rectOpNorm2Le (rectMatMul Aplus Delta2) rho := by
    simpa [rho, eta] using
      higham21_rectOpNorm2Le_pseudoinverse_product_of_row_bounds
        A Delta2 Aplus eta heta hrow2
  apply higham21_lemma21_2_rowwise_backward_error_bound_of_pseudoinverse_products
    A Aplus Delta1 Delta2 b
      (higham21FlMGSCorrectedOutput fp Qhat y) htransfer.dual
      rho rho eta hRight hfirst hsecond hprod1 hprod2
  . simpa [rho, eta] using hsmall
  . exact heta
  . exact hrow1
  . exact hrow2

/-- Printed `omega^R` consequence for the actual rounded recurrence output. -/
theorem higham21_mgs_rounded_actual_output_omegaR_le
    (fp : FPModel) {m n : Nat}
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (Qhat : Fin n -> Fin m -> Real) (y : Fin m -> Real)
    (DeltaBase : Fin m -> Fin n -> Real)
    {etaBase etaAction : Real}
    (hetaBase : 0 <= etaBase)
    (hbase : forall i,
      rectRowNorm2 DeltaBase i <= etaBase * rectRowNorm2 A i)
    (htransfer : Higham21MGSRoundedSystemTransfer
      fp A b Qhat y DeltaBase etaAction)
    (Aplus : Fin n -> Fin m -> Real)
    (hRight : rectMatMul A Aplus = idMatrix m)
    (hsmall :
      3 * ((etaBase + etaAction) * Real.sqrt (n : Real) *
        higham21Cond2With A Aplus) < 1) :
    higham21RowwiseBackwardErrorOmegaR A b
      (higham21FlMGSCorrectedOutput fp Qhat y) <=
        Real.sqrt 2 * (etaBase + etaAction) := by
  exact higham21RowwiseBackwardErrorOmegaR_le_of_fixed_b_certificate
    (higham21_mgs_rounded_actual_output_rowwise_backward_stable
      fp A b Qhat y DeltaBase hetaBase hbase htransfer Aplus hRight hsmall)

/-- Explicit interface for the one missing structural step: convert the
proved repaired-action componentwise certificate into the two row-scaled
system perturbations consumed by `Higham21MGSRoundedSystemTransfer`. -/
def Higham21MGSRoundedActionToSystemTransfer
    (fp : FPModel) {m n : Nat}
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (Qhat Qrepair : Fin n -> Fin m -> Real)
    (Rhat : Fin m -> Fin m -> Real)
    (DeltaAT : Fin n -> Fin m -> Real)
    (y : Fin m -> Real) (etaAction : Real) : Type :=
  forall DeltaR : Fin m -> Fin m -> Real,
    (forall i j, |DeltaR i j| <= gamma fp m * |Rhat i j|) ->
    (forall i,
      matMulVec m (matTranspose (fun a b => Rhat a b + DeltaR a b)) y i =
        b i) ->
    (forall i,
      |higham21FlMGSCorrectedOutput fp Qhat y i -
          higham21MGSNaiveFormation Qrepair y i| <=
        higham21FlMGSRepairedActionBudget fp Qhat Qrepair y i) ->
    Higham21MGSRoundedSystemTransfer fp A b Qhat y
      (finiteTranspose
        (higham21MGSFoldedDeltaAT Qrepair DeltaAT DeltaR)) etaAction

/-- Theorem-21.4-level actual-output result with the computed triangular solve
folded into the repaired `R` factor.  The recurrence-specific remaining
hypothesis is `Higham21MGSRoundedActionToSystemTransfer`; the explicit
rank-one constructor above reduces it to row bounds and nonzero branches. -/
theorem higham21_mgs_rounded_forwardSub_actual_output_theorem21_4
    (fp : FPModel) {m n : Nat}
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (Qhat Qrepair : Fin n -> Fin m -> Real)
    (Rhat : Fin m -> Fin m -> Real)
    (DeltaAT : Fin n -> Fin m -> Real)
    {etaQR etaAction : Real}
    (hrepair : Higham21MGSSelectedRepair
      A Rhat Qrepair DeltaAT etaQR)
    (hdiag : forall i : Fin m, Rhat i i ≠ 0)
    (hvalidStep : gammaValid fp (n + 3))
    (hvalidSolve : gammaValid fp m)
    (htransfer : Higham21MGSRoundedActionToSystemTransfer
      fp A b Qhat Qrepair Rhat DeltaAT
        (fl_forwardSub fp m (matTranspose Rhat) b) etaAction)
    (Aplus : Fin n -> Fin m -> Real)
    (hRight : rectMatMul A Aplus = idMatrix m)
    (hsmall :
      3 * (((etaQR + gamma fp m * (1 + etaQR)) + etaAction) *
        Real.sqrt (n : Real) * higham21Cond2With A Aplus) < 1) :
    exists DeltaR : Fin m -> Fin m -> Real,
      (forall i j, |DeltaR i j| <= gamma fp m * |Rhat i j|) /\
      (forall i,
        matMulVec m (matTranspose (fun a b => Rhat a b + DeltaR a b))
          (fl_forwardSub fp m (matTranspose Rhat) b) i = b i) /\
      (forall i j,
        finiteTranspose A i j +
            higham21MGSFoldedDeltaAT Qrepair DeltaAT DeltaR i j =
          matMulRect n m m Qrepair
            (fun a b => Rhat a b + DeltaR a b) i j) /\
      UndetRowwiseBackwardErrorBounded m n A b
        (higham21FlMGSCorrectedOutput fp Qhat
          (fl_forwardSub fp m (matTranspose Rhat) b))
        (Real.sqrt 2 *
          ((etaQR + gamma fp m * (1 + etaQR)) + etaAction)) := by
  let y := fl_forwardSub fp m (matTranspose Rhat) b
  let etaBase := etaQR + gamma fp m * (1 + etaQR)
  obtain ⟨DeltaR, hDeltaR, hsolve⟩ :=
    higham21_theorem21_4_forwardSub_transpose_triangular_solve_backward_error
      fp m Rhat b hdiag hrepair.upper hvalidSolve
  have hgamma : 0 <= gamma fp m := gamma_nonneg fp hvalidSolve
  have hetaBase : 0 <= etaBase := by
    exact add_nonneg hrepair.eta_nonneg
      (mul_nonneg hgamma (add_nonneg zero_le_one hrepair.eta_nonneg))
  have hfoldFactor := higham21_mgs_folded_deltaAT_factor
    (finiteTranspose A) DeltaAT Qrepair Rhat DeltaR hrepair.factor
  have hfoldColumn := higham21_mgs_folded_deltaAT_column_bound
    (finiteTranspose A) DeltaAT Qrepair Rhat DeltaR
      hrepair.orthonormal hrepair.factor hrepair.eta_nonneg
      hrepair.column_bound hgamma hDeltaR
  have hbase : forall i,
      rectRowNorm2
        (finiteTranspose
          (higham21MGSFoldedDeltaAT Qrepair DeltaAT DeltaR)) i <=
        etaBase * rectRowNorm2 A i := by
    have hrows := higham21_row_bounds_of_transposed_qr_column_bounds
      (finiteTranspose A)
      (higham21MGSFoldedDeltaAT Qrepair DeltaAT DeltaR) hfoldColumn
    intro i
    simpa [etaBase] using hrows i
  have hcomparison : forall i,
      |higham21FlMGSCorrectedOutput fp Qhat y i -
          higham21MGSNaiveFormation Qrepair y i| <=
        higham21FlMGSRepairedActionBudget fp Qhat Qrepair y i :=
    higham21_fl_mgs_corrected_output_repaired_action_componentwise
      fp Qhat Qrepair y hvalidStep
  have hsystem := htransfer DeltaR hDeltaR (by simpa [y] using hsolve)
    hcomparison
  have hrowwise :=
    higham21_mgs_rounded_actual_output_rowwise_backward_stable
      fp A b Qhat y
      (finiteTranspose
        (higham21MGSFoldedDeltaAT Qrepair DeltaAT DeltaR))
      hetaBase hbase hsystem Aplus hRight (by simpa [etaBase] using hsmall)
  refine ⟨DeltaR, hDeltaR, hsolve, ?_, ?_⟩
  . exact hfoldFactor
  . simpa [y, etaBase] using hrowwise

/-- `omega^R` form of the folded actual-output theorem. -/
theorem higham21_mgs_rounded_forwardSub_actual_output_omegaR_le
    (fp : FPModel) {m n : Nat}
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (Qhat Qrepair : Fin n -> Fin m -> Real)
    (Rhat : Fin m -> Fin m -> Real)
    (DeltaAT : Fin n -> Fin m -> Real)
    {etaQR etaAction : Real}
    (hrepair : Higham21MGSSelectedRepair
      A Rhat Qrepair DeltaAT etaQR)
    (hdiag : forall i : Fin m, Rhat i i ≠ 0)
    (hvalidStep : gammaValid fp (n + 3))
    (hvalidSolve : gammaValid fp m)
    (htransfer : Higham21MGSRoundedActionToSystemTransfer
      fp A b Qhat Qrepair Rhat DeltaAT
        (fl_forwardSub fp m (matTranspose Rhat) b) etaAction)
    (Aplus : Fin n -> Fin m -> Real)
    (hRight : rectMatMul A Aplus = idMatrix m)
    (hsmall :
      3 * (((etaQR + gamma fp m * (1 + etaQR)) + etaAction) *
        Real.sqrt (n : Real) * higham21Cond2With A Aplus) < 1) :
    higham21RowwiseBackwardErrorOmegaR A b
      (higham21FlMGSCorrectedOutput fp Qhat
        (fl_forwardSub fp m (matTranspose Rhat) b)) <=
      Real.sqrt 2 *
        ((etaQR + gamma fp m * (1 + etaQR)) + etaAction) := by
  obtain ⟨DeltaR, hDeltaR, hsolve, hfactor, hrowwise⟩ :=
    higham21_mgs_rounded_forwardSub_actual_output_theorem21_4
      fp A b Qhat Qrepair Rhat DeltaAT hrepair hdiag hvalidStep
        hvalidSolve htransfer Aplus hRight hsmall
  exact higham21RowwiseBackwardErrorOmegaR_le_of_fixed_b_certificate hrowwise

end

end NumStability
