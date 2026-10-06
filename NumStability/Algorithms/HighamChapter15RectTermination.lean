-- Algorithms/HighamChapter15RectTermination.lean
--
-- Higham, 2nd ed., Chapter 15, p. 291: source-dimensional finite
-- termination of Algorithm 15.1 at p = 1 and p = infinity.

import NumStability.Algorithms.PNormPowerMethodRect
import NumStability.Algorithms.HighamChapter15ConvergenceProse

namespace NumStability

open scoped BigOperators
open Ch15

namespace RectPNormPair

/-! ## Rectangular endpoint p = 1 -/

/-- The column objective visited by rectangular Algorithm 15.1 at `p = 1`. -/
noncomputable def oneColumnValueRect {m n : Nat}
    (A : Fin m -> Fin n -> Real) (j : Fin n) : Real :=
  oneNormVec (fun i => A i j)

/-- After a rectangular `p = 1` update, the next estimate is the 1-norm of
the selected column. -/
theorem gammaSeq_one_succ_eq_column_rect {m n : Nat} (hn : 0 < n)
    (A : Fin m -> Fin n -> Real) (x0 : Fin n -> Real) (k : Nat) :
    (one hn A).gammaSeq x0 (k + 1) =
      oneColumnValueRect A
        (argmaxAbs hn ((one hn A).zof ((one hn A).xseq x0 k))) := by
  let P := one hn A
  let z := P.zof (P.xseq x0 k)
  let J := argmaxAbs hn z
  let s := signVec z J
  have hs : |s| = 1 := by
    simpa [s] using abs_signVec z J
  change oneNormVec (P.yof (P.xnext (P.xseq x0 k))) =
    oneNormVec (fun i => A i J)
  have hxnext : P.xnext (P.xseq x0 k) =
      fun j => s * basisVec J j := by
    rfl
  rw [hxnext]
  unfold RectPNormPair.yof oneNormVec
  apply Finset.sum_congr rfl
  intro i _hi
  change |Finset.univ.sum (fun j : Fin n => A i j * (s * basisVec J j))| =
    |A i J|
  have hsum :
      Finset.univ.sum (fun j : Fin n => A i j * (s * basisVec J j)) =
        s * A i J := by
    simp only [basisVec]
    rw [show Finset.univ.sum
        (fun j : Fin n => A i j * (s * if j = J then 1 else 0)) =
          Finset.univ.sum (fun j : Fin n => if j = J then s * A i J else 0) by
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases hj : j = J
      · subst j
        simp
        ring
      · simp [hj]]
    simp
  rw [hsum, abs_mul, hs, one_mul]

/-- **Higham p. 291, rectangular finite termination for `p = 1`.**
Among the first `n+1` tests, one succeeds.  The bound depends on the domain
dimension because the updates visit signed coordinate vectors in `R^n`. -/
theorem one_terminates_by_n_plus_one_rect {m n : Nat} (hn : 0 < n)
    (A : Fin m -> Fin n -> Real) (x0 : Fin n -> Real)
    (hx0 : oneNormVec x0 = 1) :
    exists k : Nat, k <= n /\ (one hn A).StopsAt ((one hn A).xseq x0 k) := by
  let P := one hn A
  let label : Nat -> Fin n := fun k => argmaxAbs hn (P.zof (P.xseq x0 k))
  let value : Fin n -> Real := oneColumnValueRect A
  obtain ⟨r, hrn, hrnoninc⟩ :=
    Ch15.exists_nonincreasing_step_of_fin_labels label value
  by_cases htest : P.StopsAt (P.xseq x0 (r + 1))
  · exact ⟨r + 1, by omega, htest⟩
  · have hstrict : P.gammaSeq x0 (r + 1) < P.gammaSeq x0 (r + 2) := by
      have hfirst : P.pOut (P.yof (P.xseq x0 (r + 1))) <
          P.qIn (P.zof (P.xseq x0 (r + 1))) :=
        (P.higham15_lemma15_2_rectangular_strict
          (P.xseq x0 (r + 1))).mp htest
      have hunit : P.pIn (P.xseq x0 (r + 1)) = 1 :=
        P.xseq_punit x0 hx0 (r + 1)
      have hsecond :=
        (P.higham15_lemma15_2b_rectangular (P.xseq x0 (r + 1)) hunit).2.1
      exact lt_of_lt_of_le hfirst
        (by simpa [RectPNormPair.gammaSeq, RectPNormPair.xseq] using hsecond)
    have hcol1 : P.gammaSeq x0 (r + 1) = value (label r) := by
      simpa [P, label, value] using gammaSeq_one_succ_eq_column_rect hn A x0 r
    have hcol2 : P.gammaSeq x0 (r + 2) = value (label (r + 1)) := by
      simpa [P, label, value, Nat.add_assoc] using
        gammaSeq_one_succ_eq_column_rect hn A x0 (r + 1)
    rw [hcol1, hcol2] at hstrict
    exact (not_lt_of_ge hrnoninc hstrict).elim

/-! ## Rectangular endpoint p = infinity -/

/-- The row objective visited by rectangular Algorithm 15.1 at `p = infinity`. -/
noncomputable def infRowValueRect {m n : Nat}
    (A : Fin m -> Fin n -> Real) (i : Fin m) : Real :=
  oneNormVec (fun j => A i j)

/-- The full `z` vector at the rectangular infinity endpoint is the selected
row, multiplied by the sign of the attaining output coordinate. -/
theorem zof_infinity_eq_signed_selected_row_rect {m n : Nat}
    (hm : 0 < m) (hn : 0 < n)
    (A : Fin m -> Fin n -> Real) (x : Fin n -> Real) :
    (infinity hm hn A).zof x = fun j =>
      signVec ((infinity hm hn A).yof x)
          (argmaxAbs hm ((infinity hm hn A).yof x)) *
        A (argmaxAbs hm ((infinity hm hn A).yof x)) j := by
  let P := infinity hm hn A
  let y := P.yof x
  let J := argmaxAbs hm y
  let s := signVec y J
  funext j
  change Finset.univ.sum (fun i : Fin m => A i j * (s * basisVec J i)) =
    s * A J j
  simp only [basisVec]
  rw [show Finset.univ.sum
      (fun i : Fin m => A i j * (s * if i = J then 1 else 0)) =
        Finset.univ.sum (fun i : Fin m => if i = J then s * A J j else 0) by
    apply Finset.sum_congr rfl
    intro i _hi
    by_cases hi : i = J
    · subst i
      simp
      ring
    · simp [hi]]
  simp

/-- At `p = infinity`, the dual vector selects an output row, and the
1-norm of `z` is exactly the 1-norm of that selected row. -/
theorem qIn_zof_infinity_eq_row_rect {m n : Nat} (hm : 0 < m) (hn : 0 < n)
    (A : Fin m -> Fin n -> Real) (x : Fin n -> Real) :
    (infinity hm hn A).qIn ((infinity hm hn A).zof x) =
      infRowValueRect A
        (argmaxAbs hm ((infinity hm hn A).yof x)) := by
  let P := infinity hm hn A
  let y := P.yof x
  let J := argmaxAbs hm y
  let s := signVec y J
  have hs : |s| = 1 := by
    simpa [s] using abs_signVec y J
  change oneNormVec (P.zof x) = oneNormVec (fun j => A J j)
  have hz : P.zof x = fun j => s * A J j := by
    funext j
    change Finset.univ.sum (fun i : Fin m => A i j * (s * basisVec J i)) =
      s * A J j
    simp only [basisVec]
    rw [show Finset.univ.sum
        (fun i : Fin m => A i j * (s * if i = J then 1 else 0)) =
          Finset.univ.sum (fun i : Fin m => if i = J then s * A J j else 0) by
      apply Finset.sum_congr rfl
      intro i _hi
      by_cases hi : i = J
      · subst i
        simp
        ring
      · simp [hi]]
    simp
  rw [hz]
  unfold oneNormVec
  apply Finset.sum_congr rfl
  intro j _hj
  rw [abs_mul, hs, one_mul]

/-- **Corrected rectangular endpoint theorem.**  At `p = infinity`, among
the first `m+1` tests one succeeds.  The count is `m+1`, not `n+1`, because
the extreme dual choices and the strictly increasing row objectives live in
the output space `R^m`. -/
theorem infinity_terminates_by_m_plus_one_rect {m n : Nat}
    (hm : 0 < m) (hn : 0 < n)
    (A : Fin m -> Fin n -> Real) (x0 : Fin n -> Real)
    (hx0 : infNormVec x0 = 1) :
    exists k : Nat, k <= m /\
      (infinity hm hn A).StopsAt ((infinity hm hn A).xseq x0 k) := by
  let P := infinity hm hn A
  let label : Nat -> Fin m := fun k => argmaxAbs hm (P.yof (P.xseq x0 k))
  let value : Fin m -> Real := infRowValueRect A
  obtain ⟨r, hrm, hrnoninc⟩ :=
    Ch15.exists_nonincreasing_step_of_fin_labels label value
  by_cases htest0 : P.StopsAt (P.xseq x0 r)
  · exact ⟨r, by omega, htest0⟩
  by_cases htest1 : P.StopsAt (P.xseq x0 (r + 1))
  · exact ⟨r + 1, by omega, htest1⟩
  · have hunit : P.pIn (P.xseq x0 r) = 1 := P.xseq_punit x0 hx0 r
    have hmiddle :=
      (P.higham15_lemma15_2b_rectangular (P.xseq x0 r) hunit).2.1
    have hstrict1 : P.pOut (P.yof (P.xseq x0 (r + 1))) <
        P.qIn (P.zof (P.xseq x0 (r + 1))) :=
      (P.higham15_lemma15_2_rectangular_strict
        (P.xseq x0 (r + 1))).mp htest1
    have hvalues : value (label r) < value (label (r + 1)) := by
      have hrow0 : P.qIn (P.zof (P.xseq x0 r)) = value (label r) := by
        have hraw := qIn_zof_infinity_eq_row_rect hm hn A (P.xseq x0 r)
        change P.qIn (P.zof (P.xseq x0 r)) =
          infRowValueRect A (argmaxAbs hm (P.yof (P.xseq x0 r))) at hraw
        simpa [label, value] using hraw
      have hrow1 : P.qIn (P.zof (P.xseq x0 (r + 1))) =
          value (label (r + 1)) := by
        have hraw := qIn_zof_infinity_eq_row_rect hm hn A (P.xseq x0 (r + 1))
        change P.qIn (P.zof (P.xseq x0 (r + 1))) =
          infRowValueRect A
            (argmaxAbs hm (P.yof (P.xseq x0 (r + 1))) ) at hraw
        simpa [label, value] using hraw
      rw [<- hrow0, <- hrow1]
      exact lt_of_le_of_lt
        (by simpa [RectPNormPair.xseq] using hmiddle) hstrict1
    exact (not_lt_of_ge hrnoninc hvalues).elim

/-! ## The printed rectangular `n+1` infinity bound is false -/

/-- A `5 x 3` matrix whose infinity-endpoint trace makes four strict
improvements before stopping. -/
def infinityNPlusOneCounterexampleA : Fin 5 -> Fin 3 -> Real :=
  ![![-14, 1, 1],
    ![-9, 9, -12],
    ![1, -16, 18],
    ![-3, -16, -6],
    ![-16, -14, 1]]

/-- Unit-infinity-norm start of the rectangular discrepancy trace. -/
noncomputable def infinityNPlusOneCounterexampleX0 : Fin 3 -> Real := ![-1, 1 / 5, 1]

private def infinityNPlusOneCounterexampleX1 : Fin 3 -> Real := ![-1, 1, 1]
private def infinityNPlusOneCounterexampleX2 : Fin 3 -> Real := ![1, 1, 1]
private def infinityNPlusOneCounterexampleX3 : Fin 3 -> Real := ![1, 1, -1]
private def infinityNPlusOneCounterexampleX4 : Fin 3 -> Real := ![-1, 1, -1]

private noncomputable def infinityNPlusOneCounterexampleY0 : Fin 5 -> Real :=
  ![76 / 5, -6 / 5, 69 / 5, -31 / 5, 71 / 5]

private def infinityNPlusOneCounterexampleY1 : Fin 5 -> Real :=
  ![16, 6, 1, -19, 3]

private def infinityNPlusOneCounterexampleY2 : Fin 5 -> Real :=
  ![-12, -12, 3, -25, -29]

private def infinityNPlusOneCounterexampleY3 : Fin 5 -> Real :=
  ![-14, 12, -33, -13, -31]

private def infinityNPlusOneCounterexampleY4 : Fin 5 -> Real :=
  ![14, 30, -35, -7, 1]

private theorem infinityNPlusOneCounterexample_yof_x0 :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).yof infinityNPlusOneCounterexampleX0 =
        infinityNPlusOneCounterexampleY0 := by
  funext i
  fin_cases i <;>
    simp [RectPNormPair.yof, infinity, infinityNPlusOneCounterexampleA,
      infinityNPlusOneCounterexampleX0, infinityNPlusOneCounterexampleY0,
      Fin.sum_univ_succ] <;>
    norm_num

private theorem infinityNPlusOneCounterexample_yof_x1 :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).yof infinityNPlusOneCounterexampleX1 =
        infinityNPlusOneCounterexampleY1 := by
  funext i
  fin_cases i <;>
    simp [RectPNormPair.yof, infinity, infinityNPlusOneCounterexampleA,
      infinityNPlusOneCounterexampleX1, infinityNPlusOneCounterexampleY1,
      Fin.sum_univ_succ] <;>
    norm_num

private theorem infinityNPlusOneCounterexample_yof_x2 :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).yof infinityNPlusOneCounterexampleX2 =
        infinityNPlusOneCounterexampleY2 := by
  funext i
  fin_cases i <;>
    simp [RectPNormPair.yof, infinity, infinityNPlusOneCounterexampleA,
      infinityNPlusOneCounterexampleX2, infinityNPlusOneCounterexampleY2,
      Fin.sum_univ_succ] <;>
    norm_num
  all_goals change (1 : Real) + 2 = 3
  all_goals norm_num

private theorem infinityNPlusOneCounterexample_yof_x3 :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).yof infinityNPlusOneCounterexampleX3 =
        infinityNPlusOneCounterexampleY3 := by
  funext i
  fin_cases i <;>
    simp [RectPNormPair.yof, infinity, infinityNPlusOneCounterexampleA,
      infinityNPlusOneCounterexampleX3, infinityNPlusOneCounterexampleY3,
      Fin.sum_univ_succ] <;>
    norm_num

private theorem infinityNPlusOneCounterexample_yof_x4 :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).yof infinityNPlusOneCounterexampleX4 =
        infinityNPlusOneCounterexampleY4 := by
  funext i
  fin_cases i <;>
    simp [RectPNormPair.yof, infinity, infinityNPlusOneCounterexampleA,
      infinityNPlusOneCounterexampleX4, infinityNPlusOneCounterexampleY4,
      Fin.sum_univ_succ] <;>
    norm_num

private theorem infinityNPlusOneCounterexample_argmax_x0 :
    argmaxAbs (by norm_num : 0 < 5)
        ((infinity (by norm_num) (by norm_num) infinityNPlusOneCounterexampleA).yof
          infinityNPlusOneCounterexampleX0) = (0 : Fin 5) := by
  let P := infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
    infinityNPlusOneCounterexampleA
  let J := argmaxAbs (by norm_num : 0 < 5)
    (P.yof infinityNPlusOneCounterexampleX0)
  have hJ := argmaxAbs_spec (by norm_num : 0 < 5)
    (P.yof infinityNPlusOneCounterexampleX0) (0 : Fin 5)
  change |P.yof infinityNPlusOneCounterexampleX0 0| <=
    |P.yof infinityNPlusOneCounterexampleX0 J| at hJ
  have hy : P.yof infinityNPlusOneCounterexampleX0 =
      infinityNPlusOneCounterexampleY0 := by
    simpa [P] using infinityNPlusOneCounterexample_yof_x0
  rw [hy] at hJ
  change J = (0 : Fin 5)
  rcases J with ⟨j, hj⟩
  by_cases htarget : j = 0
  · subst j
    rfl
  · interval_cases j <;>
      norm_num [infinityNPlusOneCounterexampleY0] at htarget
    all_goals norm_num [infinityNPlusOneCounterexampleY0] at hJ

private theorem infinityNPlusOneCounterexample_argmax_x1 :
    argmaxAbs (by norm_num : 0 < 5)
        ((infinity (by norm_num) (by norm_num) infinityNPlusOneCounterexampleA).yof
          infinityNPlusOneCounterexampleX1) = (3 : Fin 5) := by
  let P := infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
    infinityNPlusOneCounterexampleA
  let J := argmaxAbs (by norm_num : 0 < 5)
    (P.yof infinityNPlusOneCounterexampleX1)
  have hJ := argmaxAbs_spec (by norm_num : 0 < 5)
    (P.yof infinityNPlusOneCounterexampleX1) (3 : Fin 5)
  change |P.yof infinityNPlusOneCounterexampleX1 3| <=
    |P.yof infinityNPlusOneCounterexampleX1 J| at hJ
  have hy : P.yof infinityNPlusOneCounterexampleX1 =
      infinityNPlusOneCounterexampleY1 := by
    simpa [P] using infinityNPlusOneCounterexample_yof_x1
  rw [hy] at hJ
  have htargetValue :
      |infinityNPlusOneCounterexampleY1 (3 : Fin 5)| = 19 := by
    change |(-19 : Real)| = 19
    norm_num
  rw [htargetValue] at hJ
  change J = (3 : Fin 5)
  rcases J with ⟨j, hj⟩
  by_cases htarget : j = 3
  · subst j
    rfl
  · interval_cases j <;>
      norm_num [infinityNPlusOneCounterexampleY1] at htarget
    all_goals norm_num [infinityNPlusOneCounterexampleY1] at hJ

private theorem infinityNPlusOneCounterexample_argmax_x2 :
    argmaxAbs (by norm_num : 0 < 5)
        ((infinity (by norm_num) (by norm_num) infinityNPlusOneCounterexampleA).yof
          infinityNPlusOneCounterexampleX2) = (4 : Fin 5) := by
  let P := infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
    infinityNPlusOneCounterexampleA
  let J := argmaxAbs (by norm_num : 0 < 5)
    (P.yof infinityNPlusOneCounterexampleX2)
  have hJ := argmaxAbs_spec (by norm_num : 0 < 5)
    (P.yof infinityNPlusOneCounterexampleX2) (4 : Fin 5)
  change |P.yof infinityNPlusOneCounterexampleX2 4| <=
    |P.yof infinityNPlusOneCounterexampleX2 J| at hJ
  have hy : P.yof infinityNPlusOneCounterexampleX2 =
      infinityNPlusOneCounterexampleY2 := by
    simpa [P] using infinityNPlusOneCounterexample_yof_x2
  rw [hy] at hJ
  have htargetValue :
      |infinityNPlusOneCounterexampleY2 (4 : Fin 5)| = 29 := by
    change |(-29 : Real)| = 29
    norm_num
  rw [htargetValue] at hJ
  change J = (4 : Fin 5)
  rcases J with ⟨j, hj⟩
  by_cases htarget : j = 4
  · subst j
    rfl
  · interval_cases j <;>
      norm_num [infinityNPlusOneCounterexampleY2] at htarget
    all_goals norm_num [infinityNPlusOneCounterexampleY2] at hJ

private theorem infinityNPlusOneCounterexample_argmax_x3 :
    argmaxAbs (by norm_num : 0 < 5)
        ((infinity (by norm_num) (by norm_num) infinityNPlusOneCounterexampleA).yof
          infinityNPlusOneCounterexampleX3) = (2 : Fin 5) := by
  let P := infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
    infinityNPlusOneCounterexampleA
  let J := argmaxAbs (by norm_num : 0 < 5)
    (P.yof infinityNPlusOneCounterexampleX3)
  have hJ := argmaxAbs_spec (by norm_num : 0 < 5)
    (P.yof infinityNPlusOneCounterexampleX3) (2 : Fin 5)
  change |P.yof infinityNPlusOneCounterexampleX3 2| <=
    |P.yof infinityNPlusOneCounterexampleX3 J| at hJ
  have hy : P.yof infinityNPlusOneCounterexampleX3 =
      infinityNPlusOneCounterexampleY3 := by
    simpa [P] using infinityNPlusOneCounterexample_yof_x3
  rw [hy] at hJ
  have htargetValue :
      |infinityNPlusOneCounterexampleY3 (2 : Fin 5)| = 33 := by
    change |(-33 : Real)| = 33
    norm_num
  rw [htargetValue] at hJ
  change J = (2 : Fin 5)
  rcases J with ⟨j, hj⟩
  by_cases htarget : j = 2
  · subst j
    rfl
  · interval_cases j <;>
      norm_num [infinityNPlusOneCounterexampleY3] at htarget
    all_goals norm_num [infinityNPlusOneCounterexampleY3] at hJ

private theorem infinityNPlusOneCounterexample_argmax_x4 :
    argmaxAbs (by norm_num : 0 < 5)
        ((infinity (by norm_num) (by norm_num) infinityNPlusOneCounterexampleA).yof
          infinityNPlusOneCounterexampleX4) = (2 : Fin 5) := by
  let P := infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
    infinityNPlusOneCounterexampleA
  let J := argmaxAbs (by norm_num : 0 < 5)
    (P.yof infinityNPlusOneCounterexampleX4)
  have hJ := argmaxAbs_spec (by norm_num : 0 < 5)
    (P.yof infinityNPlusOneCounterexampleX4) (2 : Fin 5)
  change |P.yof infinityNPlusOneCounterexampleX4 2| <=
    |P.yof infinityNPlusOneCounterexampleX4 J| at hJ
  have hy : P.yof infinityNPlusOneCounterexampleX4 =
      infinityNPlusOneCounterexampleY4 := by
    simpa [P] using infinityNPlusOneCounterexample_yof_x4
  rw [hy] at hJ
  have htargetValue :
      |infinityNPlusOneCounterexampleY4 (2 : Fin 5)| = 35 := by
    change |(-35 : Real)| = 35
    norm_num
  rw [htargetValue] at hJ
  change J = (2 : Fin 5)
  rcases J with ⟨j, hj⟩
  by_cases htarget : j = 2
  · subst j
    rfl
  · interval_cases j <;>
      norm_num [infinityNPlusOneCounterexampleY4] at htarget
    all_goals norm_num [infinityNPlusOneCounterexampleY4] at hJ

private def infinityNPlusOneCounterexampleZ0 : Fin 3 -> Real := ![-14, 1, 1]
private def infinityNPlusOneCounterexampleZ1 : Fin 3 -> Real := ![3, 16, 6]
private def infinityNPlusOneCounterexampleZ2 : Fin 3 -> Real := ![16, 14, -1]
private def infinityNPlusOneCounterexampleZ3 : Fin 3 -> Real := ![-1, 16, -18]
private def infinityNPlusOneCounterexampleZ4 : Fin 3 -> Real := ![-1, 16, -18]

private theorem infinityNPlusOneCounterexample_zof_x0 :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).zof infinityNPlusOneCounterexampleX0 =
        infinityNPlusOneCounterexampleZ0 := by
  rw [zof_infinity_eq_signed_selected_row_rect,
    infinityNPlusOneCounterexample_argmax_x0,
    infinityNPlusOneCounterexample_yof_x0]
  have hs : signVec infinityNPlusOneCounterexampleY0 (0 : Fin 5) = 1 := by
    change (if 0 <= (76 / 5 : Real) then 1 else -1) = 1
    norm_num
  rw [hs]
  funext j
  fin_cases j <;>
    norm_num [infinityNPlusOneCounterexampleA,
      infinityNPlusOneCounterexampleZ0]

private theorem infinityNPlusOneCounterexample_zof_x1 :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).zof infinityNPlusOneCounterexampleX1 =
        infinityNPlusOneCounterexampleZ1 := by
  rw [zof_infinity_eq_signed_selected_row_rect,
    infinityNPlusOneCounterexample_argmax_x1,
    infinityNPlusOneCounterexample_yof_x1]
  have hs : signVec infinityNPlusOneCounterexampleY1 (3 : Fin 5) = -1 := by
    change (if 0 <= (-19 : Real) then 1 else -1) = -1
    norm_num
  rw [hs]
  have hrow :
      (fun j => infinityNPlusOneCounterexampleA (3 : Fin 5) j) =
        ![-3, -16, -6] := by
    rfl
  funext j
  rw [congrFun hrow j]
  fin_cases j <;>
    simp [infinityNPlusOneCounterexampleZ1]

private theorem infinityNPlusOneCounterexample_zof_x2 :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).zof infinityNPlusOneCounterexampleX2 =
        infinityNPlusOneCounterexampleZ2 := by
  rw [zof_infinity_eq_signed_selected_row_rect,
    infinityNPlusOneCounterexample_argmax_x2,
    infinityNPlusOneCounterexample_yof_x2]
  have hs : signVec infinityNPlusOneCounterexampleY2 (4 : Fin 5) = -1 := by
    change (if 0 <= (-29 : Real) then 1 else -1) = -1
    norm_num
  rw [hs]
  have hrow :
      (fun j => infinityNPlusOneCounterexampleA (4 : Fin 5) j) =
        ![-16, -14, 1] := by
    rfl
  funext j
  rw [congrFun hrow j]
  fin_cases j <;>
    simp [infinityNPlusOneCounterexampleZ2]

private theorem infinityNPlusOneCounterexample_zof_x3 :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).zof infinityNPlusOneCounterexampleX3 =
        infinityNPlusOneCounterexampleZ3 := by
  rw [zof_infinity_eq_signed_selected_row_rect,
    infinityNPlusOneCounterexample_argmax_x3,
    infinityNPlusOneCounterexample_yof_x3]
  have hs : signVec infinityNPlusOneCounterexampleY3 (2 : Fin 5) = -1 := by
    change (if 0 <= (-33 : Real) then 1 else -1) = -1
    norm_num
  rw [hs]
  have hrow :
      (fun j => infinityNPlusOneCounterexampleA (2 : Fin 5) j) =
        ![1, -16, 18] := by
    rfl
  funext j
  rw [congrFun hrow j]
  fin_cases j <;>
    simp [infinityNPlusOneCounterexampleZ3]

private theorem infinityNPlusOneCounterexample_zof_x4 :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).zof infinityNPlusOneCounterexampleX4 =
        infinityNPlusOneCounterexampleZ4 := by
  rw [zof_infinity_eq_signed_selected_row_rect,
    infinityNPlusOneCounterexample_argmax_x4,
    infinityNPlusOneCounterexample_yof_x4]
  have hs : signVec infinityNPlusOneCounterexampleY4 (2 : Fin 5) = -1 := by
    change (if 0 <= (-35 : Real) then 1 else -1) = -1
    norm_num
  rw [hs]
  have hrow :
      (fun j => infinityNPlusOneCounterexampleA (2 : Fin 5) j) =
        ![1, -16, 18] := by
    rfl
  funext j
  rw [congrFun hrow j]
  fin_cases j <;>
    simp [infinityNPlusOneCounterexampleZ4]

private theorem infinityNPlusOneCounterexample_xnext_x0 :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).xnext infinityNPlusOneCounterexampleX0 =
        infinityNPlusOneCounterexampleX1 := by
  change signVec
      ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
        infinityNPlusOneCounterexampleA).zof infinityNPlusOneCounterexampleX0) =
    infinityNPlusOneCounterexampleX1
  rw [infinityNPlusOneCounterexample_zof_x0]
  funext j
  fin_cases j <;>
    simp [signVec, infinityNPlusOneCounterexampleZ0,
      infinityNPlusOneCounterexampleX1]

private theorem infinityNPlusOneCounterexample_xnext_x1 :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).xnext infinityNPlusOneCounterexampleX1 =
        infinityNPlusOneCounterexampleX2 := by
  change signVec
      ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
        infinityNPlusOneCounterexampleA).zof infinityNPlusOneCounterexampleX1) =
    infinityNPlusOneCounterexampleX2
  rw [infinityNPlusOneCounterexample_zof_x1]
  funext j
  fin_cases j <;>
    simp [signVec, infinityNPlusOneCounterexampleZ1,
      infinityNPlusOneCounterexampleX2]

private theorem infinityNPlusOneCounterexample_xnext_x2 :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).xnext infinityNPlusOneCounterexampleX2 =
        infinityNPlusOneCounterexampleX3 := by
  change signVec
      ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
        infinityNPlusOneCounterexampleA).zof infinityNPlusOneCounterexampleX2) =
    infinityNPlusOneCounterexampleX3
  rw [infinityNPlusOneCounterexample_zof_x2]
  funext j
  fin_cases j <;>
    simp [signVec, infinityNPlusOneCounterexampleZ2,
      infinityNPlusOneCounterexampleX3]

private theorem infinityNPlusOneCounterexample_xnext_x3 :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).xnext infinityNPlusOneCounterexampleX3 =
        infinityNPlusOneCounterexampleX4 := by
  change signVec
      ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
        infinityNPlusOneCounterexampleA).zof infinityNPlusOneCounterexampleX3) =
    infinityNPlusOneCounterexampleX4
  rw [infinityNPlusOneCounterexample_zof_x3]
  funext j
  fin_cases j <;>
    simp [signVec, infinityNPlusOneCounterexampleZ3,
      infinityNPlusOneCounterexampleX4]

private theorem infinityNPlusOneCounterexample_xseq_zero :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).xseq infinityNPlusOneCounterexampleX0 0 =
        infinityNPlusOneCounterexampleX0 := by
  rfl

private theorem infinityNPlusOneCounterexample_xseq_one :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).xseq infinityNPlusOneCounterexampleX0 1 =
        infinityNPlusOneCounterexampleX1 := by
  change (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
    infinityNPlusOneCounterexampleA).xnext infinityNPlusOneCounterexampleX0 =
      infinityNPlusOneCounterexampleX1
  exact infinityNPlusOneCounterexample_xnext_x0

private theorem infinityNPlusOneCounterexample_xseq_two :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).xseq infinityNPlusOneCounterexampleX0 2 =
        infinityNPlusOneCounterexampleX2 := by
  change (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
    infinityNPlusOneCounterexampleA).xnext
      ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
        infinityNPlusOneCounterexampleA).xnext infinityNPlusOneCounterexampleX0) =
    infinityNPlusOneCounterexampleX2
  rw [infinityNPlusOneCounterexample_xnext_x0,
    infinityNPlusOneCounterexample_xnext_x1]

private theorem infinityNPlusOneCounterexample_xseq_three :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).xseq infinityNPlusOneCounterexampleX0 3 =
        infinityNPlusOneCounterexampleX3 := by
  change (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
    infinityNPlusOneCounterexampleA).xnext
      ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
        infinityNPlusOneCounterexampleA).xnext
        ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
          infinityNPlusOneCounterexampleA).xnext infinityNPlusOneCounterexampleX0)) =
    infinityNPlusOneCounterexampleX3
  rw [infinityNPlusOneCounterexample_xnext_x0,
    infinityNPlusOneCounterexample_xnext_x1,
    infinityNPlusOneCounterexample_xnext_x2]

private theorem infinityNPlusOneCounterexample_xseq_four :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).xseq infinityNPlusOneCounterexampleX0 4 =
        infinityNPlusOneCounterexampleX4 := by
  change (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
    infinityNPlusOneCounterexampleA).xnext
      ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
        infinityNPlusOneCounterexampleA).xnext
        ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
          infinityNPlusOneCounterexampleA).xnext
          ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
            infinityNPlusOneCounterexampleA).xnext infinityNPlusOneCounterexampleX0))) =
    infinityNPlusOneCounterexampleX4
  rw [infinityNPlusOneCounterexample_xnext_x0,
    infinityNPlusOneCounterexample_xnext_x1,
    infinityNPlusOneCounterexample_xnext_x2,
    infinityNPlusOneCounterexample_xnext_x3]

private theorem infinityNPlusOneCounterexample_not_stops_x0 :
    Not ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).StopsAt infinityNPlusOneCounterexampleX0) := by
  change Not (oneNormVec
      ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
        infinityNPlusOneCounterexampleA).zof infinityNPlusOneCounterexampleX0) <=
    Finset.univ.sum (fun j : Fin 3 =>
      (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
        infinityNPlusOneCounterexampleA).zof infinityNPlusOneCounterexampleX0 j *
          infinityNPlusOneCounterexampleX0 j))
  rw [infinityNPlusOneCounterexample_zof_x0]
  simp [oneNormVec, infinityNPlusOneCounterexampleZ0,
    infinityNPlusOneCounterexampleX0, Fin.sum_univ_succ]
  norm_num

private theorem infinityNPlusOneCounterexample_not_stops_x1 :
    Not ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).StopsAt infinityNPlusOneCounterexampleX1) := by
  change Not (oneNormVec
      ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
        infinityNPlusOneCounterexampleA).zof infinityNPlusOneCounterexampleX1) <=
    Finset.univ.sum (fun j : Fin 3 =>
      (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
        infinityNPlusOneCounterexampleA).zof infinityNPlusOneCounterexampleX1 j *
          infinityNPlusOneCounterexampleX1 j))
  rw [infinityNPlusOneCounterexample_zof_x1]
  simp [oneNormVec, infinityNPlusOneCounterexampleZ1,
    infinityNPlusOneCounterexampleX1, Fin.sum_univ_succ]
  calc
    (16 : Real) + 6 < 3 + (16 + 6) := lt_add_of_pos_left _ (by norm_num)
    _ < 3 + (3 + (16 + 6)) := lt_add_of_pos_left _ (by norm_num)

private theorem infinityNPlusOneCounterexample_not_stops_x2 :
    Not ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).StopsAt infinityNPlusOneCounterexampleX2) := by
  change Not (oneNormVec
      ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
        infinityNPlusOneCounterexampleA).zof infinityNPlusOneCounterexampleX2) <=
    Finset.univ.sum (fun j : Fin 3 =>
      (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
        infinityNPlusOneCounterexampleA).zof infinityNPlusOneCounterexampleX2 j *
          infinityNPlusOneCounterexampleX2 j))
  rw [infinityNPlusOneCounterexample_zof_x2]
  simp [oneNormVec, infinityNPlusOneCounterexampleZ2,
    infinityNPlusOneCounterexampleX2, Fin.sum_univ_succ]
  calc
    (14 : Real) < 14 + 1 := lt_add_of_pos_right _ (by norm_num)
    _ < 14 + 1 + 1 := lt_add_of_pos_right _ (by norm_num)

private theorem infinityNPlusOneCounterexample_not_stops_x3 :
    Not ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).StopsAt infinityNPlusOneCounterexampleX3) := by
  change Not (oneNormVec
      ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
        infinityNPlusOneCounterexampleA).zof infinityNPlusOneCounterexampleX3) <=
    Finset.univ.sum (fun j : Fin 3 =>
      (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
        infinityNPlusOneCounterexampleA).zof infinityNPlusOneCounterexampleX3 j *
          infinityNPlusOneCounterexampleX3 j))
  rw [infinityNPlusOneCounterexample_zof_x3]
  simp [oneNormVec, infinityNPlusOneCounterexampleZ3,
    infinityNPlusOneCounterexampleX3, Fin.sum_univ_succ]
  calc
    (16 : Real) + 18 < 1 + (16 + 18) := lt_add_of_pos_left _ (by norm_num)
    _ < 1 + (1 + (16 + 18)) := lt_add_of_pos_left _ (by norm_num)

private theorem infinityNPlusOneCounterexample_stops_x4 :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).StopsAt infinityNPlusOneCounterexampleX4 := by
  change oneNormVec
      ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
        infinityNPlusOneCounterexampleA).zof infinityNPlusOneCounterexampleX4) <=
    Finset.univ.sum (fun j : Fin 3 =>
      (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
        infinityNPlusOneCounterexampleA).zof infinityNPlusOneCounterexampleX4 j *
          infinityNPlusOneCounterexampleX4 j)
  rw [infinityNPlusOneCounterexample_zof_x4]
  simp [oneNormVec, infinityNPlusOneCounterexampleZ4,
    infinityNPlusOneCounterexampleX4, Fin.sum_univ_succ]

/-- The displayed counterexample starts from a unit infinity-norm vector. -/
theorem infinityNPlusOneCounterexample_unit :
    infNormVec infinityNPlusOneCounterexampleX0 = 1 := by
  apply le_antisymm
  · apply infNormVec_le_of_abs_le
    · intro i
      fin_cases i <;> norm_num [infinityNPlusOneCounterexampleX0]
    · norm_num
  · have h := abs_le_infNormVec infinityNPlusOneCounterexampleX0 (0 : Fin 3)
    norm_num [infinityNPlusOneCounterexampleX0] at h
    exact h

/-- **Formal discrepancy witness for Higham p. 291.**  For this `5 x 3`
matrix and unit start, none of the first `n+1 = 4` tests (`k = 0,1,2,3`)
succeeds.  Thus the printed rectangular `n+1` bound is false at
`p = infinity`; the valid general bound is the output-dimensional `m+1`
bound proved by `infinity_terminates_by_m_plus_one_rect`. -/
theorem higham15_rectangular_infinity_n_plus_one_source_discrepancy :
    Not (exists k : Nat, k <= 3 /\
      (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
        infinityNPlusOneCounterexampleA).StopsAt
          ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
            infinityNPlusOneCounterexampleA).xseq
              infinityNPlusOneCounterexampleX0 k)) := by
  rintro ⟨k, hk, hstop⟩
  interval_cases k
  · rw [infinityNPlusOneCounterexample_xseq_zero] at hstop
    exact infinityNPlusOneCounterexample_not_stops_x0 hstop
  · rw [infinityNPlusOneCounterexample_xseq_one] at hstop
    exact infinityNPlusOneCounterexample_not_stops_x1 hstop
  · rw [infinityNPlusOneCounterexample_xseq_two] at hstop
    exact infinityNPlusOneCounterexample_not_stops_x2 hstop
  · rw [infinityNPlusOneCounterexample_xseq_three] at hstop
    exact infinityNPlusOneCounterexample_not_stops_x3 hstop

/-- The same discrepancy trace does stop at its fifth test, `k = 4`. -/
theorem higham15_rectangular_infinity_counterexample_stops_at_four :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).StopsAt
        ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
          infinityNPlusOneCounterexampleA).xseq
            infinityNPlusOneCounterexampleX0 4) := by
  rw [infinityNPlusOneCounterexample_xseq_four]
  exact infinityNPlusOneCounterexample_stops_x4

end RectPNormPair

end NumStability
