-- Algorithms/Ch14GJEOperationalBridge.lean
--
-- Operational audit bridges for Higham Chapter 14, Algorithm 14.4 and
-- Theorem 14.5.  This file separates data that can be constructed from an
-- executed source trace from the genuinely missing finalization contract.

import NumStability.Algorithms.Ch14GJETheorem145SourceClosure

namespace NumStability.Ch14Ext

open Filter Asymptotics
open NumStability

/-! ## Canonical output, inverse, and solve witnesses -/

/-- The returned vector of the recursively executed second stage.  With this
definition, the `final_vector` field of the older family contract is
definitionally discharged rather than supplied as an independent certificate. -/
noncomputable def ch14ext_gjeSourceComputedOutput {n : Nat}
    (fp : FPModel) (s : Ch14GJEState n) : Fin n -> Real :=
  ch14ext_gjeSourceTraceRhs fp 1 s n

@[simp] theorem ch14ext_gjeSourceComputedOutput_eq {n : Nat}
    (fp : FPModel) (s : Ch14GJEState n) (i : Fin n) :
    ch14ext_gjeSourceComputedOutput fp s i =
      ch14ext_gjeSourceTraceRhs fp 1 s n i := by
  rfl

/-- The exact inverse used in the analysis is canonical once the computed
upper factor is nonsingular. -/
noncomputable def ch14ext_gjeCanonicalUpperInverse {n : Nat}
    (U : Fin n -> Fin n -> Real) : Fin n -> Fin n -> Real :=
  nonsingInv n U

/-- The exact comparison solution of the computed upper-triangular system is
canonical once its inverse is fixed.  It is an analysis-only object, not an
extra rounded computation. -/
noncomputable def ch14ext_gjeCanonicalUpperSolve {n : Nat}
    (U : Fin n -> Fin n -> Real) (y : Fin n -> Real) : Fin n -> Real :=
  matMulVec n (ch14ext_gjeCanonicalUpperInverse U) y

/-- Nonsingularity constructs the two-sided inverse certificate formerly
passed separately to the source-family endpoint. -/
theorem ch14ext_gjeCanonicalUpperInverse_isInverse {n : Nat}
    (U : Fin n -> Fin n -> Real)
    (hdet : Matrix.det (Matrix.of U : Matrix (Fin n) (Fin n) Real) ≠ 0) :
    IsInverse n U (ch14ext_gjeCanonicalUpperInverse U) := by
  simpa [ch14ext_gjeCanonicalUpperInverse] using
    isInverse_nonsingInv_of_det_ne_zero n U hdet

/-- The canonical comparison solution solves the computed upper system
exactly.  Thus the `hUz`/`upper_solve` fields in the old endpoints are not
independent mathematical assumptions once nonsingularity is known. -/
theorem ch14ext_gjeCanonicalUpperSolve_exact {n : Nat}
    (U : Fin n -> Fin n -> Real) (y : Fin n -> Real)
    (hdet : Matrix.det (Matrix.of U : Matrix (Fin n) (Fin n) Real) ≠ 0) :
    forall i : Fin n,
      matMulVec n U (ch14ext_gjeCanonicalUpperSolve U y) i = y i := by
  have hInv := ch14ext_gjeCanonicalUpperInverse_isInverse U hdet
  have h := matMulVec_of_isRightInverse U
    (ch14ext_gjeCanonicalUpperInverse U) hInv.2 y
  intro i
  exact congrFun h i

/-- Uniform boundedness of the canonical inverse and of the computed RHS
constructs uniform boundedness of the canonical exact comparison solve. -/
theorem ch14ext_gjeCanonicalUpperSolve_family_isBigOOne
    {I : Type*} {l : Filter I} {n : Nat}
    {U : I -> Fin n -> Fin n -> Real} {y : I -> Fin n -> Real}
    (hInv : MatrixFamilyIsBigOOne l
      (fun t => ch14ext_gjeCanonicalUpperInverse (U t)))
    (hy : VectorFamilyIsBigOOne l y) :
    VectorFamilyIsBigOOne l
      (fun t => ch14ext_gjeCanonicalUpperSolve (U t) (y t)) := by
  simpa [ch14ext_gjeCanonicalUpperSolve] using
    ch14ext_matrixFamily_mul_vectorFamily_isBigOOne hInv hy

/-! ## Structurally finalized source execution -/

/-- The source-active rounded matrix step with the eliminated entry stored as
an exact structural zero.  The arithmetic update is unchanged everywhere
else.  This models the usual implementation convention that a dead
Gauss--Jordan entry is not subsequently retained as rounded data. -/
noncomputable def ch14ext_gjeFinalizedSourceStepMatrix {n : Nat}
    (fp : FPModel) (U : Fin n -> Fin n -> Real) (k : Fin n) :
    Fin n -> Fin n -> Real :=
  fun i j =>
    if i.val < k.val /\ j = k then 0
    else ch14ext_gjeSourceStepMatrix fp n U k i j

/-- A finalized step writes the active entry in the pivot column as zero. -/
@[simp] theorem ch14ext_gjeFinalizedSourceStepMatrix_pivot_column {n : Nat}
    (fp : FPModel) (U : Fin n -> Fin n -> Real) (k i : Fin n)
    (hik : i.val < k.val) :
    ch14ext_gjeFinalizedSourceStepMatrix fp U k i k = 0 := by
  simp [ch14ext_gjeFinalizedSourceStepMatrix, hik]

/-- Columns already eliminated before `k` are not modified by a finalized
step. -/
theorem ch14ext_gjeFinalizedSourceStepMatrix_preserves_left {n : Nat}
    (fp : FPModel) (U : Fin n -> Fin n -> Real) (k i j : Fin n)
    (hjk : j.val < k.val) :
    ch14ext_gjeFinalizedSourceStepMatrix fp U k i j = U i j := by
  have hzero : Not (i.val < k.val /\ j = k) := by
    intro h
    rw [h.2] at hjk
    omega
  have hinactive : Not (ch14ext_gjeSourceActive k i j) := by
    intro h
    exact (Nat.not_le_of_lt hjk) h.2
  rw [ch14ext_gjeFinalizedSourceStepMatrix]
  simp only [if_neg hzero]
  simp [ch14ext_gjeSourceStepMatrix, hinactive]

/-- Finalization never changes a diagonal entry. -/
theorem ch14ext_gjeFinalizedSourceStepMatrix_diag {n : Nat}
    (fp : FPModel) (U : Fin n -> Fin n -> Real) (k i : Fin n) :
    ch14ext_gjeFinalizedSourceStepMatrix fp U k i i = U i i := by
  by_cases hik : i.val < k.val
  · have hine : Ne i k := by
      intro h
      subst i
      omega
    have hinactive : Not (ch14ext_gjeSourceActive k i i) := by
      intro h
      omega
    have hzero : Not (i.val < k.val /\ i = k) := by aesop
    rw [ch14ext_gjeFinalizedSourceStepMatrix]
    simp only [if_neg hzero]
    simp [ch14ext_gjeSourceStepMatrix, hinactive]
  · have hzero : Not (i.val < k.val /\ i = k) := by aesop
    have hinactive : Not (ch14ext_gjeSourceActive k i i) := by
      intro h
      omega
    rw [ch14ext_gjeFinalizedSourceStepMatrix]
    simp only [if_neg hzero]
    simp [ch14ext_gjeSourceStepMatrix, hinactive]

/-- The exact elementary row operation annihilates an active entry of the
pivot column. -/
theorem ch14ext_gjeStageMatrix_mul_pivot_column_eq_zero {n : Nat}
    (U : Fin n -> Fin n -> Real) (k i : Fin n)
    (hik : Ne i k) (hpiv : Ne (U k k) 0) :
    matMul n (ch14ext_gjeStageMatrix n U k) U i k = 0 := by
  rw [show matMul n (ch14ext_gjeStageMatrix n U k) U i k =
      U i k - ch14ext_gjeMultVec n U k i * U k k by
    exact ch14ext_gjeStageMatrix_mulVec_row n U k i k]
  simp [ch14ext_gjeMultVec, hik]
  field_simp
  ring

/-- The structurally finalized step satisfies exactly the same local
`gamma_3` contract as the arithmetic source step.  At the newly zeroed entry
both the computed value and the exact elementary-row-operation result are
zero, so finalization introduces no extra error. -/
theorem ch14ext_gjeFinalizedSourceStepMatrix_local_14_25 {n : Nat}
    (fp : FPModel) (U : Fin n -> Fin n -> Real) (k : Fin n)
    (hUpper : forall a b : Fin n, b.val < a.val -> U a b = 0)
    (hpiv : Ne (U k k) 0) (h3 : gammaValid fp 3) :
    forall i j : Fin n,
      |ch14ext_gjeFinalizedSourceStepMatrix fp U k i j -
          matMul n (ch14ext_gjeStageMatrix n U k) U i j| <=
        gamma fp 3 *
          matMul n (absMatrix n (ch14ext_gjeStageMatrix n U k))
            (absMatrix n U) i j := by
  intro i j
  by_cases hzero : i.val < k.val /\ j = k
  · rcases hzero with ⟨hik, hjk⟩
    subst j
    have hine : Ne i k := by
      intro h
      subst i
      omega
    rw [ch14ext_gjeFinalizedSourceStepMatrix_pivot_column fp U k i hik,
      ch14ext_gjeStageMatrix_mul_pivot_column_eq_zero U k i hine hpiv,
      sub_zero, abs_zero]
    exact mul_nonneg (gamma_nonneg fp h3)
      (Finset.sum_nonneg fun l _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  · rw [ch14ext_gjeFinalizedSourceStepMatrix]
    simp only [if_neg hzero]
    exact (ch14ext_gjeSource_local_matrix_14_25 fp U k hUpper hpiv h3).2.1 i j

/-- A finalized step preserves upper-triangular storage. -/
theorem ch14ext_gjeFinalizedSourceStepMatrix_upper {n : Nat}
    (fp : FPModel) (U : Fin n -> Fin n -> Real) (k : Fin n)
    (hUpper : forall a b : Fin n, b.val < a.val -> U a b = 0) :
    forall i j : Fin n, j.val < i.val ->
      ch14ext_gjeFinalizedSourceStepMatrix fp U k i j = 0 := by
  intro i j hji
  by_cases hzero : i.val < k.val /\ j = k
  · simp [ch14ext_gjeFinalizedSourceStepMatrix, hzero]
  · rw [ch14ext_gjeFinalizedSourceStepMatrix]
    simp only [if_neg hzero]
    exact ch14ext_gjeSourceStepMatrix_upper fp U k hUpper i j hji

/-- One coupled finalized matrix/RHS step.  The RHS follows the same rounded
source operation as before; only the dead matrix storage entry is overwritten
with its exact structural value. -/
noncomputable def ch14ext_gjeFinalizedSourceStepState {n : Nat}
    (fp : FPModel) (s : Ch14GJEState n) (k : Fin n) : Ch14GJEState n where
  matrix := ch14ext_gjeFinalizedSourceStepMatrix fp s.matrix k
  rhs := ch14ext_gjeSourceStepVec fp n s.matrix k s.rhs

/-- Recursively executed, structurally finalized second-stage trace. -/
noncomputable def ch14ext_gjeFinalizedSourceTrace {n : Nat}
    (fp : FPModel) (start : Nat) (s : Ch14GJEState n) :
    Nat -> Ch14GJEState n
  | 0 => s
  | t + 1 =>
      if h : start + t < n then
        ch14ext_gjeFinalizedSourceStepState fp
          (ch14ext_gjeFinalizedSourceTrace fp start s t) ⟨start + t, h⟩
      else ch14ext_gjeFinalizedSourceTrace fp start s t

/-- Absolute-indexed matrix view of the finalized trace. -/
noncomputable def ch14ext_gjeFinalizedSourceTraceMatrix {n : Nat}
    (fp : FPModel) (start : Nat) (s : Ch14GJEState n) (q : Nat) :
    Fin n -> Fin n -> Real :=
  (ch14ext_gjeFinalizedSourceTrace fp start s (q - start)).matrix

/-- Absolute-indexed RHS view of the finalized trace. -/
noncomputable def ch14ext_gjeFinalizedSourceTraceRhs {n : Nat}
    (fp : FPModel) (start : Nat) (s : Ch14GJEState n) (q : Nat) :
    Fin n -> Real :=
  (ch14ext_gjeFinalizedSourceTrace fp start s (q - start)).rhs

/-- Stage-matrix family read from the finalized execution. -/
noncomputable def ch14ext_gjeFinalizedSourceStages {n : Nat}
    (fp : FPModel) (s : Ch14GJEState n) :
    Fin n -> Fin n -> Fin n -> Real :=
  ch14ext_gjeSeqStages n (ch14ext_gjeFinalizedSourceTraceMatrix fp 1 s)

/-- Explicit reverse-product inverse of the finalized stage product. -/
noncomputable def ch14ext_gjeFinalizedSourceQ {n : Nat}
    (fp : FPModel) (s : Ch14GJEState n) : Fin n -> Fin n -> Real :=
  ch14ext_gjeConstructedQ n
    (ch14ext_gjeFinalizedSourceTraceMatrix fp 1 s) 1

/-- Absolute product used in the finalized trace's printed envelopes. -/
noncomputable def ch14ext_gjeFinalizedSourcePabs {n : Nat}
    (fp : FPModel) (s : Ch14GJEState n) : Fin n -> Fin n -> Real :=
  ch14ext_absCumProd n (ch14ext_gjeFinalizedSourceStages fp s) 1 (n - 1)

/-- The finalized trace's `|Q|`-weighted absolute stage product. -/
noncomputable def ch14ext_gjeFinalizedSourceXabs {n : Nat}
    (fp : FPModel) (s : Ch14GJEState n) : Fin n -> Fin n -> Real :=
  ch14ext_gjeXabs n (ch14ext_gjeFinalizedSourceStages fp s)
    (ch14ext_gjeFinalizedSourceQ fp s) 1 (n - 1)

theorem ch14ext_gjeFinalizedSourceTraceMatrix_rec {n : Nat}
    (fp : FPModel) (start : Nat) (s : Ch14GJEState n)
    (t : Nat) (ht : start + t < n) :
    ch14ext_gjeFinalizedSourceTraceMatrix fp start s (start + (t + 1)) =
      ch14ext_gjeFinalizedSourceStepMatrix fp
        (ch14ext_gjeFinalizedSourceTraceMatrix fp start s (start + t))
        ⟨start + t, ht⟩ := by
  simp [ch14ext_gjeFinalizedSourceTraceMatrix,
    ch14ext_gjeFinalizedSourceTrace, ch14ext_gjeFinalizedSourceStepState, ht]

theorem ch14ext_gjeFinalizedSourceTraceRhs_rec {n : Nat}
    (fp : FPModel) (start : Nat) (s : Ch14GJEState n)
    (t : Nat) (ht : start + t < n) :
    ch14ext_gjeFinalizedSourceTraceRhs fp start s (start + (t + 1)) =
      ch14ext_gjeSourceStepVec fp n
        (ch14ext_gjeFinalizedSourceTraceMatrix fp start s (start + t))
        ⟨start + t, ht⟩
        (ch14ext_gjeFinalizedSourceTraceRhs fp start s (start + t)) := by
  simp [ch14ext_gjeFinalizedSourceTraceRhs,
    ch14ext_gjeFinalizedSourceTraceMatrix,
    ch14ext_gjeFinalizedSourceTrace, ch14ext_gjeFinalizedSourceStepState, ht]

/-- Every finalized trace preserves the initial diagonal. -/
theorem ch14ext_gjeFinalizedSourceTrace_diag {n : Nat}
    (fp : FPModel) (start : Nat) (s : Ch14GJEState n) :
    forall t : Nat, forall i : Fin n,
      (ch14ext_gjeFinalizedSourceTrace fp start s t).matrix i i =
        s.matrix i i := by
  intro t
  induction t with
  | zero =>
      intro i
      rfl
  | succ t ih =>
      intro i
      rw [ch14ext_gjeFinalizedSourceTrace]
      split
      · simp only [ch14ext_gjeFinalizedSourceStepState]
        rw [ch14ext_gjeFinalizedSourceStepMatrix_diag]
        exact ih i
      · exact ih i

/-- Upper-triangular input remains upper triangular throughout the finalized
trace. -/
theorem ch14ext_gjeFinalizedSourceTrace_upper {n : Nat}
    (fp : FPModel) (start : Nat) (s : Ch14GJEState n)
    (hUpper : forall i j : Fin n, j.val < i.val -> s.matrix i j = 0) :
    forall t : Nat, forall i j : Fin n, j.val < i.val ->
      (ch14ext_gjeFinalizedSourceTrace fp start s t).matrix i j = 0 := by
  intro t
  induction t with
  | zero =>
      exact hUpper
  | succ t ih =>
      intro i j hji
      rw [ch14ext_gjeFinalizedSourceTrace]
      split
      · simp only [ch14ext_gjeFinalizedSourceStepState]
        exact ch14ext_gjeFinalizedSourceStepMatrix_upper fp _ _ ih i j hji
      · exact ih i j hji

/-- After `t` finalized stages beginning at column one, every strict-upper
entry in a processed column is structurally zero. -/
theorem ch14ext_gjeFinalizedSourceTrace_processed_zero {n : Nat}
    (fp : FPModel) (s : Ch14GJEState n) :
    forall t : Nat, forall i j : Fin n,
      i.val < j.val -> j.val < 1 + t ->
      (ch14ext_gjeFinalizedSourceTrace fp 1 s t).matrix i j = 0 := by
  intro t
  induction t with
  | zero =>
      intro i j hij hj
      omega
  | succ t ih =>
      intro i j hij hj
      rw [ch14ext_gjeFinalizedSourceTrace]
      split
      next hstage =>
        simp only [ch14ext_gjeFinalizedSourceStepState]
        by_cases hjold : j.val < 1 + t
        · rw [ch14ext_gjeFinalizedSourceStepMatrix_preserves_left fp _ _ i j hjold]
          exact ih i j hij hjold
        · have hjeq : j.val = 1 + t := by omega
          have hjfin : j = (⟨1 + t, hstage⟩ : Fin n) := Fin.ext hjeq
          subst j
          exact ch14ext_gjeFinalizedSourceStepMatrix_pivot_column fp _ _ i hij
      next hstage =>
        have hjold : j.val < 1 + t := by
          have hjlt : j.val < n := j.isLt
          omega
        exact ih i j hij hjold

/-- Diagonal matrix retained by the finalized second stage. -/
def ch14ext_gjeFinalDiagonal {n : Nat}
    (U : Fin n -> Fin n -> Real) : Fin n -> Fin n -> Real :=
  fun i j => if i = j then U i i else 0

/-- The finalized executor ends at the actual diagonal `D`; this is the
general, unnormalized operational endpoint preceding Higham's `D = I`
simplification. -/
theorem ch14ext_gjeFinalizedSourceTrace_final_diagonal {n : Nat}
    (fp : FPModel) (s : Ch14GJEState n) (hn : 1 <= n)
    (hUpper : forall i j : Fin n, j.val < i.val -> s.matrix i j = 0) :
    (ch14ext_gjeFinalizedSourceTrace fp 1 s (n - 1)).matrix =
      ch14ext_gjeFinalDiagonal s.matrix := by
  funext i j
  by_cases hij : i = j
  · subst j
    rw [ch14ext_gjeFinalizedSourceTrace_diag]
    simp [ch14ext_gjeFinalDiagonal]
  · by_cases hijlt : i.val < j.val
    · have hjdone : j.val < 1 + (n - 1) := by omega
      rw [ch14ext_gjeFinalizedSourceTrace_processed_zero fp s
        (n - 1) i j hijlt hjdone]
      simp [ch14ext_gjeFinalDiagonal, hij]
    · have hji : j.val < i.val := by
        have hne : Ne i.val j.val := by
          intro h
          exact hij (Fin.ext h)
        omega
      rw [ch14ext_gjeFinalizedSourceTrace_upper fp 1 s hUpper
        (n - 1) i j hji]
      simp [ch14ext_gjeFinalDiagonal, hij]

/-- **Operational finalization producer for Algorithm 14.4.**  Starting from
an upper-triangular matrix with unit diagonal, the recursively executed
finalized second stage produces the identity matrix.  No final-identity
certificate is assumed. -/
theorem ch14ext_gjeFinalizedSourceTrace_final_matrix {n : Nat}
    (fp : FPModel) (s : Ch14GJEState n) (hn : 1 <= n)
    (hUpper : forall i j : Fin n, j.val < i.val -> s.matrix i j = 0)
    (hDiag : forall i : Fin n, s.matrix i i = 1) :
    (ch14ext_gjeFinalizedSourceTrace fp 1 s (n - 1)).matrix = idMatrix n := by
  funext i j
  by_cases hij : i = j
  · subst j
    rw [ch14ext_gjeFinalizedSourceTrace_diag]
    simp [idMatrix, hDiag]
  · by_cases hijlt : i.val < j.val
    · have hjdone : j.val < 1 + (n - 1) := by omega
      rw [ch14ext_gjeFinalizedSourceTrace_processed_zero fp s
        (n - 1) i j hijlt hjdone]
      simp [idMatrix, hij]
    · have hji : j.val < i.val := by
        have hne : Ne i.val j.val := by
          intro h
          exact hij (Fin.ext h)
        omega
      rw [ch14ext_gjeFinalizedSourceTrace_upper fp 1 s hUpper
        (n - 1) i j hji]
      simp [idMatrix, hij]

/-- The finalized trace supplies the two local recurrence bounds consumed by
the source accumulation theorem.  Both bounds are derived from the executed
trace and the FP model; neither is a caller-provided error certificate. -/
theorem ch14ext_gjeFinalizedSourceTrace_recurrence_bounds_14_25b_14_26
    {n : Nat} (fp : FPModel) (s : Ch14GJEState n)
    (hidx : forall t : Nat, t < n - 1 -> 1 + t < n)
    (hUpper : forall i j : Fin n, j.val < i.val -> s.matrix i j = 0)
    (hpiv : forall t : Nat, (ht : t < n - 1) ->
      ch14ext_gjeFinalizedSourceTraceMatrix fp 1 s (1 + t)
        ⟨1 + t, hidx t ht⟩ ⟨1 + t, hidx t ht⟩ ≠ 0)
    (h3 : gammaValid fp 3) :
    let V := ch14ext_gjeFinalizedSourceTraceMatrix fp 1 s
    let xseq := ch14ext_gjeFinalizedSourceTraceRhs fp 1 s
    let Nhat := ch14ext_gjeSeqStages n V
    (forall t : Nat, (ht : t < n - 1) -> forall i j : Fin n,
      |V (1 + (t + 1)) i j -
          ∑ l : Fin n, Nhat ⟨1 + t, hidx t ht⟩ i l * V (1 + t) l j| <=
        gamma fp 3 *
          ∑ l : Fin n,
            |Nhat ⟨1 + t, hidx t ht⟩ i l| * |V (1 + t) l j|) /\
    (forall t : Nat, (ht : t < n - 1) -> forall i : Fin n,
      |xseq (1 + (t + 1)) i -
          ∑ l : Fin n, Nhat ⟨1 + t, hidx t ht⟩ i l * xseq (1 + t) l| <=
        gamma fp 3 *
          ∑ l : Fin n,
            |Nhat ⟨1 + t, hidx t ht⟩ i l| * |xseq (1 + t) l|) := by
  let V := ch14ext_gjeFinalizedSourceTraceMatrix fp 1 s
  let xseq := ch14ext_gjeFinalizedSourceTraceRhs fp 1 s
  let Nhat := ch14ext_gjeSeqStages n V
  dsimp only
  constructor
  · intro t ht i j
    have hUt : forall a b : Fin n, b.val < a.val -> V (1 + t) a b = 0 := by
      simpa [V, ch14ext_gjeFinalizedSourceTraceMatrix] using
        ch14ext_gjeFinalizedSourceTrace_upper fp 1 s hUpper t
    rw [ch14ext_gjeFinalizedSourceTraceMatrix_rec fp 1 s t (hidx t ht)]
    simpa [Nhat, ch14ext_gjeSeqStages, matMul, absMatrix] using
      ch14ext_gjeFinalizedSourceStepMatrix_local_14_25 fp (V (1 + t))
        ⟨1 + t, hidx t ht⟩ hUt (hpiv t ht) h3 i j
  · intro t ht i
    have hUt : forall a b : Fin n, b.val < a.val -> V (1 + t) a b = 0 := by
      simpa [V, ch14ext_gjeFinalizedSourceTraceMatrix] using
        ch14ext_gjeFinalizedSourceTrace_upper fp 1 s hUpper t
    have hlocal := ch14ext_gjeSource_local_rhs_14_26 fp (V (1 + t))
      ⟨1 + t, hidx t ht⟩ (xseq (1 + t)) hUt (hpiv t ht) h3
    rw [ch14ext_gjeFinalizedSourceTraceRhs_rec fp 1 s t (hidx t ht)]
    calc
      |ch14ext_gjeSourceStepVec fp n (V (1 + t))
            ⟨1 + t, hidx t ht⟩ (xseq (1 + t)) i -
          ∑ l : Fin n, Nhat ⟨1 + t, hidx t ht⟩ i l * xseq (1 + t) l| =
          |ch14ext_gjeSourceF fp n (V (1 + t))
            ⟨1 + t, hidx t ht⟩ (xseq (1 + t)) i| := by
        rw [hlocal.1 i]
        simp [Nhat, ch14ext_gjeSeqStages, matMulVec]
      _ <= gamma fp 3 *
          ∑ l : Fin n,
            |Nhat ⟨1 + t, hidx t ht⟩ i l| * |xseq (1 + t) l| := by
        simpa [Nhat, ch14ext_gjeSeqStages, matMulVec, absMatrix, absVec] using
          hlocal.2.1 i

/-- **Higham (14.29) for the structurally finalized Algorithm 14.4 trace.**
The final identity is produced by the executed trace from upper-triangular,
unit-diagonal input; it is not a theorem hypothesis. -/
theorem ch14ext_gjeFinalizedSourceTrace_stage2_forward_error_14_29
    {n : Nat} (fp : FPModel) (s : Ch14GJEState n)
    (x : Fin n -> Real) (hn : 1 <= n) (h3 : gammaValid fp 3)
    (hUpper : forall i j : Fin n, j.val < i.val -> s.matrix i j = 0)
    (hDiag : forall i : Fin n, s.matrix i i = 1)
    (hUx : forall i : Fin n, matMulVec n s.matrix x i = s.rhs i)
    (hpiv : forall t : Nat, (ht : t < n - 1) ->
      ch14ext_gjeFinalizedSourceTraceMatrix fp 1 s (1 + t)
        ⟨1 + t, by omega⟩ ⟨1 + t, by omega⟩ ≠ 0) :
    forall i : Fin n,
      |x i - ch14ext_gjeFinalizedSourceTraceRhs fp 1 s n i| <=
        gje_c₃ fp n *
          ch14ext_gjeForwardEnvelope n
            (ch14ext_gjeSeqStages n
              (ch14ext_gjeFinalizedSourceTraceMatrix fp 1 s))
            s.matrix x s.rhs 1 (n - 1) i := by
  let V := ch14ext_gjeFinalizedSourceTraceMatrix fp 1 s
  let xseq := ch14ext_gjeFinalizedSourceTraceRhs fp 1 s
  let Nhat := ch14ext_gjeSeqStages n V
  have hidx : forall t : Nat, t < n - 1 -> 1 + t < n := by omega
  have hpiv' : forall t : Nat, (ht : t < n - 1) ->
      V (1 + t) ⟨1 + t, hidx t ht⟩ ⟨1 + t, hidx t ht⟩ ≠ 0 := by
    intro t ht
    simpa [V] using hpiv t ht
  have hrec :=
    ch14ext_gjeFinalizedSourceTrace_recurrence_bounds_14_25b_14_26
      fp s hidx hUpper hpiv' h3
  have hsum : 1 + (n - 1) = n := by omega
  have hVfinal : V (1 + (n - 1)) = idMatrix n := by
    rw [hsum]
    simpa [V, ch14ext_gjeFinalizedSourceTraceMatrix] using
      ch14ext_gjeFinalizedSourceTrace_final_matrix fp s hn hUpper hDiag
  have hUx' : forall i : Fin n, matMulVec n (V 1) x i = xseq 1 i := by
    intro i
    simpa [V, xseq, ch14ext_gjeFinalizedSourceTraceMatrix,
      ch14ext_gjeFinalizedSourceTraceRhs,
      ch14ext_gjeFinalizedSourceTrace] using hUx i
  have hforward := ch14ext_gje_stage2_forward_error_of_accumulation_14_29
    fp n Nhat V xseq x 1 hn h3 hidx hVfinal hUx' hrec.1 hrec.2
  simpa [V, xseq, Nhat, hsum,
    ch14ext_gjeFinalizedSourceTraceMatrix,
    ch14ext_gjeFinalizedSourceTraceRhs,
    ch14ext_gjeFinalizedSourceTrace] using hforward

/-- **Higham (14.30a-c) on the finalized computed output.**  This is the
backward-error companion of the preceding forward bound.  The returned vector
and final identity are both constructed by the concrete trace. -/
theorem ch14ext_gjeFinalizedSourceTrace_stage2_backward_error_14_30abc
    {n : Nat} (fp : FPModel) (s : Ch14GJEState n)
    (hn : 1 <= n) (h3 : gammaValid fp 3)
    (hUpper : forall i j : Fin n, j.val < i.val -> s.matrix i j = 0)
    (hDiag : forall i : Fin n, s.matrix i i = 1)
    (hpiv : forall t : Nat, (ht : t < n - 1) ->
      ch14ext_gjeFinalizedSourceTraceMatrix fp 1 s (1 + t)
        ⟨1 + t, by omega⟩ ⟨1 + t, by omega⟩ ≠ 0) :
    exists DeltaU : Fin n -> Fin n -> Real,
      exists Deltay : Fin n -> Real,
        (forall i : Fin n,
          ∑ j : Fin n, (s.matrix i j + DeltaU i j) *
              ch14ext_gjeFinalizedSourceTraceRhs fp 1 s n j =
            s.rhs i + Deltay i) /\
        (forall i j : Fin n, |DeltaU i j| <= gje_c₃ fp n *
          ∑ k : Fin n,
            |ch14ext_gjeFinalizedSourceXabs fp s i k| * |s.matrix k j|) /\
        (forall i : Fin n, |Deltay i| <= gje_c₃ fp n *
          ∑ j : Fin n,
            |ch14ext_gjeFinalizedSourceXabs fp s i j| * |s.rhs j|) := by
  let V := ch14ext_gjeFinalizedSourceTraceMatrix fp 1 s
  let xseq := ch14ext_gjeFinalizedSourceTraceRhs fp 1 s
  let Nhat := ch14ext_gjeFinalizedSourceStages fp s
  let Q := ch14ext_gjeFinalizedSourceQ fp s
  let xhat : Fin n -> Real := ch14ext_gjeFinalizedSourceTraceRhs fp 1 s n
  have hidx : forall t : Nat, t < n - 1 -> 1 + t < n := by omega
  have hpiv' : forall t : Nat, (ht : t < n - 1) ->
      V (1 + t) ⟨1 + t, hidx t ht⟩ ⟨1 + t, hidx t ht⟩ ≠ 0 := by
    intro t ht
    simpa [V] using hpiv t ht
  have hrec :=
    ch14ext_gjeFinalizedSourceTrace_recurrence_bounds_14_25b_14_26
      fp s hidx hUpper hpiv' h3
  have hsum : 1 + (n - 1) = n := by omega
  have hVfinal : V (1 + (n - 1)) = idMatrix n := by
    rw [hsum]
    simpa [V, ch14ext_gjeFinalizedSourceTraceMatrix] using
      ch14ext_gjeFinalizedSourceTrace_final_matrix fp s hn hUpper hDiag
  have hxhat : forall i : Fin n, xhat i = xseq (1 + (n - 1)) i := by
    intro i
    rw [hsum]
  have hQP :
      matMul n Q
        (gje_cumulative_product n Nhat 1 (1 + (n - 1))) = idMatrix n := by
    simpa [Q, Nhat, ch14ext_gjeFinalizedSourceQ,
      ch14ext_gjeFinalizedSourceStages] using
      ch14ext_gjeConstructedQ_isLeftInverse n V 1 hidx
  obtain ⟨DeltaU, Deltay, hEq, hDeltaU, hDeltay⟩ :=
    ch14ext_gje_stage2_backward_error_of_accumulation n fp xhat Nhat V xseq Q 1
      hn h3 hidx hVfinal hxhat hQP hrec.1 hrec.2
  refine ⟨DeltaU, Deltay, ?_, ?_, ?_⟩
  · intro i
    simpa [V, xseq, xhat, ch14ext_gjeFinalizedSourceTraceMatrix,
      ch14ext_gjeFinalizedSourceTraceRhs,
      ch14ext_gjeFinalizedSourceTrace] using hEq i
  · intro i j
    simpa [V, Nhat, Q, ch14ext_gjeFinalizedSourceXabs,
      ch14ext_gjeFinalizedSourceStages, ch14ext_gjeFinalizedSourceQ,
      ch14ext_gjeFinalizedSourceTraceMatrix,
      ch14ext_gjeFinalizedSourceTrace] using hDeltaU i j
  · intro i
    simpa [V, xseq, Nhat, Q, ch14ext_gjeFinalizedSourceXabs,
      ch14ext_gjeFinalizedSourceStages, ch14ext_gjeFinalizedSourceQ,
      ch14ext_gjeFinalizedSourceTraceMatrix,
      ch14ext_gjeFinalizedSourceTraceRhs,
      ch14ext_gjeFinalizedSourceTrace] using hDeltay i

/-! ## The remaining finalization obstruction -/

/-- A legal `FPModel` whose multiplication always takes the extremal positive
relative error while addition, subtraction, division, and square root are
exact.  It is used to test whether finalization is actually forced by the
abstract model. -/
noncomputable def ch14ext_mulBiasedModel (u : Real) (hu : 0 <= u) : FPModel where
  u := u
  u_nonneg := hu
  fl_add := fun x y => x + y
  fl_sub := fun x y => x - y
  fl_mul := fun x y => (x * y) * (1 + u)
  fl_div := fun x y => x / y
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
    exact ⟨u, by simp [abs_of_nonneg hu], rfl⟩
  model_div := by
    intro x y _hy
    refine ⟨0, by simpa using hu, ?_⟩
    ring
  model_sqrt := by
    intro x _hx
    refine ⟨0, by simpa using hu, ?_⟩
    ring

/-- The counterexample model satisfies all gamma guards used by the
two-by-two Theorem-14.5 source trace whenever `3*u < 1`. -/
theorem ch14ext_mulBiasedModel_gammaValid_two_three
    (u : Real) (hu : 0 <= u) (hsmall : 3 * u < 1) :
    gammaValid (ch14ext_mulBiasedModel u hu) 2 ∧
      gammaValid (ch14ext_mulBiasedModel u hu) 3 := by
  constructor
  · unfold gammaValid
    dsimp [ch14ext_mulBiasedModel]
    nlinarith
  · simpa [gammaValid, ch14ext_mulBiasedModel] using hsmall

/-- A normalized two-by-two upper-triangular state. -/
def ch14ext_finalizationCounterMatrix : Fin 2 -> Fin 2 -> Real :=
  !![(1 : Real), 1; 0, 1]

def ch14ext_finalizationCounterState : Ch14GJEState 2 where
  matrix := ch14ext_finalizationCounterMatrix
  rhs := ![(0 : Real), 0]

/-- The sole second-stage pivot in the two-by-two counterexample is nonzero,
so the rounded source trace satisfies the operational pivot-success guard. -/
theorem ch14ext_finalizationCounter_pivot_nonzero
    (u : Real) (hu : 0 <= u) :
    forall t : Nat, (ht : t < 2 - 1) ->
      ch14ext_gjeSourceTraceMatrix (ch14ext_mulBiasedModel u hu) 1
          ch14ext_finalizationCounterState (1 + t)
          ⟨1 + t, by omega⟩ ⟨1 + t, by omega⟩ ≠ 0 := by
  intro t ht
  have ht0 : t = 0 := by omega
  subst t
  norm_num [ch14ext_gjeSourceTraceMatrix, ch14ext_gjeSourceTrace,
    ch14ext_finalizationCounterState, ch14ext_finalizationCounterMatrix]

/-- After the one rounded elimination step, the nominally eliminated entry is
`-u`.  The current executor computes the arithmetic update but does not perform
the structural zero assignment used implicitly by Higham's final `D = I`
normalization. -/
theorem ch14ext_finalizationCounter_entry
    (u : Real) (hu : 0 <= u) :
    ch14ext_gjeSourceTraceMatrix (ch14ext_mulBiasedModel u hu) 1
        ch14ext_finalizationCounterState 2 0 1 = -u := by
  simp [ch14ext_gjeSourceTraceMatrix, ch14ext_gjeSourceTrace,
    ch14ext_gjeSourceStepState, ch14ext_gjeSourceStepMatrix,
    ch14ext_gjeSourceActive, ch14ext_gjeStepMatrix,
    ch14ext_mulBiasedModel, ch14ext_finalizationCounterState,
    ch14ext_finalizationCounterMatrix]

/-- Successful nonzero pivots do not imply the `final_matrix = I` field of
`Ch14GJETheorem145SourceFamily` for the repository's current rounded executor.
Consequently that field cannot be manufactured as an Algorithm-14.4 producer
without changing the executor to model structural zeroing/final scaling (and
then reproving the local-error bridge for that execution). -/
theorem ch14ext_finalizationCounter_not_identity
    (u : Real) (hu : 0 < u) :
    ch14ext_gjeSourceTraceMatrix
        (ch14ext_mulBiasedModel u hu.le) 1
        ch14ext_finalizationCounterState 2 ≠ idMatrix 2 := by
  intro h
  have hentry := congrFun (congrFun h (0 : Fin 2)) (1 : Fin 2)
  rw [ch14ext_finalizationCounter_entry u hu.le] at hentry
  simp [idMatrix] at hentry
  linarith

/-- All local model-validity and pivot-success guards can hold while the
current rounded source trace still fails its assumed final-identity field. -/
theorem ch14ext_finalizationCounter_all_local_guards_but_not_identity
    (u : Real) (hu : 0 < u) (hsmall : 3 * u < 1) :
    gammaValid (ch14ext_mulBiasedModel u hu.le) 2 ∧
      gammaValid (ch14ext_mulBiasedModel u hu.le) 3 ∧
      (forall t : Nat, (ht : t < 2 - 1) ->
        ch14ext_gjeSourceTraceMatrix (ch14ext_mulBiasedModel u hu.le) 1
            ch14ext_finalizationCounterState (1 + t)
            ⟨1 + t, by omega⟩ ⟨1 + t, by omega⟩ ≠ 0) ∧
      ch14ext_gjeSourceTraceMatrix (ch14ext_mulBiasedModel u hu.le) 1
          ch14ext_finalizationCounterState 2 ≠ idMatrix 2 := by
  refine ⟨(ch14ext_mulBiasedModel_gammaValid_two_three u hu.le hsmall).1,
    (ch14ext_mulBiasedModel_gammaValid_two_three u hu.le hsmall).2,
    ch14ext_finalizationCounter_pivot_nonzero u hu.le,
    ch14ext_finalizationCounter_not_identity u hu⟩

end NumStability.Ch14Ext
