import NumStability.Algorithms.QR.Higham19Alg11CGSRounded
import NumStability.Algorithms.QR.GramSchmidtPolar

/-!
# Rounded modified Gram--Schmidt (Higham Algorithm 19.12)

Source: N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
SIAM 2002, Chapter 19, Algorithm 19.12, page 374.

This module supplies the literal floating-point MGS loop missing from the QR
infrastructure.  At outer step `k` it computes, in the printed order,

* `r_kk = fl_norm2(v_k)`;
* `q_k i = fl_div (v_k i) r_kk`;
* `r_kj = fl_dotProduct(q_k,v_j)` for `k < j`;
* `v_j i = fl_sub (v_j i) (fl_mul r_kj (q_k i))`.

The output is therefore an actual `FPModel` execution of Algorithm 19.12, not
the padded-Householder construction used elsewhere as a QR surrogate.  The
module proves the complete local rounded-state contract, telescopes those
local fields into a product-residual bound, and combines it with an exact
right-Gram polar repair.  The companion local-Gram compression module isolates
the remaining printed `O(u)` Gram-defect coefficient.
-/

namespace NumStability

open scoped BigOperators

noncomputable section

/-! ## The literal rounded loop -/

/-- Rounded diagonal norm at one MGS stage. -/
def flMGSColumnNorm {m n : Nat} (fp : FPModel)
    (V : Fin n -> Fin m -> Real) (k : Fin n) : Real :=
  fl_norm2 fp m (V k)

/-- Rounded componentwise normalization of the active MGS column. -/
def flMGSNormalizedColumn {m n : Nat} (fp : FPModel)
    (V : Fin n -> Fin m -> Real) (k : Fin n) : Fin m -> Real :=
  fun i => fp.fl_div (V k i) (flMGSColumnNorm fp V k)

/-- Rounded MGS projection coefficient `fl(q_k^T v_j)`. -/
def flMGSProjection {m n : Nat} (fp : FPModel)
    (V : Fin n -> Fin m -> Real) (k j : Fin n) : Real :=
  fl_dotProduct fp m (flMGSNormalizedColumn fp V k) (V j)

/-- One literal rounded MGS outer step.  Only columns strictly after `k` are
updated; each component uses a rounded multiply followed by a rounded
subtraction, in the order printed in Algorithm 19.12. -/
def flMGSStep {m n : Nat} (fp : FPModel)
    (V : Fin n -> Fin m -> Real) (k : Fin n) :
    Fin n -> Fin m -> Real :=
  let qk := flMGSNormalizedColumn fp V k
  fun j i =>
    if _h : k < j then
      fp.fl_sub (V j i) (fp.fl_mul (flMGSProjection fp V k j) (qk i))
    else
      V j i

/-- Rounded MGS stage vectors.  Stage `t` is the stored matrix after outer
steps `0, ..., t-1` that exist for the `n`-column input. -/
def flMGSVectors {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) : Nat -> Fin n -> Fin m -> Real
  | 0 => fun j => gsColumn A j
  | t + 1 =>
      if ht : t < n then
        flMGSStep fp (flMGSVectors fp A t) (Fin.mk t ht)
      else
        flMGSVectors fp A t

/-- Computed `Q-hat` of the literal rounded MGS loop. -/
def fl_modifiedGramSchmidtQ {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) : Fin m -> Fin n -> Real :=
  fun i k => flMGSNormalizedColumn fp (flMGSVectors fp A k.val) k i

/-- Computed `R-hat` of the literal rounded MGS loop.  Below-diagonal entries
are exact zeros, the diagonal contains rounded norms, and the strict upper
part contains the rounded inner products used by the updates. -/
def fl_modifiedGramSchmidtR {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) : Fin n -> Fin n -> Real :=
  fun k j =>
    if _hle : k.val <= j.val then
      if k = j then
        flMGSColumnNorm fp (flMGSVectors fp A k.val) k
      else
        flMGSProjection fp (flMGSVectors fp A k.val) k j
    else
      0

/-- The literal rounded Algorithm 19.12 output packaged as `(Q-hat,R-hat)`. -/
def fl_modifiedGramSchmidt {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) :
    (Fin m -> Fin n -> Real) × (Fin n -> Fin n -> Real) :=
  (fl_modifiedGramSchmidtQ fp A, fl_modifiedGramSchmidtR fp A)

/-! ## Exact structural identities of the computed loop -/

/-- A rounded MGS step updates a later column by its printed rounded
projection-removal operations. -/
theorem flMGSStep_eq_update_of_lt {m n : Nat} (fp : FPModel)
    (V : Fin n -> Fin m -> Real) {k j : Fin n} (hkj : k < j) :
    flMGSStep fp V k j = fun i =>
      fp.fl_sub (V j i)
        (fp.fl_mul (flMGSProjection fp V k j)
          (flMGSNormalizedColumn fp V k i)) := by
  funext i
  simp [flMGSStep, hkj]

/-- A rounded MGS step leaves non-later columns unchanged. -/
theorem flMGSStep_eq_self_of_not_lt {m n : Nat} (fp : FPModel)
    (V : Fin n -> Fin m -> Real) {k j : Fin n} (hkj : Not (k < j)) :
    flMGSStep fp V k j = V j := by
  funext i
  simp [flMGSStep, hkj]

/-- Successor equation for the rounded stage recursion. -/
theorem flMGSVectors_succ_eq_step {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) {t : Nat} (ht : t < n) :
    flMGSVectors fp A (t + 1) =
      flMGSStep fp (flMGSVectors fp A t) (Fin.mk t ht) := by
  simp [flMGSVectors, ht]

/-- Fin-indexed successor equation for the rounded stage recursion. -/
theorem flMGSVectors_succ_eq_step_fin {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) (k : Fin n) :
    flMGSVectors fp A (k.val + 1) =
      flMGSStep fp (flMGSVectors fp A k.val) k := by
  simpa using flMGSVectors_succ_eq_step fp A k.isLt

/-- A later stored column at stage `k+1` is the literal rounded update. -/
theorem flMGSVectors_succ_later {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) {k j : Fin n} (hkj : k < j) :
    flMGSVectors fp A (k.val + 1) j = fun i =>
      fp.fl_sub (flMGSVectors fp A k.val j i)
        (fp.fl_mul
          (flMGSProjection fp (flMGSVectors fp A k.val) k j)
          (flMGSNormalizedColumn fp (flMGSVectors fp A k.val) k i)) := by
  rw [flMGSVectors_succ_eq_step_fin]
  exact flMGSStep_eq_update_of_lt fp _ hkj

/-- The computed `Q-hat` column is the rounded normalization used at its
corresponding stage. -/
theorem fl_modifiedGramSchmidtQ_col {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) (k : Fin n) :
    gsColumn (fl_modifiedGramSchmidtQ fp A) k =
      flMGSNormalizedColumn fp (flMGSVectors fp A k.val) k := by
  rfl

/-- Diagonal entries of computed `R-hat` are the rounded stage norms. -/
theorem fl_modifiedGramSchmidtR_diag {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) (k : Fin n) :
    fl_modifiedGramSchmidtR fp A k k =
      flMGSColumnNorm fp (flMGSVectors fp A k.val) k := by
  simp [fl_modifiedGramSchmidtR]

/-- Strict-upper entries of computed `R-hat` are exactly the rounded
projection coefficients used by the stored-column update. -/
theorem fl_modifiedGramSchmidtR_strict_upper {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) {k j : Fin n} (hkj : k.val < j.val) :
    fl_modifiedGramSchmidtR fp A k j =
      flMGSProjection fp (flMGSVectors fp A k.val) k j := by
  have hle : k.val <= j.val := Nat.le_of_lt hkj
  have hne : k ≠ j := by
    intro h
    subst h
    exact Nat.lt_irrefl _ hkj
  simp [fl_modifiedGramSchmidtR, hle, hne]

/-- Below-diagonal entries of computed `R-hat` are exact zeros. -/
theorem fl_modifiedGramSchmidtR_lower_zero {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) {i j : Fin n} (hji : j.val < i.val) :
    fl_modifiedGramSchmidtR fp A i j = 0 := by
  simp [fl_modifiedGramSchmidtR, Nat.not_le_of_gt hji]

/-- Exact upper-trapezoidal shape of the `R-hat` returned by the literal
rounded MGS loop. -/
theorem fl_modifiedGramSchmidtR_upperTrapezoidal {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) :
    IsUpperTrapezoidal n n (fl_modifiedGramSchmidtR fp A) := by
  intro i j hji
  exact fl_modifiedGramSchmidtR_lower_zero fp A hji

/-! ## Local error of the printed MGS update -/

/-- Explicit componentwise error budget for one rounded MGS update.  The
terms respectively account for the length-`m` dot product, the rounded
multiplication, and the final rounded subtraction. -/
def flMGSUpdateLocalBudget {m : Nat} (fp : FPModel)
    (q v : Fin m -> Real) (i : Fin m) : Real :=
  let S := Finset.univ.sum fun r : Fin m => |q r| * |v r|
  let Edot := gamma fp m * S
  let Emul := |q i| * Edot * (1 + fp.u) + |q i| * S * fp.u
  Emul + (|v i| + |gsDot q v * q i| + Emul) * fp.u

/-- The rounded multiply after the rounded MGS dot product has the explicit
componentwise error used in `flMGSUpdateLocalBudget`. -/
theorem flMGSProjection_mul_error_bound {m : Nat} (fp : FPModel)
    (q v : Fin m -> Real) (i : Fin m) (hm : gammaValid fp m) :
    |fp.fl_mul (fl_dotProduct fp m q v) (q i) - gsDot q v * q i| <=
      |q i| * (gamma fp m *
        (Finset.univ.sum fun r : Fin m => |q r| * |v r|)) * (1 + fp.u) +
      |q i| * (Finset.univ.sum fun r : Fin m => |q r| * |v r|) * fp.u := by
  let d : Real := gsDot q v
  let t : Real := fl_dotProduct fp m q v
  let S : Real := Finset.univ.sum fun r : Fin m => |q r| * |v r|
  let E : Real := gamma fp m * S
  have hgamma : 0 <= gamma fp m := gamma_nonneg fp hm
  have hS : 0 <= S :=
    Finset.sum_nonneg fun r _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hE : 0 <= E := mul_nonneg hgamma hS
  have hdot : |t - d| <= E := by
    simpa [t, d, E, S, gsDot, abs_mul] using
      dotProduct_error_bound fp m q v hm
  have hd : |d| <= S := by
    calc
      |d| = |Finset.univ.sum fun r : Fin m => q r * v r| := rfl
      _ <= Finset.univ.sum fun r : Fin m => |q r * v r| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = S := by simp [S, abs_mul]
  obtain ⟨delta, hdelta, hmul⟩ := fp.model_mul t (q i)
  have hone : |1 + delta| <= 1 + fp.u := by
    calc
      |1 + delta| <= |(1 : Real)| + |delta| := abs_add_le _ _
      _ <= 1 + fp.u := by simpa using add_le_add_left hdelta 1
  have hrewrite :
      fp.fl_mul t (q i) - d * q i =
        q i * (t - d) * (1 + delta) + d * q i * delta := by
    rw [hmul]
    ring
  rw [hrewrite]
  calc
    |q i * (t - d) * (1 + delta) + d * q i * delta| <=
        |q i * (t - d) * (1 + delta)| + |d * q i * delta| :=
      abs_add_le _ _
    _ = |q i| * |t - d| * |1 + delta| + |d| * |q i| * |delta| := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul]
    _ <= |q i| * E * (1 + fp.u) + S * |q i| * fp.u := by
      exact add_le_add
        (mul_le_mul
          (mul_le_mul_of_nonneg_left hdot (abs_nonneg (q i))) hone
          (abs_nonneg (1 + delta))
          (mul_nonneg (abs_nonneg (q i)) hE))
        (mul_le_mul
          (mul_le_mul_of_nonneg_right hd (abs_nonneg (q i))) hdelta
          (abs_nonneg delta) (mul_nonneg hS (abs_nonneg (q i))))
    _ = |q i| * (gamma fp m *
          (Finset.univ.sum fun r : Fin m => |q r| * |v r|)) *
          (1 + fp.u) +
        |q i| * (Finset.univ.sum fun r : Fin m => |q r| * |v r|) * fp.u := by
      simp only [E, S]
      ring

/-- One printed rounded MGS update is close, componentwise, to exact
projection removal applied to the same stored vectors. -/
theorem flMGSUpdate_entry_error_bound {m : Nat} (fp : FPModel)
    (q v : Fin m -> Real) (i : Fin m) (hm : gammaValid fp m) :
    |fp.fl_sub (v i)
          (fp.fl_mul (fl_dotProduct fp m q v) (q i)) -
        gsProjectAway v q i| <=
      flMGSUpdateLocalBudget fp q v i := by
  let d : Real := gsDot q v
  let what : Real := fp.fl_mul (fl_dotProduct fp m q v) (q i)
  let w : Real := d * q i
  let S : Real := Finset.univ.sum fun r : Fin m => |q r| * |v r|
  let Edot : Real := gamma fp m * S
  let Emul : Real := |q i| * Edot * (1 + fp.u) + |q i| * S * fp.u
  have hgamma : 0 <= gamma fp m := gamma_nonneg fp hm
  have hS : 0 <= S :=
    Finset.sum_nonneg fun r _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hEdot : 0 <= Edot := mul_nonneg hgamma hS
  have hEmul : 0 <= Emul := by
    exact add_nonneg
      (mul_nonneg (mul_nonneg (abs_nonneg (q i)) hEdot)
        (add_nonneg zero_le_one fp.u_nonneg))
      (mul_nonneg (mul_nonneg (abs_nonneg (q i)) hS) fp.u_nonneg)
  have hwhat : |what - w| <= Emul := by
    simpa [what, w, d, Emul, Edot, S] using
      flMGSProjection_mul_error_bound fp q v i hm
  have hwhatAbs : |what| <= |w| + Emul := by
    calc
      |what| = |w + (what - w)| := by ring_nf
      _ <= |w| + |what - w| := abs_add_le _ _
      _ <= |w| + Emul := add_le_add (le_refl _) hwhat
  have hdiff : |v i - what| <= |v i| + |w| + Emul := by
    calc
      |v i - what| <= |v i| + |what| := abs_sub _ _
      _ <= |v i| + (|w| + Emul) := add_le_add (le_refl _) hwhatAbs
      _ = |v i| + |w| + Emul := by ring
  have hbudgetNonneg : 0 <= |v i| + |w| + Emul :=
    add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) hEmul
  obtain ⟨delta, hdelta, hsub⟩ := fp.model_sub (v i) what
  have hrewrite :
      fp.fl_sub (v i) what - (v i - w) =
        -(what - w) + (v i - what) * delta := by
    rw [hsub]
    ring
  change |fp.fl_sub (v i) what - (v i - w)| <=
    flMGSUpdateLocalBudget fp q v i
  rw [hrewrite]
  calc
    |-(what - w) + (v i - what) * delta| <=
        |-(what - w)| + |(v i - what) * delta| := abs_add_le _ _
    _ = |what - w| + |v i - what| * |delta| := by
      rw [abs_neg, abs_mul]
    _ <= Emul + (|v i| + |w| + Emul) * fp.u :=
      add_le_add hwhat
        (mul_le_mul hdiff hdelta (abs_nonneg delta) hbudgetNonneg)
    _ = flMGSUpdateLocalBudget fp q v i := by
      simp [flMGSUpdateLocalBudget, Emul, Edot, S, w, d]

/-! ## Honest rounded-state contract -/

/-- Floating-point analogue of `ModifiedGramSchmidtState` for the literal
rounded Algorithm 19.12 loop.  It records every computed channel and the local
error of every later-column update. -/
structure ModifiedGramSchmidtRoundedState {m n : Nat}
    (fp : FPModel) (A Q : Fin m -> Fin n -> Real)
    (R : Fin n -> Fin n -> Real)
    (V : Nat -> Fin n -> Fin m -> Real) : Prop where
  /-- Stage zero is the source matrix, column by column. -/
  initial : forall (j : Fin n) (i : Fin m), V 0 j i = A i j
  /-- The computed `R-hat` is exactly upper trapezoidal. -/
  upper : IsUpperTrapezoidal n n R
  /-- The diagonal is a rounded norm of the active stored column. -/
  diagonal : forall k : Fin n,
    Exists fun theta : Real =>
      |theta| <= gamma fp (m + 1) /\
      R k k = gsColumnNorm2 (V k.val k) * (1 + theta)
  /-- Each computed `Q-hat` entry is the rounded quotient used by the loop. -/
  normalized : forall (i : Fin m) (k : Fin n),
    Exists fun delta : Real =>
      |delta| <= fp.u /\
      gsColumn Q k i = gsNormalize (V k.val k) (R k k) i * (1 + delta)
  /-- Strict-upper entries are rounded inner products against the current
  stored later column. -/
  projection : forall k j : Fin n, k.val < j.val ->
    |R k j - gsDot (gsColumn Q k) (V k.val j)| <=
      gamma fp m *
        (Finset.univ.sum fun r : Fin m => |Q r k| * |V k.val j r|)
  /-- Each stored later-column update has the explicit local error budget. -/
  update : forall (k j : Fin n), k < j -> forall i : Fin m,
    |V (k.val + 1) j i -
        gsProjectAway (V k.val j) (gsColumn Q k) i| <=
      flMGSUpdateLocalBudget fp (gsColumn Q k) (V k.val j) i

/-- Exact product residual of the rounded factors.  This is the accumulated
Algorithm 19.12 channel `Qhat * Rhat - A`; it is data, not a hypothesis. -/
noncomputable def mgsRoundedProductResidual {m n : Nat}
    (A Qhat : Fin m -> Fin n -> Real)
    (Rhat : Fin n -> Fin n -> Real) : Fin m -> Fin n -> Real :=
  fun i j => matMulRect m n n Qhat Rhat i j - A i j

/-- Primitive one-step contribution to the rounded product residual.  The
first term is the local stored-column update error and the second is the
rounded projection-coefficient error transported by the computed `q_k`. -/
noncomputable def mgsRoundedStepReconstructionBudget {m n : Nat}
    (fp : FPModel) (Q : Fin m -> Fin n -> Real)
    (V : Nat -> Fin n -> Fin m -> Real)
    (k j : Fin n) (i : Fin m) : Real :=
  flMGSUpdateLocalBudget fp (gsColumn Q k) (V k.val j) i +
    |Q i k| *
      (gamma fp m *
        (Finset.univ.sum fun r : Fin m => |Q r k| * |V k.val j r|))

/-- A rounded MGS state controls the exact defect of one reconstruction step
`v_j^(k) = v_j^(k+1) + q_k r_kj`. -/
theorem ModifiedGramSchmidtRoundedState.step_reconstruction_error
    {m n : Nat} {fp : FPModel}
    {A Q : Fin m -> Fin n -> Real}
    {R : Fin n -> Fin n -> Real}
    {V : Nat -> Fin n -> Fin m -> Real}
    (hstate : ModifiedGramSchmidtRoundedState fp A Q R V)
    (k j : Fin n) (hkj : k < j) (i : Fin m) :
    |(V (k.val + 1) j i + Q i k * R k j) - V k.val j i| <=
      mgsRoundedStepReconstructionBudget fp Q V k j i := by
  have hupdate := hstate.update k j hkj i
  have hprojection := hstate.projection k j hkj
  have hsplit :
      (V (k.val + 1) j i + Q i k * R k j) - V k.val j i =
        (V (k.val + 1) j i -
          gsProjectAway (V k.val j) (gsColumn Q k) i) +
        Q i k * (R k j - gsDot (gsColumn Q k) (V k.val j)) := by
    simp only [gsProjectAway, gsColumn]
    ring
  rw [hsplit]
  calc
    |(V (k.val + 1) j i -
          gsProjectAway (V k.val j) (gsColumn Q k) i) +
        Q i k * (R k j - gsDot (gsColumn Q k) (V k.val j))| <=
        |V (k.val + 1) j i -
          gsProjectAway (V k.val j) (gsColumn Q k) i| +
        |Q i k * (R k j - gsDot (gsColumn Q k) (V k.val j))| :=
      abs_add_le _ _
    _ = |V (k.val + 1) j i -
          gsProjectAway (V k.val j) (gsColumn Q k) i| +
        |Q i k| * |R k j - gsDot (gsColumn Q k) (V k.val j)| := by
      rw [abs_mul]
    _ <= flMGSUpdateLocalBudget fp (gsColumn Q k) (V k.val j) i +
        |Q i k| *
          (gamma fp m *
            (Finset.univ.sum fun r : Fin m => |Q r k| * |V k.val j r|)) :=
      add_le_add hupdate
        (mul_le_mul_of_nonneg_left hprojection (abs_nonneg (Q i k)))
    _ = mgsRoundedStepReconstructionBudget fp Q V k j i := rfl

/-- An upper-triangular right factor makes a product column a prefix sum plus
its diagonal term. -/
theorem matMulRect_upper_column_eq_prefix_diag {m n : Nat}
    (Q : Fin m -> Fin n -> Real) (R : Fin n -> Fin n -> Real)
    (hupper : IsUpperTrapezoidal n n R) (i : Fin m) (j : Fin n) :
    matMulRect m n n Q R i j =
      (Finset.univ.sum fun k : Fin j.val =>
        Q i (Fin.castLT k (lt_trans k.isLt j.isLt)) *
          R (Fin.castLT k (lt_trans k.isLt j.isLt)) j) +
      Q i j * R j j := by
  let f : Nat -> Real := fun k =>
    if hk : k < n then Q i (Fin.mk k hk) * R (Fin.mk k hk) j else 0
  have hall :
      matMulRect m n n Q R i j =
        Finset.sum (Finset.range n) f := by
    unfold matMulRect
    calc
      (Finset.univ.sum fun k : Fin n => Q i k * R k j) =
          Finset.univ.sum fun k : Fin n => f k.val := by
        apply Finset.sum_congr rfl
        intro k _hk
        simp [f, k.isLt]
      _ = Finset.sum (Finset.range n) f :=
        Fin.sum_univ_eq_sum_range f n
  have hprefix :
      (Finset.univ.sum fun k : Fin j.val =>
        Q i (Fin.castLT k (lt_trans k.isLt j.isLt)) *
          R (Fin.castLT k (lt_trans k.isLt j.isLt)) j) =
        Finset.sum (Finset.range j.val) f := by
    calc
      (Finset.univ.sum fun k : Fin j.val =>
          Q i (Fin.castLT k (lt_trans k.isLt j.isLt)) *
            R (Fin.castLT k (lt_trans k.isLt j.isLt)) j) =
          Finset.univ.sum fun k : Fin j.val => f k.val := by
        apply Finset.sum_congr rfl
        intro k _hk
        have hkn : k.val < n := lt_trans k.isLt j.isLt
        simp [f, hkn, Fin.castLT]
      _ = Finset.sum (Finset.range j.val) f :=
        Fin.sum_univ_eq_sum_range f j.val
  have hsubset : Finset.range (j.val + 1) ⊆ Finset.range n := by
    intro k hk
    exact Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hk) (Nat.succ_le_iff.mpr j.isLt))
  have htruncate :
      Finset.sum (Finset.range n) f =
        Finset.sum (Finset.range (j.val + 1)) f := by
    symm
    apply Finset.sum_subset hsubset
    intro k hkn hnot
    have hge : j.val + 1 <= k := by
      exact Nat.le_of_not_gt (fun hk => hnot (Finset.mem_range.mpr hk))
    have hkn' : k < n := Finset.mem_range.mp hkn
    have hjk : j.val < k := lt_of_lt_of_le (Nat.lt_succ_self j.val) hge
    have hzero : R (Fin.mk k hkn') j = 0 := hupper (Fin.mk k hkn') j hjk
    simp [hkn', hzero]
  rw [hall, htruncate, Finset.sum_range_succ, <- hprefix]
  have hjn : j.val < n := j.isLt
  simp [hjn]

/-- The diagonal reconstruction defect comes only from the rounded division
recorded by `RoundedState.normalized`. -/
theorem ModifiedGramSchmidtRoundedState.diagonal_reconstruction_error
    {m n : Nat} {fp : FPModel}
    {A Q : Fin m -> Fin n -> Real}
    {R : Fin n -> Fin n -> Real}
    {V : Nat -> Fin n -> Fin m -> Real}
    (hstate : ModifiedGramSchmidtRoundedState fp A Q R V)
    (hdiag : forall k : Fin n, Ne (R k k) 0)
    (j : Fin n) (i : Fin m) :
    |Q i j * R j j - V j.val j i| <= |V j.val j i| * fp.u := by
  obtain ⟨delta, hdelta, hq⟩ := hstate.normalized i j
  have hq' :
      Q i j = (V j.val j i / R j j) * (1 + delta) := by
    simpa [gsColumn, gsNormalize] using hq
  have heq : Q i j * R j j - V j.val j i = V j.val j i * delta := by
    rw [hq']
    field_simp [hdiag j]
    ring
  rw [heq, abs_mul]
  exact mul_le_mul_of_nonneg_left hdelta (abs_nonneg (V j.val j i))

/-- Exact telescoping identity for the stored later-column reconstruction
defects preceding column `j`. -/
theorem mgsRounded_step_defects_telescope {m n : Nat}
    (Q : Fin m -> Fin n -> Real) (R : Fin n -> Fin n -> Real)
    (V : Nat -> Fin n -> Fin m -> Real) (j : Fin n) (i : Fin m) :
    (Finset.univ.sum fun k : Fin j.val =>
      let kk : Fin n := Fin.castLT k (lt_trans k.isLt j.isLt)
      (V (kk.val + 1) j i + Q i kk * R kk j) - V kk.val j i) =
      (V j.val j i - V 0 j i) +
        Finset.univ.sum (fun k : Fin j.val =>
          let kk : Fin n := Fin.castLT k (lt_trans k.isLt j.isLt)
          Q i kk * R kk j) := by
  let d : Nat -> Real := fun k => V (k + 1) j i - V k j i
  have htel : Finset.sum (Finset.range j.val) d = V j.val j i - V 0 j i := by
    simpa [d] using Finset.sum_range_sub (fun k => V k j i) j.val
  calc
    (Finset.univ.sum fun k : Fin j.val =>
        let kk : Fin n := Fin.castLT k (lt_trans k.isLt j.isLt)
        (V (kk.val + 1) j i + Q i kk * R kk j) - V kk.val j i) =
        (Finset.univ.sum fun k : Fin j.val =>
          V (k.val + 1) j i - V k.val j i) +
        Finset.univ.sum (fun k : Fin j.val =>
          let kk : Fin n := Fin.castLT k (lt_trans k.isLt j.isLt)
          Q i kk * R kk j) := by
      rw [<- Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _hk
      simp only [Fin.castLT]
      ring
    _ = (V j.val j i - V 0 j i) +
        Finset.univ.sum (fun k : Fin j.val =>
          let kk : Fin n := Fin.castLT k (lt_trans k.isLt j.isLt)
          Q i kk * R kk j) := by
      congr 1
      calc
        (Finset.univ.sum fun k : Fin j.val =>
            V (k.val + 1) j i - V k.val j i) =
            Finset.sum (Finset.range j.val) d := by
          exact Fin.sum_univ_eq_sum_range d j.val
        _ = V j.val j i - V 0 j i := htel

/-- Primitive entrywise accumulation bound obtained solely from the local
rounded Algorithm 19.12 fields. -/
noncomputable def mgsRoundedProductEntryBudget {m n : Nat}
    (fp : FPModel) (Q : Fin m -> Fin n -> Real)
    (V : Nat -> Fin n -> Fin m -> Real)
    (j : Fin n) (i : Fin m) : Real :=
  |V j.val j i| * fp.u +
    Finset.univ.sum (fun k : Fin j.val =>
      let kk : Fin n := Fin.castLT k (lt_trans k.isLt j.isLt)
      mgsRoundedStepReconstructionBudget fp Q V kk j i)

/-- The exact product residual is the diagonal defect plus the telescoped
stored-column reconstruction defects. -/
theorem ModifiedGramSchmidtRoundedState.product_residual_decomposition
    {m n : Nat} {fp : FPModel}
    {A Q : Fin m -> Fin n -> Real}
    {R : Fin n -> Fin n -> Real}
    {V : Nat -> Fin n -> Fin m -> Real}
    (hstate : ModifiedGramSchmidtRoundedState fp A Q R V)
    (j : Fin n) (i : Fin m) :
    mgsRoundedProductResidual A Q R i j =
      (Q i j * R j j - V j.val j i) +
        Finset.univ.sum (fun k : Fin j.val =>
          let kk : Fin n := Fin.castLT k (lt_trans k.isLt j.isLt)
          (V (kk.val + 1) j i + Q i kk * R kk j) - V kk.val j i) := by
  have hprod := matMulRect_upper_column_eq_prefix_diag
    Q R hstate.upper i j
  have htel := mgsRounded_step_defects_telescope Q R V j i
  rw [mgsRoundedProductResidual, hprod, htel, hstate.initial j i]
  ring

/-- Literal local-to-global accumulation theorem for the rounded MGS product
residual.  Its right side contains only source/model data, gamma factors, and
the stored Algorithm 19.12 stages. -/
theorem ModifiedGramSchmidtRoundedState.product_residual_entry_bound
    {m n : Nat} {fp : FPModel}
    {A Q : Fin m -> Fin n -> Real}
    {R : Fin n -> Fin n -> Real}
    {V : Nat -> Fin n -> Fin m -> Real}
    (hstate : ModifiedGramSchmidtRoundedState fp A Q R V)
    (hdiag : forall k : Fin n, Ne (R k k) 0)
    (j : Fin n) (i : Fin m) :
    |mgsRoundedProductResidual A Q R i j| <=
      mgsRoundedProductEntryBudget fp Q V j i := by
  rw [hstate.product_residual_decomposition j i]
  calc
    |(Q i j * R j j - V j.val j i) +
        Finset.univ.sum (fun k : Fin j.val =>
          let kk : Fin n := Fin.castLT k (lt_trans k.isLt j.isLt)
          (V (kk.val + 1) j i + Q i kk * R kk j) - V kk.val j i)| <=
        |Q i j * R j j - V j.val j i| +
          |Finset.univ.sum (fun k : Fin j.val =>
            let kk : Fin n := Fin.castLT k (lt_trans k.isLt j.isLt)
            (V (kk.val + 1) j i + Q i kk * R kk j) - V kk.val j i)| :=
      abs_add_le _ _
    _ <= |Q i j * R j j - V j.val j i| +
        Finset.univ.sum (fun k : Fin j.val =>
          |(V (k.val + 1) j i +
              Q i (Fin.castLT k (lt_trans k.isLt j.isLt)) *
                R (Fin.castLT k (lt_trans k.isLt j.isLt)) j) -
            V k.val j i|) := by
      exact add_le_add le_rfl
        (Finset.abs_sum_le_sum_abs
          (fun k : Fin j.val =>
            let kk : Fin n := Fin.castLT k (lt_trans k.isLt j.isLt)
            (V (kk.val + 1) j i + Q i kk * R kk j) - V kk.val j i)
          Finset.univ)
    _ <= |V j.val j i| * fp.u +
        Finset.univ.sum (fun k : Fin j.val =>
          mgsRoundedStepReconstructionBudget fp Q V
            (Fin.castLT k (lt_trans k.isLt j.isLt)) j i) := by
      exact add_le_add
        (hstate.diagonal_reconstruction_error hdiag j i)
        (Finset.sum_le_sum fun k _hk =>
          hstate.step_reconstruction_error
            (Fin.castLT k (lt_trans k.isLt j.isLt)) j k.isLt i)
    _ = mgsRoundedProductEntryBudget fp Q V j i := rfl

/-- Column-norm form of the literal product-residual accumulation theorem. -/
theorem ModifiedGramSchmidtRoundedState.product_residual_column_bound
    {m n : Nat} {fp : FPModel}
    {A Q : Fin m -> Fin n -> Real}
    {R : Fin n -> Fin n -> Real}
    {V : Nat -> Fin n -> Fin m -> Real}
    (hstate : ModifiedGramSchmidtRoundedState fp A Q R V)
    (hdiag : forall k : Fin n, Ne (R k k) 0)
    (j : Fin n) :
    columnFrob (mgsRoundedProductResidual A Q R) j <=
      vecNorm2 (mgsRoundedProductEntryBudget fp Q V j) := by
  rw [columnFrob_eq_vecNorm2]
  exact vecNorm2_le_of_abs_le _ _
    (fun i => hstate.product_residual_entry_bound hdiag j i)

/-- The precise global interface consumed when using MGS as a least-squares
factorization.  It is the
columnwise `R`-factor repair channel of Higham Theorem 19.13: the computed
`R-hat` must also be the exact triangular factor of a nearby matrix with an
orthonormal factor.

This interface deliberately omits the residual and computed-`Q`
orthogonality channels of Theorem 19.13, because the Chapter 20 Problem 20.5
transfer does not use them.  The declarations below construct this interface
from `ModifiedGramSchmidtRoundedState` by local accumulation and right-Gram
polar repair. -/
structure ModifiedGramSchmidtGlobalRepair (m n : Nat)
    (A : Fin m -> Fin n -> Real) (Rhat : Fin n -> Fin n -> Real)
    (eta : Real) : Prop where
  repair : Exists fun Qrepair : Fin m -> Fin n -> Real =>
    Exists fun dA : Fin m -> Fin n -> Real =>
      GramSchmidtOrthonormalColumns Qrepair /\
      (forall i j,
        A i j + dA i j = matMulRect m n n Qrepair Rhat i j) /\
      (forall j, columnFrob dA j <= eta * columnFrob A j)

/-! ## Concrete polar producer for the literal rounded loop -/

/-- The orthonormal analysis factor selected by the tall right-Gram polar
completion of the *computed* MGS factor `Qhat`.  This is not another computed
matrix: it is the exact analysis object used to repair the rounded factor. -/
noncomputable def mgsRoundedPolarRepairQ {m n : Nat}
    (Qhat : Fin m -> Fin n -> Real) (hnm : n <= m) :
    Fin m -> Fin n -> Real :=
  Classical.choose (exists_rectRightGramPolarCompletion_of_tall Qhat hnm)

/-- The selected polar repair has orthonormal columns. -/
theorem mgsRoundedPolarRepairQ_orthonormal {m n : Nat}
    (Qhat : Fin m -> Fin n -> Real) (hnm : n <= m) :
    GramSchmidtOrthonormalColumns (mgsRoundedPolarRepairQ Qhat hnm) := by
  exact (Classical.choose_spec
    (exists_rectRightGramPolarCompletion_of_tall Qhat hnm)).2

/-- The selected polar analysis factor reconstructs the computed `Qhat`
through its positive right-Gram factor. -/
theorem mgsRoundedPolarRepairQ_factor {m n : Nat}
    (Qhat : Fin m -> Fin n -> Real) (hnm : n <= m) :
    Qhat = matMulRect m n n (mgsRoundedPolarRepairQ Qhat hnm)
      (rectRightGramPolarH Qhat) := by
  exact (Classical.choose_spec
    (exists_rectRightGramPolarCompletion_of_tall Qhat hnm)).1

/-- Difference between the exact polar repair and the computed `Qhat`. -/
noncomputable def mgsRoundedPolarCorrection {m n : Nat}
    (Qhat : Fin m -> Fin n -> Real) (hnm : n <= m) :
    Fin m -> Fin n -> Real :=
  fun i j => mgsRoundedPolarRepairQ Qhat hnm i j - Qhat i j

/-- The polar correction factors as `Qrepair * (I-H)`. -/
theorem mgsRoundedPolarCorrection_eq_factor {m n : Nat}
    (Qhat : Fin m -> Fin n -> Real) (hnm : n <= m) :
    mgsRoundedPolarCorrection Qhat hnm =
      matMulRect m n n (mgsRoundedPolarRepairQ Qhat hnm)
        (fun i j => idMatrix n i j - rectRightGramPolarH Qhat i j) := by
  ext i j
  have hlin := congrFun
    (congrFun
      (matMulRect_sub_right m n n (mgsRoundedPolarRepairQ Qhat hnm)
        (idMatrix n) (rectRightGramPolarH Qhat)) i) j
  have hfactor := congrFun
    (congrFun (mgsRoundedPolarRepairQ_factor Qhat hnm) i) j
  rw [hlin, matMulRect_id_right, <- hfactor]
  rfl

/-- Opposite-sign Gram residual used by the polar resolvent identity. -/
noncomputable def mgsRoundedGramDefect {m n : Nat}
    (Qhat : Fin m -> Fin n -> Real) : Fin n -> Fin n -> Real :=
  fun i j => idMatrix n i j - rectangularGram Qhat i j

/-- Readable polar-sensitivity coefficient: the Frobenius norm of the
computed Gram defect.  The theorem below proves that this controls the polar
correction, rather than defining the coefficient from the final repaired
matrix residual. -/
noncomputable def mgsRoundedPolarSensitivityBudget {m n : Nat}
    (Qhat : Fin m -> Fin n -> Real) : Real :=
  frobNorm (mgsRoundedGramDefect Qhat)

theorem mgsRoundedPolarSensitivityBudget_nonneg {m n : Nat}
    (Qhat : Fin m -> Fin n -> Real) :
    0 <= mgsRoundedPolarSensitivityBudget Qhat :=
  frobNorm_nonneg _

/-- The spectral resolvent converts the computed Gram defect into `I-H`, so
the latter has operator norm at most the explicit Gram-defect Frobenius norm. -/
theorem mgsRounded_id_sub_polarH_opNorm2Le {m n : Nat}
    (Qhat : Fin m -> Fin n -> Real) :
    opNorm2Le
      (fun i j => idMatrix n i j - rectRightGramPolarH Qhat i j)
      (mgsRoundedPolarSensitivityBudget Qhat) := by
  let D : Fin n -> Fin n -> Real := mgsRoundedGramDefect Qhat
  have hD : opNorm2Le D (frobNorm D) := opNorm2Le_of_frobNorm_self D
  have hres := rectRightGramPolarResolvent_opNorm2Le_one Qhat
  have hprod := opNorm2Le_matMul_square_of_bounds
    (rectRightGramPolarResolvent Qhat) D (by norm_num) hres hD
  have hidentity := rectRightGramPolarResolvent_mul_id_sub_polarH_sq Qhat
  rw [rectRightGramPolarH_sq_eq_rectangularGram Qhat] at hidentity
  have hDidentity :
      matMul n (rectRightGramPolarResolvent Qhat) D =
        fun i j => idMatrix n i j - rectRightGramPolarH Qhat i j := by
    simpa [D, mgsRoundedGramDefect] using hidentity
  rw [hDidentity] at hprod
  simpa [D, mgsRoundedPolarSensitivityBudget, one_mul] using hprod

/-- Rectangular operator bound for the exact polar correction of `Qhat`. -/
theorem mgsRoundedPolarCorrection_rectOpNorm2Le {m n : Nat}
    (Qhat : Fin m -> Fin n -> Real) (hnm : n <= m) :
    rectOpNorm2Le (mgsRoundedPolarCorrection Qhat hnm)
      (mgsRoundedPolarSensitivityBudget Qhat) := by
  rw [mgsRoundedPolarCorrection_eq_factor Qhat hnm]
  have hQ : rectOpNorm2Le (mgsRoundedPolarRepairQ Qhat hnm) 1 :=
    (mgsRoundedPolarRepairQ_orthonormal Qhat hnm).rectOpNorm2Le_one
  have hH : rectOpNorm2Le
      (fun i j => idMatrix n i j - rectRightGramPolarH Qhat i j)
      (mgsRoundedPolarSensitivityBudget Qhat) :=
    rectOpNorm2Le_of_opNorm2Le_square _
      (mgsRounded_id_sub_polarH_opNorm2Le Qhat)
  have hprod := rectOpNorm2Le_rectMatMul
    (mgsRoundedPolarRepairQ Qhat hnm)
    (fun i j => idMatrix n i j - rectRightGramPolarH Qhat i j)
    (by norm_num) hQ hH
  simpa [rectMatMul, one_mul] using hprod

/-- Columnwise polar-sensitivity action bound on the computed right factor. -/
theorem mgsRoundedPolarCorrection_product_column_bound {m n : Nat}
    (Qhat : Fin m -> Fin n -> Real) (Rhat : Fin n -> Fin n -> Real)
    (hnm : n <= m) (j : Fin n) :
    columnFrob
        (matMulRect m n n (mgsRoundedPolarCorrection Qhat hnm) Rhat) j <=
      mgsRoundedPolarSensitivityBudget Qhat * columnFrob Rhat j := by
  exact columnFrob_matMulRect_le_rectOpNorm2_mul_columnFrob
    (mgsRoundedPolarCorrection Qhat hnm) Rhat
    (mgsRoundedPolarCorrection_rectOpNorm2Le Qhat hnm) j

/-- Global perturbation obtained by adding the accumulated product residual
to the action of the polar/sensitivity correction on the computed `Rhat`. -/
noncomputable def mgsRoundedGlobalRepairDelta {m n : Nat}
    (A Qhat : Fin m -> Fin n -> Real)
    (Rhat : Fin n -> Fin n -> Real) (hnm : n <= m) :
    Fin m -> Fin n -> Real :=
  fun i j =>
    mgsRoundedProductResidual A Qhat Rhat i j +
      matMulRect m n n (mgsRoundedPolarCorrection Qhat hnm) Rhat i j

/-- Interpretable column budget obtained from the proved local product
accumulation plus the proved polar Gram-defect sensitivity estimate. -/
noncomputable def mgsRoundedAccumulatedPolarColumnBudget {m n : Nat}
    (fp : FPModel) (Qhat : Fin m -> Fin n -> Real)
    (Rhat : Fin n -> Fin n -> Real)
    (V : Nat -> Fin n -> Fin m -> Real) (j : Fin n) : Real :=
  vecNorm2 (mgsRoundedProductEntryBudget fp Qhat V j) +
    mgsRoundedPolarSensitivityBudget Qhat * columnFrob Rhat j

/-- Relative coefficient corresponding to the locally accumulated product
error and the polar Gram-defect sensitivity term.  Unlike the fallback
realized quotient below, its numerator is proved from primitive Algorithm
19.12 and polar-resolvent bounds. -/
noncomputable def mgsRoundedAccumulatedPolarRelativeBudget {m n : Nat}
    (fp : FPModel) (A Qhat : Fin m -> Fin n -> Real)
    (Rhat : Fin n -> Fin n -> Real)
    (V : Nat -> Fin n -> Fin m -> Real) : Real :=
  Finset.univ.sum fun j : Fin n =>
    mgsRoundedAccumulatedPolarColumnBudget fp Qhat Rhat V j /
      columnFrob A j

theorem mgsRoundedAccumulatedPolarColumnBudget_nonneg {m n : Nat}
    (fp : FPModel) (Qhat : Fin m -> Fin n -> Real)
    (Rhat : Fin n -> Fin n -> Real)
    (V : Nat -> Fin n -> Fin m -> Real) (j : Fin n) :
    0 <= mgsRoundedAccumulatedPolarColumnBudget fp Qhat Rhat V j := by
  exact add_nonneg (vecNorm2_nonneg _)
    (mul_nonneg (mgsRoundedPolarSensitivityBudget_nonneg Qhat)
      (columnFrob_nonneg Rhat j))

theorem mgsRoundedAccumulatedPolarRelativeBudget_nonneg {m n : Nat}
    (fp : FPModel) (A Qhat : Fin m -> Fin n -> Real)
    (Rhat : Fin n -> Fin n -> Real)
    (V : Nat -> Fin n -> Fin m -> Real) :
    0 <= mgsRoundedAccumulatedPolarRelativeBudget fp A Qhat Rhat V := by
  apply Finset.sum_nonneg
  intro j _hj
  exact div_nonneg
    (mgsRoundedAccumulatedPolarColumnBudget_nonneg fp Qhat Rhat V j)
    (columnFrob_nonneg A j)

/-- The concrete global repair perturbation is bounded by the readable
accumulation-plus-polar coefficient. -/
theorem ModifiedGramSchmidtRoundedState.globalRepairDelta_column_bound
    {m n : Nat} {fp : FPModel}
    {A Q : Fin m -> Fin n -> Real}
    {R : Fin n -> Fin n -> Real}
    {V : Nat -> Fin n -> Fin m -> Real}
    (hstate : ModifiedGramSchmidtRoundedState fp A Q R V)
    (hdiag : forall k : Fin n, Ne (R k k) 0)
    (hnm : n <= m) (j : Fin n) :
    columnFrob (mgsRoundedGlobalRepairDelta A Q R hnm) j <=
      mgsRoundedAccumulatedPolarColumnBudget fp Q R V j := by
  calc
    columnFrob (mgsRoundedGlobalRepairDelta A Q R hnm) j <=
        columnFrob (mgsRoundedProductResidual A Q R) j +
          columnFrob
            (matMulRect m n n (mgsRoundedPolarCorrection Q hnm) R) j :=
      columnFrob_add_le
        (mgsRoundedProductResidual A Q R)
        (matMulRect m n n (mgsRoundedPolarCorrection Q hnm) R) j
    _ <= vecNorm2 (mgsRoundedProductEntryBudget fp Q V j) +
        mgsRoundedPolarSensitivityBudget Q * columnFrob R j :=
      add_le_add (hstate.product_residual_column_bound hdiag j)
        (mgsRoundedPolarCorrection_product_column_bound Q R hnm j)
    _ = mgsRoundedAccumulatedPolarColumnBudget fp Q R V j := rfl

/-- Relative columnwise form of the primitive accumulation-plus-polar bound. -/
theorem ModifiedGramSchmidtRoundedState.globalRepairDelta_columnwise
    {m n : Nat} {fp : FPModel}
    {A Q : Fin m -> Fin n -> Real}
    {R : Fin n -> Fin n -> Real}
    {V : Nat -> Fin n -> Fin m -> Real}
    (hstate : ModifiedGramSchmidtRoundedState fp A Q R V)
    (hdiag : forall k : Fin n, Ne (R k k) 0)
    (hnm : n <= m)
    (hsource : forall j : Fin n, 0 < columnFrob A j) :
    forall j,
      columnFrob (mgsRoundedGlobalRepairDelta A Q R hnm) j <=
        mgsRoundedAccumulatedPolarRelativeBudget fp A Q R V *
          columnFrob A j := by
  intro j
  let c := mgsRoundedAccumulatedPolarColumnBudget fp Q R V j
  have hratio :
      c / columnFrob A j <=
        mgsRoundedAccumulatedPolarRelativeBudget fp A Q R V := by
    exact Finset.single_le_sum
      (fun k _hk => div_nonneg
        (mgsRoundedAccumulatedPolarColumnBudget_nonneg fp Q R V k)
        (columnFrob_nonneg A k))
      (Finset.mem_univ j)
  have hmul := mul_le_mul_of_nonneg_right hratio (le_of_lt (hsource j))
  have hc_eq : (c / columnFrob A j) * columnFrob A j = c := by
    field_simp [ne_of_gt (hsource j)]
  calc
    columnFrob (mgsRoundedGlobalRepairDelta A Q R hnm) j <= c :=
      hstate.globalRepairDelta_column_bound hdiag hnm j
    _ = (c / columnFrob A j) * columnFrob A j := hc_eq.symm
    _ <= mgsRoundedAccumulatedPolarRelativeBudget fp A Q R V *
        columnFrob A j := hmul

/-- Concrete global repair derived from the local rounded-state accumulation
and the polar Gram-defect sensitivity theorem.  No desired repair, QR
stability statement, or final perturbation inequality is assumed. -/
theorem ModifiedGramSchmidtRoundedState.toGlobalRepairWithAccumulatedPolarBudget
    {m n : Nat} {fp : FPModel}
    {A Q : Fin m -> Fin n -> Real}
    {R : Fin n -> Fin n -> Real}
    {V : Nat -> Fin n -> Fin m -> Real}
    (hstate : ModifiedGramSchmidtRoundedState fp A Q R V)
    (hdiag : forall k : Fin n, Ne (R k k) 0)
    (hnm : n <= m)
    (hsource : forall j : Fin n, 0 < columnFrob A j) :
    ModifiedGramSchmidtGlobalRepair m n A R
      (mgsRoundedAccumulatedPolarRelativeBudget fp A Q R V) := by
  let Qrepair := mgsRoundedPolarRepairQ Q hnm
  let dA := mgsRoundedGlobalRepairDelta A Q R hnm
  refine { repair := ?_ }
  refine Exists.intro Qrepair ?_
  refine Exists.intro dA ?_
  refine And.intro (mgsRoundedPolarRepairQ_orthonormal Q hnm) ?_
  refine And.intro ?_ ?_
  · intro i j
    have hlin := congrFun
      (congrFun
        (matMulRect_sub_left_square_right
          (mgsRoundedPolarRepairQ Q hnm) Q R) i) j
    change
      A i j +
          (matMulRect m n n Q R i j - A i j +
            matMulRect m n n
              (fun a b => mgsRoundedPolarRepairQ Q hnm a b - Q a b)
              R i j) =
        matMulRect m n n (mgsRoundedPolarRepairQ Q hnm) R i j
    rw [hlin]
    ring
  · exact hstate.globalRepairDelta_columnwise hdiag hnm hsource

/-- Diagnostic per-column realized majorant for the concrete polar repair.
The source-facing producer above uses the stronger primitive local/Gram
budget; this definition remains useful for exact structural comparison. -/
noncomputable def mgsRoundedAccumulatedSensitivityColumnBudget {m n : Nat}
    (A Qhat : Fin m -> Fin n -> Real)
    (Rhat : Fin n -> Fin n -> Real) (hnm : n <= m)
    (j : Fin n) : Real :=
  columnFrob (mgsRoundedProductResidual A Qhat Rhat) j +
    columnFrob
      (matMulRect m n n (mgsRoundedPolarCorrection Qhat hnm) Rhat) j

/-- Diagnostic realized relative repair coefficient.  This is not the
interpretable source bound used by the main producer. -/
noncomputable def mgsRoundedGlobalRepairRelativeBudget {m n : Nat}
    (A Qhat : Fin m -> Fin n -> Real)
    (Rhat : Fin n -> Fin n -> Real) (hnm : n <= m) : Real :=
  Finset.univ.sum fun j : Fin n =>
    mgsRoundedAccumulatedSensitivityColumnBudget A Qhat Rhat hnm j /
      columnFrob A j

/-- The explicit global perturbation is bounded by its separated accumulated
product-residual and polar-sensitivity channels. -/
theorem mgsRoundedGlobalRepairDelta_columnFrob_le {m n : Nat}
    (A Qhat : Fin m -> Fin n -> Real)
    (Rhat : Fin n -> Fin n -> Real) (hnm : n <= m)
    (j : Fin n) :
    columnFrob (mgsRoundedGlobalRepairDelta A Qhat Rhat hnm) j <=
      mgsRoundedAccumulatedSensitivityColumnBudget A Qhat Rhat hnm j := by
  exact columnFrob_add_le
    (mgsRoundedProductResidual A Qhat Rhat)
    (matMulRect m n n (mgsRoundedPolarCorrection Qhat hnm) Rhat) j

/-- The numerical repair budget is nonnegative when source columns are
nonzero (indeed, nonnegativity itself only needs their norms nonnegative). -/
theorem mgsRoundedGlobalRepairRelativeBudget_nonneg {m n : Nat}
    (A Qhat : Fin m -> Fin n -> Real)
    (Rhat : Fin n -> Fin n -> Real) (hnm : n <= m) :
    0 <= mgsRoundedGlobalRepairRelativeBudget A Qhat Rhat hnm := by
  apply Finset.sum_nonneg
  intro j _hj
  exact div_nonneg
    (add_nonneg
      (columnFrob_nonneg (mgsRoundedProductResidual A Qhat Rhat) j)
      (columnFrob_nonneg
        (matMulRect m n n (mgsRoundedPolarCorrection Qhat hnm) Rhat) j))
    (columnFrob_nonneg A j)

/-- Each concrete repair column satisfies the fully numerical relative
budget. -/
theorem mgsRoundedGlobalRepairDelta_columnwise {m n : Nat}
    (A Qhat : Fin m -> Fin n -> Real)
    (Rhat : Fin n -> Fin n -> Real) (hnm : n <= m)
    (hsource : forall j : Fin n, 0 < columnFrob A j) :
    forall j,
      columnFrob (mgsRoundedGlobalRepairDelta A Qhat Rhat hnm) j <=
        mgsRoundedGlobalRepairRelativeBudget A Qhat Rhat hnm *
          columnFrob A j := by
  intro j
  let c := mgsRoundedAccumulatedSensitivityColumnBudget A Qhat Rhat hnm j
  have hc : 0 <= c := by
    exact add_nonneg
      (columnFrob_nonneg (mgsRoundedProductResidual A Qhat Rhat) j)
      (columnFrob_nonneg
        (matMulRect m n n (mgsRoundedPolarCorrection Qhat hnm) Rhat) j)
  have hratio :
      c / columnFrob A j <=
        mgsRoundedGlobalRepairRelativeBudget A Qhat Rhat hnm := by
    exact Finset.single_le_sum
      (fun k _hk => div_nonneg
        (add_nonneg
          (columnFrob_nonneg (mgsRoundedProductResidual A Qhat Rhat) k)
          (columnFrob_nonneg
            (matMulRect m n n (mgsRoundedPolarCorrection Qhat hnm) Rhat) k))
        (columnFrob_nonneg A k))
      (Finset.mem_univ j)
  have hmul := mul_le_mul_of_nonneg_right hratio (le_of_lt (hsource j))
  have hc_eq : (c / columnFrob A j) * columnFrob A j = c := by
    field_simp [ne_of_gt (hsource j)]
  calc
    columnFrob (mgsRoundedGlobalRepairDelta A Qhat Rhat hnm) j <= c :=
      mgsRoundedGlobalRepairDelta_columnFrob_le A Qhat Rhat hnm j
    _ = (c / columnFrob A j) * columnFrob A j := hc_eq.symm
    _ <= mgsRoundedGlobalRepairRelativeBudget A Qhat Rhat hnm *
        columnFrob A j := hmul

/-- Structural fallback using the realized residual quotient.  It constructs
the same repair witness but is deliberately not advertised as a source-level
stability bound. -/
theorem ModifiedGramSchmidtRoundedState.toGlobalRepairWithPolarBudget
    {m n : Nat} {fp : FPModel}
    {A Qhat : Fin m -> Fin n -> Real}
    {Rhat : Fin n -> Fin n -> Real}
    {V : Nat -> Fin n -> Fin m -> Real}
    (_hstate : ModifiedGramSchmidtRoundedState fp A Qhat Rhat V)
    (hnm : n <= m)
    (hsource : forall j : Fin n, 0 < columnFrob A j) :
    ModifiedGramSchmidtGlobalRepair m n A Rhat
      (mgsRoundedGlobalRepairRelativeBudget A Qhat Rhat hnm) := by
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
  · exact mgsRoundedGlobalRepairDelta_columnwise A Qhat Rhat hnm hsource

/-- The full Theorem 19.13 MGS backward-error contract supplies the weaker
global repair interface used by the Chapter 20 least-squares transfer. -/
theorem ModifiedGramSchmidtBackwardError.toGlobalRepair
    {m n : Nat} {A Qhat : Fin m -> Fin n -> Real}
    {Rhat : Fin n -> Fin n -> Real}
    {c1 c2 c3 u normA kappaA higherOrder : Real}
    (hMGS : ModifiedGramSchmidtBackwardError m n A Qhat Rhat
      c1 c2 c3 u normA kappaA higherOrder) :
    ModifiedGramSchmidtGlobalRepair m n A Rhat (c3 * u) := by
  rcases hMGS.r_factor with ⟨Qrepair, dA, hQ, hfactor, hcol⟩
  exact ⟨Qrepair, dA, hQ, hfactor, hcol⟩

/-- **Literal rounded MGS state theorem** (Higham Algorithm 19.12, page 374).

Under the standard gamma-validity condition and the honest nonzero-computed-
pivot condition required by rounded division, the concrete `FPModel` loop
`fl_modifiedGramSchmidt` satisfies all of the printed algorithm equations with
explicit local floating-point errors. -/
theorem fl_modifiedGramSchmidt_roundedState {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real)
    (hm : gammaValid fp (2 * (m + 1)))
    (hpivot : forall k : Fin n, fl_modifiedGramSchmidtR fp A k k ≠ 0) :
    ModifiedGramSchmidtRoundedState fp A
      (fl_modifiedGramSchmidtQ fp A)
      (fl_modifiedGramSchmidtR fp A) (flMGSVectors fp A) where
  initial := by
    intro j i
    rfl
  upper := fl_modifiedGramSchmidtR_upperTrapezoidal fp A
  diagonal := by
    intro k
    rw [fl_modifiedGramSchmidtR_diag]
    exact fl_norm2_eq_gsColumnNorm2_mul fp (flMGSVectors fp A k.val k) hm
  normalized := by
    intro i k
    have hpiv : flMGSColumnNorm fp (flMGSVectors fp A k.val) k ≠ 0 := by
      simpa [fl_modifiedGramSchmidtR_diag] using hpivot k
    obtain ⟨delta, hdelta, hdiv⟩ :=
      fp.model_div (flMGSVectors fp A k.val k i)
        (flMGSColumnNorm fp (flMGSVectors fp A k.val) k) hpiv
    refine ⟨delta, hdelta, ?_⟩
    rw [fl_modifiedGramSchmidtQ_col]
    simp only [flMGSNormalizedColumn, hdiv, gsNormalize]
    rw [fl_modifiedGramSchmidtR_diag]
  projection := by
    intro k j hkj
    rw [fl_modifiedGramSchmidtR_strict_upper fp A hkj]
    have hmm : gammaValid fp m := gammaValid_mono fp (by omega) hm
    have hdot := fl_dotProduct_sub_gsDot_abs_le fp
      (flMGSNormalizedColumn fp (flMGSVectors fp A k.val) k)
      (flMGSVectors fp A k.val j) hmm
    simpa [flMGSProjection, fl_modifiedGramSchmidtQ_col, gsColumn] using hdot
  update := by
    intro k j hkj i
    rw [flMGSVectors_succ_later fp A hkj]
    have hmm : gammaValid fp m := gammaValid_mono fp (by omega) hm
    have hlocal := flMGSUpdate_entry_error_bound fp
      (flMGSNormalizedColumn fp (flMGSVectors fp A k.val) k)
      (flMGSVectors fp A k.val j) i hmm
    simpa [flMGSProjection, fl_modifiedGramSchmidtQ_col, gsColumn] using hlocal

/-- Concrete Chapter 19 producer for the literal `FPModel` MGS loop.  The
repair coefficient is the proved local accumulation budget plus the proved
polar Gram-defect sensitivity budget; it is not defined from the final repair
residual. -/
theorem fl_modifiedGramSchmidt_globalRepairWithAccumulatedPolarBudget
    {m n : Nat} (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (hnm : n <= m)
    (hm : gammaValid fp (2 * (m + 1)))
    (hpivot : forall k : Fin n, Ne (fl_modifiedGramSchmidtR fp A k k) 0)
    (hsource : forall j : Fin n, 0 < columnFrob A j) :
    ModifiedGramSchmidtGlobalRepair m n A
      (fl_modifiedGramSchmidtR fp A)
      (mgsRoundedAccumulatedPolarRelativeBudget fp A
        (fl_modifiedGramSchmidtQ fp A)
        (fl_modifiedGramSchmidtR fp A) (flMGSVectors fp A)) := by
  exact
    (fl_modifiedGramSchmidt_roundedState fp A hm hpivot).toGlobalRepairWithAccumulatedPolarBudget
      hpivot hnm hsource

/-- Literal-loop specialization of the diagnostic realized-residual fallback.
Use `fl_modifiedGramSchmidt_globalRepairWithAccumulatedPolarBudget` (or the
local-Gram compression module) for an interpretable numerical coefficient. -/
theorem fl_modifiedGramSchmidt_globalRepairWithPolarBudget {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (hnm : n <= m)
    (hm : gammaValid fp (2 * (m + 1)))
    (hpivot : forall k : Fin n, Ne (fl_modifiedGramSchmidtR fp A k k) 0)
    (hsource : forall j : Fin n, 0 < columnFrob A j) :
    ModifiedGramSchmidtGlobalRepair m n A
      (fl_modifiedGramSchmidtR fp A)
      (mgsRoundedGlobalRepairRelativeBudget A
        (fl_modifiedGramSchmidtQ fp A)
        (fl_modifiedGramSchmidtR fp A) hnm) := by
  exact
    (fl_modifiedGramSchmidt_roundedState fp A hm hpivot).toGlobalRepairWithPolarBudget
      hnm hsource

end

end NumStability
