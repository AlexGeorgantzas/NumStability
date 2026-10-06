import NumStability.Algorithms.QR.Higham19Alg12MGSClosure
import NumStability.Algorithms.RankOneUpdate
import NumStability.Algorithms.QR.HouseholderQRSupport

/-!
# Rounded MGS to the padded Householder analysis process

This file supplies the missing source-facing bridge in the proof of Higham's
Theorem 19.13.  The Householder process used there is induced by the literal
rounded MGS trace; it is not a second run of the repository's standard
Householder constructor.  The first layer below proves, directly from
`fl_norm2` and `FPModel.fl_div`, that the computed MGS column is uniformly
close to the exact normalization of the current stored column.
-/

namespace NumStability

open scoped BigOperators

noncomputable section

/-- Relative coefficient for one rounded MGS normalization. -/
def mgsNormalizationEps (fp : FPModel) (m : Nat) : Real :=
  (gamma fp (m + 1) + fp.u) / (1 - gamma fp (m + 1))

/-- Exact analysis direction associated with an active MGS column. -/
def mgsExactNormalized {m : Nat} (x : Fin m -> Real) : Fin m -> Real :=
  fun i => (vecNorm2 x)⁻¹ * x i

theorem mgsNormalizationEps_nonneg (fp : FPModel) (m : Nat)
    (hm : gammaValid fp (2 * (m + 1))) :
    0 <= mgsNormalizationEps fp m := by
  have hm1 : gammaValid fp (m + 1) :=
    gammaValid_mono fp (by omega) hm
  have hgamma0 : 0 <= gamma fp (m + 1) := gamma_nonneg fp hm1
  have hgamma1 : gamma fp (m + 1) < 1 :=
    gamma_lt_one fp (m + 1) hm
  exact div_nonneg (add_nonneg hgamma0 fp.u_nonneg) (by linarith)

theorem mgsExactNormalized_norm_eq_one {m : Nat} (x : Fin m -> Real)
    (hx : 0 < vecNorm2 x) :
    vecNorm2 (mgsExactNormalized x) = 1 := by
  simpa [mgsExactNormalized] using vecNorm2_inv_smul_self_of_pos x hx

/-- Componentwise normalization error for the literal rounded MGS executor.

The denominator is the actual rounded norm and the quotient is the actual
`FPModel.fl_div`; the theorem does not posit an already-normalized output. -/
theorem flMGSNormalizedColumn_sub_exact_abs_le {m n : Nat}
    (fp : FPModel) (V : Fin n -> Fin m -> Real) (k : Fin n)
    (hm : gammaValid fp (2 * (m + 1)))
    (hk : 0 < vecNorm2 (V k)) (i : Fin m) :
    |flMGSNormalizedColumn fp V k i - mgsExactNormalized (V k) i| <=
      mgsNormalizationEps fp m * |mgsExactNormalized (V k) i| := by
  have hm1 : gammaValid fp (m + 1) :=
    gammaValid_mono fp (by omega) hm
  have hgamma0 : 0 <= gamma fp (m + 1) := gamma_nonneg fp hm1
  have hgamma1 : gamma fp (m + 1) < 1 :=
    gamma_lt_one fp (m + 1) hm
  obtain ⟨theta, htheta, hnorm⟩ :=
    fl_norm2_relative_error fp m (V k) hm
  have hsqrt :
      Real.sqrt (∑ r : Fin m, V k r * V k r) = vecNorm2 (V k) := by
    simp [vecNorm2, vecNorm2Sq, pow_two]
  rw [hsqrt] at hnorm
  have hfactor : 0 < 1 + theta := by
    linarith [neg_abs_le theta]
  have hroundedPos : 0 < flMGSColumnNorm fp V k := by
    rw [flMGSColumnNorm, hnorm]
    exact mul_pos hk hfactor
  obtain ⟨delta, hdelta, hdiv⟩ :=
    fp.model_div (V k i) (flMGSColumnNorm fp V k)
      (ne_of_gt hroundedPos)
  have hrewrite :
      flMGSNormalizedColumn fp V k i - mgsExactNormalized (V k) i =
        mgsExactNormalized (V k) i * ((delta - theta) / (1 + theta)) := by
    rw [flMGSNormalizedColumn, hdiv, flMGSColumnNorm, hnorm]
    simp only [mgsExactNormalized]
    field_simp [ne_of_gt hk, ne_of_gt hfactor]
    ring
  have hnum : |delta - theta| <= fp.u + gamma fp (m + 1) := by
    calc
      |delta - theta| <= |delta| + |theta| := abs_sub delta theta
      _ <= fp.u + gamma fp (m + 1) := add_le_add hdelta htheta
  have hnum0 : 0 <= fp.u + gamma fp (m + 1) :=
    add_nonneg fp.u_nonneg hgamma0
  have hdenLower : 1 - gamma fp (m + 1) <= 1 + theta := by
    linarith [neg_abs_le theta]
  have hdenLowerPos : 0 < 1 - gamma fp (m + 1) := by linarith
  have hfrac :
      |(delta - theta) / (1 + theta)| <= mgsNormalizationEps fp m := by
    rw [abs_div, abs_of_pos hfactor]
    calc
      |delta - theta| / (1 + theta) <=
          (fp.u + gamma fp (m + 1)) / (1 + theta) :=
        div_le_div_of_nonneg_right hnum (le_of_lt hfactor)
      _ <= (fp.u + gamma fp (m + 1)) /
          (1 - gamma fp (m + 1)) :=
        div_le_div_of_nonneg_left hnum0 hdenLowerPos hdenLower
      _ = mgsNormalizationEps fp m := by
        simp [mgsNormalizationEps, add_comm]
  rw [hrewrite, abs_mul]
  nlinarith [abs_nonneg (mgsExactNormalized (V k) i)]

/-- Euclidean form of the rounded MGS normalization error. -/
theorem flMGSNormalizedColumn_sub_exact_norm_le {m n : Nat}
    (fp : FPModel) (V : Fin n -> Fin m -> Real) (k : Fin n)
    (hm : gammaValid fp (2 * (m + 1)))
    (hk : 0 < vecNorm2 (V k)) :
    vecNorm2 (fun i =>
        flMGSNormalizedColumn fp V k i - mgsExactNormalized (V k) i) <=
      mgsNormalizationEps fp m := by
  let eps := mgsNormalizationEps fp m
  let q := mgsExactNormalized (V k)
  have heps : 0 <= eps := mgsNormalizationEps_nonneg fp m hm
  have hentry : forall i : Fin m,
      |flMGSNormalizedColumn fp V k i - q i| <= eps * |q i| := by
    intro i
    simpa [eps, q] using
      flMGSNormalizedColumn_sub_exact_abs_le fp V k hm hk i
  have hmono := vecNorm2_le_of_abs_le
    (fun i => flMGSNormalizedColumn fp V k i - q i)
    (fun i => eps * |q i|) hentry
  calc
    vecNorm2 (fun i =>
        flMGSNormalizedColumn fp V k i - mgsExactNormalized (V k) i) =
        vecNorm2 (fun i => flMGSNormalizedColumn fp V k i - q i) := by
          rfl
    _ <= vecNorm2 (fun i => eps * |q i|) := hmono
    _ = eps * vecNorm2 q := by
      rw [vecNorm2_smul, abs_of_nonneg heps, vecNorm2_abs]
    _ = eps := by rw [mgsExactNormalized_norm_eq_one (V k) hk, mul_one]
    _ = mgsNormalizationEps fp m := rfl

/-- The actual computed MGS direction has a dimension/model-only norm cap. -/
theorem flMGSNormalizedColumn_norm_le {m n : Nat}
    (fp : FPModel) (V : Fin n -> Fin m -> Real) (k : Fin n)
    (hm : gammaValid fp (2 * (m + 1)))
    (hk : 0 < vecNorm2 (V k)) :
    vecNorm2 (flMGSNormalizedColumn fp V k) <=
      1 + mgsNormalizationEps fp m := by
  let q := mgsExactNormalized (V k)
  have hdecomp :
      flMGSNormalizedColumn fp V k =
        fun i => q i + (flMGSNormalizedColumn fp V k i - q i) := by
    funext i
    ring
  rw [hdecomp]
  have herr :
      vecNorm2 (fun i => flMGSNormalizedColumn fp V k i - q i) <=
        mgsNormalizationEps fp m := by
    simpa only [q] using
      flMGSNormalizedColumn_sub_exact_norm_le fp V k hm hk
  calc
    vecNorm2 (fun i => q i +
        (flMGSNormalizedColumn fp V k i - q i)) <=
        vecNorm2 q + vecNorm2 (fun i =>
          flMGSNormalizedColumn fp V k i - q i) :=
      vecNorm2_add_le _ _
    _ <= vecNorm2 q + mgsNormalizationEps fp m :=
      add_le_add_right herr _
    _ = 1 + mgsNormalizationEps fp m := by
      rw [show vecNorm2 q = 1 by
        simpa only [q] using mgsExactNormalized_norm_eq_one (V k) hk]

/-! ## Dimension-only control of one rounded MGS update -/

/-- Coefficient obtained by taking a Euclidean norm of the explicit local
MGS update budget. -/
def mgsUpdateLocalNormCoeff (fp : FPModel) (m : Nat)
    (q : Fin m -> Real) : Real :=
  fp.u +
    (((gamma fp m * (1 + fp.u) + fp.u) * (1 + fp.u) + fp.u) *
      (vecNorm2 q) ^ 2)

/-- The explicit componentwise update budget already produced by the literal
MGS executor has a clean normwise bound. -/
theorem flMGSUpdateLocalBudget_norm_le {m : Nat}
    (fp : FPModel) (q v : Fin m -> Real)
    (hm : gammaValid fp m) :
    vecNorm2 (flMGSUpdateLocalBudget fp q v) <=
      mgsUpdateLocalNormCoeff fp m q * vecNorm2 v := by
  let S : Real := Finset.univ.sum fun r : Fin m => |q r| * |v r|
  let C : Real := gamma fp m * (1 + fp.u) + fp.u
  let K : Real := C * (1 + fp.u) + fp.u
  let E : Fin m -> Real := fun i => |q i| * S * C
  let b : Fin m -> Real := fun i => fp.u * |v i| + (K * S) * |q i|
  have hgamma0 : 0 <= gamma fp m := gamma_nonneg fp hm
  have hS0 : 0 <= S :=
    Finset.sum_nonneg fun r _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hC0 : 0 <= C := by
    dsimp [C]
    exact add_nonneg
      (mul_nonneg hgamma0 (add_nonneg zero_le_one fp.u_nonneg)) fp.u_nonneg
  have hK0 : 0 <= K := by
    dsimp [K]
    exact add_nonneg
      (mul_nonneg hC0 (add_nonneg zero_le_one fp.u_nonneg)) fp.u_nonneg
  have hE0 : forall i, 0 <= E i := by
    intro i
    dsimp [E]
    positivity
  have hinner : |gsDot q v| <= S := by
    calc
      |gsDot q v| = |Finset.univ.sum fun r : Fin m => q r * v r| := rfl
      _ <= Finset.univ.sum (fun r : Fin m => |q r * v r|) :=
        Finset.abs_sum_le_sum_abs _ _
      _ = S := by simp [S, abs_mul]
  have hbudgetEq : forall i : Fin m,
      flMGSUpdateLocalBudget fp q v i =
        E i + (|v i| + |gsDot q v * q i| + E i) * fp.u := by
    intro i
    simp only [flMGSUpdateLocalBudget]
    dsimp [E, C, S]
    ring
  have hbudget0 : forall i : Fin m,
      0 <= flMGSUpdateLocalBudget fp q v i := by
    intro i
    rw [hbudgetEq]
    exact add_nonneg (hE0 i)
      (mul_nonneg
        (add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (hE0 i))
        fp.u_nonneg)
  have hpoint : forall i : Fin m,
      flMGSUpdateLocalBudget fp q v i <= b i := by
    intro i
    have hdotmul : |gsDot q v * q i| <= S * |q i| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hinner (abs_nonneg (q i))
    rw [hbudgetEq]
    dsimp [b]
    calc
      E i + (|v i| + |gsDot q v * q i| + E i) * fp.u <=
          E i + (|v i| + S * |q i| + E i) * fp.u := by
        have hsum :
            |v i| + |gsDot q v * q i| + E i <=
              |v i| + S * |q i| + E i := by
          linarith
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_right hsum fp.u_nonneg)
      _ = fp.u * |v i| + (K * S) * |q i| := by
        dsimp [E, K]
        ring
  have hmono :
      vecNorm2 (flMGSUpdateLocalBudget fp q v) <= vecNorm2 b := by
    apply vecNorm2_le_of_abs_le
    intro i
    rw [abs_of_nonneg (hbudget0 i)]
    exact hpoint i
  have hSle : S <= vecNorm2 q * vecNorm2 v := by
    have hcs := abs_vecInnerProduct_le_vecNorm2_mul
      (fun i : Fin m => |q i|) (fun i : Fin m => |v i|)
    have hSabs : |S| = S := abs_of_nonneg hS0
    simpa [S, hSabs, vecNorm2_abs] using hcs
  have hbNorm :
      vecNorm2 b <= fp.u * vecNorm2 v + (K * S) * vecNorm2 q := by
    dsimp [b]
    calc
      vecNorm2 (fun i : Fin m =>
          fp.u * |v i| + (K * S) * |q i|) <=
          vecNorm2 (fun i : Fin m => fp.u * |v i|) +
            vecNorm2 (fun i : Fin m => (K * S) * |q i|) :=
        vecNorm2_add_le _ _
      _ = fp.u * vecNorm2 v + (K * S) * vecNorm2 q := by
        rw [vecNorm2_smul, abs_of_nonneg fp.u_nonneg, vecNorm2_abs,
          vecNorm2_smul, abs_of_nonneg (mul_nonneg hK0 hS0), vecNorm2_abs]
  have htransport :
      (K * S) * vecNorm2 q <=
        (K * (vecNorm2 q * vecNorm2 v)) * vecNorm2 q := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hSle hK0) (vecNorm2_nonneg q)
  calc
    vecNorm2 (flMGSUpdateLocalBudget fp q v) <= vecNorm2 b := hmono
    _ <= fp.u * vecNorm2 v + (K * S) * vecNorm2 q := hbNorm
    _ <= fp.u * vecNorm2 v +
        (K * (vecNorm2 q * vecNorm2 v)) * vecNorm2 q :=
      add_le_add le_rfl htransport
    _ = mgsUpdateLocalNormCoeff fp m q * vecNorm2 v := by
      simp [mgsUpdateLocalNormCoeff, K, C]
      ring

theorem flMGSUpdateLocalBudget_nonneg {m : Nat}
    (fp : FPModel) (q v : Fin m -> Real)
    (hm : gammaValid fp m) (i : Fin m) :
    0 <= flMGSUpdateLocalBudget fp q v i := by
  have hgamma0 : 0 <= gamma fp m := gamma_nonneg fp hm
  let S : Real := Finset.univ.sum fun r : Fin m => |q r| * |v r|
  have hS0 : 0 <= S :=
    Finset.sum_nonneg fun r _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  let E : Real :=
    |q i| * (gamma fp m * S) * (1 + fp.u) + |q i| * S * fp.u
  have hE0 : 0 <= E := by
    dsimp [E]
    exact add_nonneg
      (mul_nonneg
        (mul_nonneg (abs_nonneg _) (mul_nonneg hgamma0 hS0))
        (add_nonneg zero_le_one fp.u_nonneg))
      (mul_nonneg (mul_nonneg (abs_nonneg _) hS0) fp.u_nonneg)
  change E + (|v i| + |gsDot q v * q i| + E) * fp.u >= 0
  exact add_nonneg hE0
    (mul_nonneg
      (add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) hE0)
      fp.u_nonneg)

/-- Normwise form of the literal rounded-state update field. -/
theorem ModifiedGramSchmidtRoundedState.update_norm_le
    {m n : Nat} {fp : FPModel}
    {A Q : Fin m -> Fin n -> Real} {R : Fin n -> Fin n -> Real}
    {V : Nat -> Fin n -> Fin m -> Real}
    (hstate : ModifiedGramSchmidtRoundedState fp A Q R V)
    (hm : gammaValid fp m) (k j : Fin n) (hkj : k < j) :
    vecNorm2 (fun i => V (k.val + 1) j i -
        gsProjectAway (V k.val j) (gsColumn Q k) i) <=
      mgsUpdateLocalNormCoeff fp m (gsColumn Q k) *
        vecNorm2 (V k.val j) := by
  have hentry : forall i : Fin m,
      |V (k.val + 1) j i -
          gsProjectAway (V k.val j) (gsColumn Q k) i| <=
        flMGSUpdateLocalBudget fp (gsColumn Q k) (V k.val j) i :=
    fun i => hstate.update k j hkj i
  calc
    vecNorm2 (fun i => V (k.val + 1) j i -
        gsProjectAway (V k.val j) (gsColumn Q k) i) <=
        vecNorm2 (flMGSUpdateLocalBudget fp (gsColumn Q k) (V k.val j)) :=
      vecNorm2_le_of_abs_le _ _ hentry
    _ <= mgsUpdateLocalNormCoeff fp m (gsColumn Q k) *
        vecNorm2 (V k.val j) :=
      flMGSUpdateLocalBudget_norm_le fp (gsColumn Q k) (V k.val j) hm

/-- Changing the direction in one exact projection removal is Lipschitz in
the direction vector. -/
theorem gsProjectAway_sub_gsProjectAway_norm_le {m : Nat}
    (v qhat q : Fin m -> Real) :
    vecNorm2 (fun i => gsProjectAway v qhat i - gsProjectAway v q i) <=
      vecNorm2 (fun i => qhat i - q i) *
        (vecNorm2 q + vecNorm2 qhat) * vecNorm2 v := by
  let e : Fin m -> Real := fun i => q i - qhat i
  have hdot : gsDot q v - gsDot qhat v = gsDot e v := by
    unfold gsDot e
    rw [<- Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  have hdecomp :
      (fun i => gsProjectAway v qhat i - gsProjectAway v q i) =
        fun i => gsDot q v * e i + gsDot e v * qhat i := by
    funext i
    simp only [gsProjectAway]
    rw [<- hdot]
    dsimp [e]
    ring
  rw [hdecomp]
  have hq := abs_vecInnerProduct_le_vecNorm2_mul q v
  have he := abs_vecInnerProduct_le_vecNorm2_mul e v
  have henorm : vecNorm2 e = vecNorm2 (fun i => qhat i - q i) := by
    have hfun : e = fun i => -(qhat i - q i) := by
      funext i
      simp [e]
    rw [hfun, vecNorm2_neg]
  calc
    vecNorm2 (fun i => gsDot q v * e i + gsDot e v * qhat i) <=
        vecNorm2 (fun i => gsDot q v * e i) +
          vecNorm2 (fun i => gsDot e v * qhat i) :=
      vecNorm2_add_le _ _
    _ = |gsDot q v| * vecNorm2 e + |gsDot e v| * vecNorm2 qhat := by
      rw [vecNorm2_smul, vecNorm2_smul]
    _ <= (vecNorm2 q * vecNorm2 v) * vecNorm2 e +
        (vecNorm2 e * vecNorm2 v) * vecNorm2 qhat := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hq (vecNorm2_nonneg e))
        (mul_le_mul_of_nonneg_right he (vecNorm2_nonneg qhat))
    _ = vecNorm2 (fun i => qhat i - q i) *
        (vecNorm2 q + vecNorm2 qhat) * vecNorm2 v := by
      rw [henorm]
      ring

/-- Dimension/model-only cap for the norm of a computed MGS direction. -/
def mgsComputedQNormCap (fp : FPModel) (m : Nat) : Real :=
  1 + mgsNormalizationEps fp m

/-- Dimension/model-only cap for one literal rounded projection-removal
update, before accounting for the difference between the computed and exact
normalization directions. -/
def mgsUpdateLocalNormCap (fp : FPModel) (m : Nat) : Real :=
  fp.u +
    (((gamma fp m * (1 + fp.u) + fp.u) * (1 + fp.u) + fp.u) *
      (mgsComputedQNormCap fp m) ^ 2)

/-- Total bottom-block error coefficient for an MGS-induced padded step. -/
def mgsPaddedBottomStepCoeff (fp : FPModel) (m : Nat) : Real :=
  mgsUpdateLocalNormCap fp m +
    mgsNormalizationEps fp m * (2 + mgsNormalizationEps fp m)

/-- Top-row dot/normalization error coefficient for an active padded column. -/
def mgsPaddedTopStepCoeff (fp : FPModel) (m : Nat) : Real :=
  gamma fp m * mgsComputedQNormCap fp m + mgsNormalizationEps fp m

theorem mgsUpdateLocalNormCoeff_le_cap {m n : Nat}
    (fp : FPModel) (V : Fin n -> Fin m -> Real) (k : Fin n)
    (hm : gammaValid fp (2 * (m + 1)))
    (hk : 0 < vecNorm2 (V k)) :
    mgsUpdateLocalNormCoeff fp m (flMGSNormalizedColumn fp V k) <=
      mgsUpdateLocalNormCap fp m := by
  have hm0 : gammaValid fp m := gammaValid_mono fp (by omega) hm
  have hgamma0 : 0 <= gamma fp m := gamma_nonneg fp hm0
  have heps0 := mgsNormalizationEps_nonneg fp m hm
  have hcap0 : 0 <= mgsComputedQNormCap fp m := by
    simp [mgsComputedQNormCap]
    linarith
  have hq0 : 0 <= vecNorm2 (flMGSNormalizedColumn fp V k) :=
    vecNorm2_nonneg _
  have hqle : vecNorm2 (flMGSNormalizedColumn fp V k) <=
      mgsComputedQNormCap fp m := by
    simpa [mgsComputedQNormCap] using
      flMGSNormalizedColumn_norm_le fp V k hm hk
  have hsq : (vecNorm2 (flMGSNormalizedColumn fp V k)) ^ 2 <=
      (mgsComputedQNormCap fp m) ^ 2 := by
    nlinarith
  let K : Real :=
    (gamma fp m * (1 + fp.u) + fp.u) * (1 + fp.u) + fp.u
  have hK0 : 0 <= K := by
    dsimp [K]
    exact add_nonneg
      (mul_nonneg
        (add_nonneg
          (mul_nonneg hgamma0 (add_nonneg zero_le_one fp.u_nonneg))
          fp.u_nonneg)
        (add_nonneg zero_le_one fp.u_nonneg)) fp.u_nonneg
  unfold mgsUpdateLocalNormCoeff mgsUpdateLocalNormCap
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hsq hK0)

/-- A later literal MGS column update is close to projection removal along the
exactly normalized current stored column, with a coefficient independent of
the matrix data. -/
theorem flMGSVectors_succ_later_exact_normalized_norm_le {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (hm : gammaValid fp (2 * (m + 1)))
    (k j : Fin n) (hkj : k < j)
    (hk : 0 < vecNorm2 (flMGSVectors fp A k.val k)) :
    vecNorm2 (fun i => flMGSVectors fp A (k.val + 1) j i -
        gsProjectAway (flMGSVectors fp A k.val j)
          (mgsExactNormalized (flMGSVectors fp A k.val k)) i) <=
      mgsPaddedBottomStepCoeff fp m *
        vecNorm2 (flMGSVectors fp A k.val j) := by
  let V := flMGSVectors fp A k.val
  let qhat := flMGSNormalizedColumn fp V k
  let q := mgsExactNormalized (V k)
  let w := V j
  have hm0 : gammaValid fp m := gammaValid_mono fp (by omega) hm
  have heps0 : 0 <= mgsNormalizationEps fp m :=
    mgsNormalizationEps_nonneg fp m hm
  have hqnorm : vecNorm2 q = 1 := by
    simpa [q, V] using
      mgsExactNormalized_norm_eq_one (flMGSVectors fp A k.val k) hk
  have hqhatNorm : vecNorm2 qhat <= mgsComputedQNormCap fp m := by
    simpa [qhat, V, mgsComputedQNormCap] using
      flMGSNormalizedColumn_norm_le fp
        (flMGSVectors fp A k.val) k hm hk
  have hqerr : vecNorm2 (fun i => qhat i - q i) <=
      mgsNormalizationEps fp m := by
    simpa [qhat, q, V] using
      flMGSNormalizedColumn_sub_exact_norm_le fp
        (flMGSVectors fp A k.val) k hm hk
  have hupdateEntry : forall i : Fin m,
      |flMGSVectors fp A (k.val + 1) j i - gsProjectAway w qhat i| <=
        flMGSUpdateLocalBudget fp qhat w i := by
    intro i
    rw [flMGSVectors_succ_later fp A hkj]
    simpa [qhat, w, V] using
      flMGSUpdate_entry_error_bound fp qhat w i hm0
  have hcap : mgsUpdateLocalNormCoeff fp m qhat <=
      mgsUpdateLocalNormCap fp m := by
    simpa only [qhat, V] using
      (mgsUpdateLocalNormCoeff_le_cap
        (m := m) (n := n) fp (flMGSVectors fp A k.val) k hm hk)
  have hupdate :
      vecNorm2 (fun i => flMGSVectors fp A (k.val + 1) j i -
          gsProjectAway w qhat i) <=
        mgsUpdateLocalNormCap fp m * vecNorm2 w := by
    calc
      vecNorm2 (fun i => flMGSVectors fp A (k.val + 1) j i -
          gsProjectAway w qhat i) <=
          vecNorm2 (flMGSUpdateLocalBudget fp qhat w) :=
        vecNorm2_le_of_abs_le _ _ hupdateEntry
      _ <= mgsUpdateLocalNormCoeff fp m qhat * vecNorm2 w :=
        flMGSUpdateLocalBudget_norm_le fp qhat w hm0
      _ <= mgsUpdateLocalNormCap fp m * vecNorm2 w :=
        mul_le_mul_of_nonneg_right hcap (vecNorm2_nonneg w)
  have hproj0 := gsProjectAway_sub_gsProjectAway_norm_le w qhat q
  have hproj :
      vecNorm2 (fun i => gsProjectAway w qhat i - gsProjectAway w q i) <=
        (mgsNormalizationEps fp m *
          (2 + mgsNormalizationEps fp m)) * vecNorm2 w := by
    calc
      vecNorm2 (fun i => gsProjectAway w qhat i - gsProjectAway w q i) <=
          vecNorm2 (fun i => qhat i - q i) *
            (vecNorm2 q + vecNorm2 qhat) * vecNorm2 w := hproj0
      _ <= mgsNormalizationEps fp m *
          (1 + mgsComputedQNormCap fp m) * vecNorm2 w := by
        have hsum : vecNorm2 q + vecNorm2 qhat <=
            1 + mgsComputedQNormCap fp m := by
          rw [hqnorm]
          exact add_le_add le_rfl hqhatNorm
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul hqerr hsum
            (add_nonneg (vecNorm2_nonneg q) (vecNorm2_nonneg qhat)) heps0)
          (vecNorm2_nonneg w)
      _ = (mgsNormalizationEps fp m *
          (2 + mgsNormalizationEps fp m)) * vecNorm2 w := by
        change mgsNormalizationEps fp m *
            (1 + (1 + mgsNormalizationEps fp m)) * vecNorm2 w = _
        ring
  have hdecomp :
      (fun i => flMGSVectors fp A (k.val + 1) j i -
          gsProjectAway w q i) =
        fun i =>
          (flMGSVectors fp A (k.val + 1) j i - gsProjectAway w qhat i) +
          (gsProjectAway w qhat i - gsProjectAway w q i) := by
    funext i
    ring
  change vecNorm2 (fun i => flMGSVectors fp A (k.val + 1) j i -
      gsProjectAway w q i) <= _
  rw [hdecomp]
  calc
    vecNorm2 (fun i =>
        (flMGSVectors fp A (k.val + 1) j i - gsProjectAway w qhat i) +
        (gsProjectAway w qhat i - gsProjectAway w q i)) <=
        vecNorm2 (fun i => flMGSVectors fp A (k.val + 1) j i -
          gsProjectAway w qhat i) +
        vecNorm2 (fun i => gsProjectAway w qhat i -
          gsProjectAway w q i) := vecNorm2_add_le _ _
    _ <= mgsUpdateLocalNormCap fp m * vecNorm2 w +
        (mgsNormalizationEps fp m *
          (2 + mgsNormalizationEps fp m)) * vecNorm2 w :=
      add_le_add hupdate hproj
    _ = mgsPaddedBottomStepCoeff fp m * vecNorm2 w := by
      simp [mgsPaddedBottomStepCoeff]
      ring

/-- The rounded MGS projection coefficient is close to the inner product
against the exact analysis direction. -/
theorem flMGSProjection_sub_exact_normalized_dot_abs_le {m n : Nat}
    (fp : FPModel) (V : Fin n -> Fin m -> Real)
    (hm : gammaValid fp (2 * (m + 1)))
    (k j : Fin n) (hk : 0 < vecNorm2 (V k)) :
    |flMGSProjection fp V k j - gsDot (mgsExactNormalized (V k)) (V j)| <=
      mgsPaddedTopStepCoeff fp m * vecNorm2 (V j) := by
  let qhat := flMGSNormalizedColumn fp V k
  let q := mgsExactNormalized (V k)
  let w := V j
  have hm0 : gammaValid fp m := gammaValid_mono fp (by omega) hm
  have hgamma0 : 0 <= gamma fp m := gamma_nonneg fp hm0
  have heps0 : 0 <= mgsNormalizationEps fp m :=
    mgsNormalizationEps_nonneg fp m hm
  have hqhatNorm : vecNorm2 qhat <= mgsComputedQNormCap fp m := by
    simpa [qhat, mgsComputedQNormCap] using
      flMGSNormalizedColumn_norm_le fp V k hm hk
  have hqerr : vecNorm2 (fun i => qhat i - q i) <=
      mgsNormalizationEps fp m := by
    simpa [qhat, q] using
      flMGSNormalizedColumn_sub_exact_norm_le fp V k hm hk
  have hdotRound :
      |flMGSProjection fp V k j - gsDot qhat w| <=
        gamma fp m * (vecNorm2 qhat * vecNorm2 w) := by
    have hraw := dotProduct_error_bound fp m qhat w hm0
    have hsum :
        (Finset.univ.sum fun r : Fin m => |qhat r| * |w r|) <=
          vecNorm2 qhat * vecNorm2 w := by
      have hcs := abs_vecInnerProduct_le_vecNorm2_mul
        (fun r : Fin m => |qhat r|) (fun r : Fin m => |w r|)
      have hsum0 : 0 <= Finset.univ.sum fun r : Fin m =>
          |qhat r| * |w r| :=
        Finset.sum_nonneg fun r _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
      simpa [abs_of_nonneg hsum0, vecNorm2_abs] using hcs
    exact le_trans (by simpa [flMGSProjection, qhat, w, gsDot] using hraw)
      (mul_le_mul_of_nonneg_left hsum hgamma0)
  have hdotDir : |gsDot qhat w - gsDot q w| <=
      mgsNormalizationEps fp m * vecNorm2 w := by
    have heq : gsDot qhat w - gsDot q w =
        gsDot (fun i => qhat i - q i) w := by
      unfold gsDot
      rw [<- Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    rw [heq]
    exact le_trans
      (abs_vecInnerProduct_le_vecNorm2_mul (fun i => qhat i - q i) w)
      (mul_le_mul_of_nonneg_right hqerr (vecNorm2_nonneg w))
  have hsplit :
      flMGSProjection fp V k j - gsDot q w =
        (flMGSProjection fp V k j - gsDot qhat w) +
          (gsDot qhat w - gsDot q w) := by ring
  rw [hsplit]
  calc
    |(flMGSProjection fp V k j - gsDot qhat w) +
        (gsDot qhat w - gsDot q w)| <=
        |flMGSProjection fp V k j - gsDot qhat w| +
          |gsDot qhat w - gsDot q w| := abs_add_le _ _
    _ <= gamma fp m * (vecNorm2 qhat * vecNorm2 w) +
        mgsNormalizationEps fp m * vecNorm2 w :=
      add_le_add hdotRound hdotDir
    _ <= gamma fp m *
          (mgsComputedQNormCap fp m * vecNorm2 w) +
        mgsNormalizationEps fp m * vecNorm2 w := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hqhatNorm (vecNorm2_nonneg w))
          hgamma0) le_rfl
    _ = mgsPaddedTopStepCoeff fp m * vecNorm2 w := by
      simp [mgsPaddedTopStepCoeff]
      ring

/-! ## The actual MGS-induced padded process -/

/-- Padded stage built from the literal rounded MGS trace.  Processed top
rows contain computed `R`, active bottom columns contain the actual stored MGS
vectors, and processed bottom columns are exact zeros. -/
def flMGSPaddedStageSum {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) (t : Nat) :
    Sum (Fin n) (Fin m) -> Fin n -> Real
  | Sum.inl i, j =>
      if i.val < t then fl_modifiedGramSchmidtR fp A i j else 0
  | Sum.inr i, j =>
      if j.val < t then 0 else flMGSVectors fp A t j i

/-- Contiguous-row form of `flMGSPaddedStageSum`, for the generic orthogonal
sequence accumulation theorem. -/
def flMGSPaddedFinStage {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) (t : Nat) :
    Fin (n + m) -> Fin n -> Real :=
  mgsPaddedRowsToFin (flMGSPaddedStageSum fp A t)

/-- Final padded block `[Rhat;0]` of the literal rounded MGS trace. -/
def flMGSPaddedRBlock {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) : Fin (n + m) -> Fin n -> Real :=
  mgsPaddedRowsToFin (mgsStackedBlocks (fl_modifiedGramSchmidtR fp A)
    (fun _ _ => 0))

theorem flMGSPaddedFinStage_zero {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) :
    flMGSPaddedFinStage fp A 0 = mgsPaddedFinInput A := by
  ext r j
  cases r using Fin.addCases with
  | left i => simp [flMGSPaddedFinStage, flMGSPaddedStageSum,
      mgsPaddedRowsToFin, mgsPaddedRowFromFin, mgsPaddedFinInput,
      mgsPaddedInput]
  | right i => simp [flMGSPaddedFinStage, flMGSPaddedStageSum,
      mgsPaddedRowsToFin, mgsPaddedRowFromFin, mgsPaddedFinInput,
      mgsPaddedInput, flMGSVectors, gsColumn]

theorem flMGSPaddedFinStage_final {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) :
    flMGSPaddedFinStage fp A n = flMGSPaddedRBlock fp A := by
  ext r j
  cases r using Fin.addCases with
  | left i => simp [flMGSPaddedFinStage, flMGSPaddedStageSum,
      flMGSPaddedRBlock, mgsPaddedRowsToFin, mgsPaddedRowFromFin,
      mgsStackedBlocks, i.isLt]
  | right i => simp [flMGSPaddedFinStage, flMGSPaddedStageSum,
      flMGSPaddedRBlock, mgsPaddedRowsToFin, mgsPaddedRowFromFin,
      mgsStackedBlocks, j.isLt]

/-- Exact unit direction used to analyze padded stage `k`. -/
def mgsExactPaddedDirection {m n : Nat}
    (V : Fin n -> Fin m -> Real) (k : Fin n) : Fin (n + m) -> Real :=
  fun r => mgsHouseholderVector (mgsExactNormalized (V k)) k
    (mgsPaddedRowFromFin r)

@[simp] theorem mgsExactPaddedDirection_castAdd {m n : Nat}
    (V : Fin n -> Fin m -> Real) (k i : Fin n) :
    mgsExactPaddedDirection V k (Fin.castAdd m i) =
      (if i = k then -1 else 0) := by
  simp [mgsExactPaddedDirection, mgsHouseholderVector, mgsHouseholderTop,
    sumBothVec, mgsPaddedRowFromFin]

@[simp] theorem mgsExactPaddedDirection_natAdd {m n : Nat}
    (V : Fin n -> Fin m -> Real) (k : Fin n) (i : Fin m) :
    mgsExactPaddedDirection V k (Fin.natAdd n i) =
      mgsExactNormalized (V k) i := by
  simp [mgsExactPaddedDirection, mgsHouseholderVector, sumBothVec,
    mgsPaddedRowFromFin]

theorem mgsExactPaddedDirection_self_dot {m n : Nat}
    (V : Fin n -> Fin m -> Real) (k : Fin n)
    (hk : 0 < vecNorm2 (V k)) :
    (Finset.univ.sum fun r : Fin (n + m) =>
      mgsExactPaddedDirection V k r * mgsExactPaddedDirection V k r) = 2 := by
  rw [Fin.sum_univ_add]
  have hqnorm := mgsExactNormalized_norm_eq_one (V k) hk
  have hqdot :
      (Finset.univ.sum fun i : Fin m =>
        mgsExactNormalized (V k) i * mgsExactNormalized (V k) i) = 1 := by
    have hsquare := vecNorm2_sq (mgsExactNormalized (V k))
    rw [hqnorm] at hsquare
    simpa [vecNorm2Sq, pow_two] using hsquare.symm
  simp [mgsExactPaddedDirection_castAdd, mgsExactPaddedDirection_natAdd,
    hqdot]
  norm_num

theorem mgsExactPaddedDirection_householder_orthogonal {m n : Nat}
    (V : Fin n -> Fin m -> Real) (k : Fin n)
    (hk : 0 < vecNorm2 (V k)) :
    IsOrthogonal (n + m)
      (householder (n + m) (mgsExactPaddedDirection V k) 1) := by
  apply householder_orthogonal
  rw [mgsExactPaddedDirection_self_dot V k hk]
  norm_num

/-- Embed a top/bottom vector into the contiguous padded row indexing. -/
def mgsPaddedVectorToFin {m n : Nat}
    (x : Fin n -> Real) (y : Fin m -> Real) : Fin (n + m) -> Real :=
  Fin.addCases x y

theorem mgsPaddedVectorToFin_norm_le {m n : Nat}
    (x : Fin n -> Real) (y : Fin m -> Real) :
    vecNorm2 (mgsPaddedVectorToFin x y) <= vecNorm2 x + vecNorm2 y := by
  let xpad : Fin (n + m) -> Real :=
    Fin.addCases x (fun _ : Fin m => 0)
  let ypad : Fin (n + m) -> Real :=
    Fin.addCases (fun _ : Fin n => 0) y
  have hsum : mgsPaddedVectorToFin x y = fun r => xpad r + ypad r := by
    funext r
    cases r using Fin.addCases with
    | left i => simp [mgsPaddedVectorToFin, xpad, ypad]
    | right i => simp [mgsPaddedVectorToFin, xpad, ypad]
  have hxnorm : vecNorm2 xpad = vecNorm2 x := by
    unfold vecNorm2 vecNorm2Sq
    congr 1
    rw [Fin.sum_univ_add]
    simp [xpad]
  have hynorm : vecNorm2 ypad = vecNorm2 y := by
    unfold vecNorm2 vecNorm2Sq
    congr 1
    rw [Fin.sum_univ_add]
    simp [ypad]
  rw [hsum]
  exact (vecNorm2_add_le xpad ypad).trans_eq (by rw [hxnorm, hynorm])

/-- The active bottom part of a padded column is no larger than the full
padded column. -/
theorem flMGSVectors_norm_le_padded_stage_column {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (k j : Fin n) (hactive : Not (j.val < k.val)) :
    vecNorm2 (flMGSVectors fp A k.val j) <=
      vecNorm2 (fun r => flMGSPaddedFinStage fp A k.val r j) := by
  unfold vecNorm2 vecNorm2Sq
  apply Real.sqrt_le_sqrt
  rw [Fin.sum_univ_add]
  simp only [flMGSPaddedFinStage, mgsPaddedRowsToFin,
    mgsPaddedRowFromFin, flMGSPaddedStageSum]
  simp [hactive]
  positivity

/-- Inner product of the exact padded direction with an active padded stage
column. -/
theorem mgsExactPaddedDirection_inner_stage_active {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (k j : Fin n) (hactive : Not (j.val < k.val)) :
    (Finset.univ.sum fun r : Fin (n + m) =>
      mgsExactPaddedDirection (flMGSVectors fp A k.val) k r *
        flMGSPaddedFinStage fp A k.val r j) =
      gsDot (mgsExactNormalized (flMGSVectors fp A k.val k))
        (flMGSVectors fp A k.val j) := by
  rw [Fin.sum_univ_add]
  simp only [mgsExactPaddedDirection_castAdd,
    mgsExactPaddedDirection_natAdd, flMGSPaddedFinStage,
    mgsPaddedRowsToFin, mgsPaddedRowFromFin, flMGSPaddedStageSum]
  simp [hactive, gsDot]
  apply Finset.sum_eq_zero
  intro x _hx
  by_cases hxk : x = k <;> simp [hxk]

/-- Processed padded columns are orthogonal to the next exact padded
direction. -/
theorem mgsExactPaddedDirection_inner_stage_processed {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (k j : Fin n) (hproc : j.val < k.val) :
    (Finset.univ.sum fun r : Fin (n + m) =>
      mgsExactPaddedDirection (flMGSVectors fp A k.val) k r *
        flMGSPaddedFinStage fp A k.val r j) = 0 := by
  rw [Fin.sum_univ_add]
  simp only [mgsExactPaddedDirection_castAdd,
    mgsExactPaddedDirection_natAdd, flMGSPaddedFinStage,
    mgsPaddedRowsToFin, mgsPaddedRowFromFin, flMGSPaddedStageSum]
  simp [hproc]
  apply Finset.sum_eq_zero
  intro x _hx
  by_cases hxk : x = k <;> simp [hxk]

/-- Exact padded reflector action on an active bottom block. -/
theorem mgsExactPadded_householder_active_bottom {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (k j : Fin n) (hactive : Not (j.val < k.val)) (i : Fin m) :
    matMulVec (n + m)
        (householder (n + m)
          (mgsExactPaddedDirection (flMGSVectors fp A k.val) k) 1)
        (fun r => flMGSPaddedFinStage fp A k.val r j)
        (Fin.natAdd n i) =
      gsProjectAway (flMGSVectors fp A k.val j)
        (mgsExactNormalized (flMGSVectors fp A k.val k)) i := by
  have happ := congrFun
    (householder_matMulVec_eq (n + m)
      (mgsExactPaddedDirection (flMGSVectors fp A k.val) k) 1
      (fun r => flMGSPaddedFinStage fp A k.val r j)) (Fin.natAdd n i)
  rw [happ, mgsExactPaddedDirection_inner_stage_active fp A k j hactive]
  simp [flMGSPaddedFinStage, flMGSPaddedStageSum, mgsPaddedRowsToFin,
    mgsPaddedRowFromFin, hactive, mgsExactPaddedDirection_natAdd,
    gsProjectAway]
  ring

/-- Exact padded reflector action on an active top row. -/
theorem mgsExactPadded_householder_active_top {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (k j : Fin n) (hactive : Not (j.val < k.val)) (i : Fin n) :
    matMulVec (n + m)
        (householder (n + m)
          (mgsExactPaddedDirection (flMGSVectors fp A k.val) k) 1)
        (fun r => flMGSPaddedFinStage fp A k.val r j)
        (Fin.castAdd m i) =
      (if i = k then
        gsDot (mgsExactNormalized (flMGSVectors fp A k.val k))
          (flMGSVectors fp A k.val j)
       else if i.val < k.val then fl_modifiedGramSchmidtR fp A i j else 0) := by
  have happ := congrFun
    (householder_matMulVec_eq (n + m)
      (mgsExactPaddedDirection (flMGSVectors fp A k.val) k) 1
      (fun r => flMGSPaddedFinStage fp A k.val r j)) (Fin.castAdd m i)
  rw [happ, mgsExactPaddedDirection_inner_stage_active fp A k j hactive]
  simp only [flMGSPaddedFinStage, flMGSPaddedStageSum, mgsPaddedRowsToFin,
    mgsPaddedRowFromFin, mgsExactPaddedDirection_castAdd]
  by_cases hik : i = k
  · subst i
    simp
  · simp [hik]

/-- A processed padded column is fixed by the next exact padded reflector. -/
theorem mgsExactPadded_householder_processed {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (k j : Fin n) (hproc : j.val < k.val) :
    matMulVec (n + m)
        (householder (n + m)
          (mgsExactPaddedDirection (flMGSVectors fp A k.val) k) 1)
        (fun r => flMGSPaddedFinStage fp A k.val r j) =
      fun r => flMGSPaddedFinStage fp A k.val r j := by
  rw [householder_matMulVec_eq]
  funext r
  rw [mgsExactPaddedDirection_inner_stage_processed fp A k j hproc]
  ring

/-! ## One-step forward error for the literal padded trace -/

/-- A uniform dimension/model-only coefficient for one MGS-induced padded
reflector step.  The three summands respectively cover the pivot norm, the
active top projection coefficient, and the active bottom update. -/
def mgsPaddedStepCoeff (fp : FPModel) (m : Nat) : Real :=
  gamma fp (m + 1) + mgsPaddedTopStepCoeff fp m +
    mgsPaddedBottomStepCoeff fp m

theorem mgsPaddedStepCoeff_nonneg (fp : FPModel) (m : Nat)
    (hm : gammaValid fp (2 * (m + 1))) :
    0 <= mgsPaddedStepCoeff fp m := by
  have hm0 : gammaValid fp m := gammaValid_mono fp (by omega) hm
  have hm1 : gammaValid fp (m + 1) := gammaValid_mono fp (by omega) hm
  have hgamma0 : 0 <= gamma fp m := gamma_nonneg fp hm0
  have hgamma10 : 0 <= gamma fp (m + 1) := gamma_nonneg fp hm1
  have heps0 : 0 <= mgsNormalizationEps fp m :=
    mgsNormalizationEps_nonneg fp m hm
  have hqcap0 : 0 <= mgsComputedQNormCap fp m := by
    simp [mgsComputedQNormCap]
    linarith
  have hupdate0 : 0 <= mgsUpdateLocalNormCap fp m := by
    have hK0 : 0 <=
        (gamma fp m * (1 + fp.u) + fp.u) * (1 + fp.u) + fp.u := by
      exact add_nonneg
        (mul_nonneg
          (add_nonneg
            (mul_nonneg hgamma0 (add_nonneg zero_le_one fp.u_nonneg))
            fp.u_nonneg)
          (add_nonneg zero_le_one fp.u_nonneg)) fp.u_nonneg
    unfold mgsUpdateLocalNormCap
    exact add_nonneg fp.u_nonneg (mul_nonneg hK0 (sq_nonneg _))
  have htop0 : 0 <= mgsPaddedTopStepCoeff fp m := by
    unfold mgsPaddedTopStepCoeff
    exact add_nonneg (mul_nonneg hgamma0 hqcap0) heps0
  have hbottom0 : 0 <= mgsPaddedBottomStepCoeff fp m := by
    unfold mgsPaddedBottomStepCoeff
    exact add_nonneg hupdate0
      (mul_nonneg heps0 (add_nonneg (by norm_num) heps0))
  unfold mgsPaddedStepCoeff
  exact add_nonneg (add_nonneg hgamma10 htop0) hbottom0

theorem mgsPaddedTopStepCoeff_nonneg (fp : FPModel) (m : Nat)
    (hm : gammaValid fp (2 * (m + 1))) :
    0 <= mgsPaddedTopStepCoeff fp m := by
  have hm0 : gammaValid fp m := gammaValid_mono fp (by omega) hm
  have hgamma0 : 0 <= gamma fp m := gamma_nonneg fp hm0
  have heps0 : 0 <= mgsNormalizationEps fp m :=
    mgsNormalizationEps_nonneg fp m hm
  have hcap0 : 0 <= mgsComputedQNormCap fp m := by
    simp [mgsComputedQNormCap]
    linarith
  unfold mgsPaddedTopStepCoeff
  exact add_nonneg (mul_nonneg hgamma0 hcap0) heps0

theorem mgsPaddedBottomStepCoeff_nonneg (fp : FPModel) (m : Nat)
    (hm : gammaValid fp (2 * (m + 1))) :
    0 <= mgsPaddedBottomStepCoeff fp m := by
  have hm0 : gammaValid fp m := gammaValid_mono fp (by omega) hm
  have hgamma0 : 0 <= gamma fp m := gamma_nonneg fp hm0
  have heps0 : 0 <= mgsNormalizationEps fp m :=
    mgsNormalizationEps_nonneg fp m hm
  have hcap0 : 0 <= mgsComputedQNormCap fp m := by
    simp [mgsComputedQNormCap]
    linarith
  have hK0 : 0 <=
      (gamma fp m * (1 + fp.u) + fp.u) * (1 + fp.u) + fp.u := by
    exact add_nonneg
      (mul_nonneg
        (add_nonneg
          (mul_nonneg hgamma0 (add_nonneg zero_le_one fp.u_nonneg))
          fp.u_nonneg)
        (add_nonneg zero_le_one fp.u_nonneg)) fp.u_nonneg
  have hupdate0 : 0 <= mgsUpdateLocalNormCap fp m := by
    unfold mgsUpdateLocalNormCap
    exact add_nonneg fp.u_nonneg (mul_nonneg hK0 (sq_nonneg _))
  unfold mgsPaddedBottomStepCoeff
  exact add_nonneg hupdate0
    (mul_nonneg heps0 (add_nonneg (by norm_num) heps0))

/-- A nonzero rounded MGS diagonal implies that the exact norm of the stored
pivot column is positive.  This is the operational nonbreakdown condition of
the printed division, not a target conclusion. -/
theorem flMGSVectors_pivot_norm_pos_of_diag_ne_zero {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (hm : gammaValid fp (2 * (m + 1))) (k : Fin n)
    (hpivot : Ne (fl_modifiedGramSchmidtR fp A k k) 0) :
    0 < vecNorm2 (flMGSVectors fp A k.val k) := by
  have hpivNorm :
      Ne (flMGSColumnNorm fp (flMGSVectors fp A k.val) k) 0 := by
    simpa [fl_modifiedGramSchmidtR_diag] using hpivot
  obtain ⟨theta, _htheta, hnorm⟩ :=
    fl_norm2_relative_error fp m (flMGSVectors fp A k.val k) hm
  have hsqrt :
      Real.sqrt (∑ r : Fin m,
        flMGSVectors fp A k.val k r * flMGSVectors fp A k.val k r) =
        vecNorm2 (flMGSVectors fp A k.val k) := by
    simp [vecNorm2, vecNorm2Sq, pow_two]
  rw [hsqrt] at hnorm
  have hne : Ne (vecNorm2 (flMGSVectors fp A k.val k)) 0 := by
    intro hz
    apply hpivNorm
    rw [flMGSColumnNorm, hnorm, hz, zero_mul]
  exact lt_of_le_of_ne (vecNorm2_nonneg _) hne.symm

/-- The rounded diagonal norm has the standard relative error with respect to
the exact norm of the current stored MGS pivot. -/
theorem fl_modifiedGramSchmidtR_diag_sub_stage_norm_abs_le {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (hm : gammaValid fp (2 * (m + 1))) (k : Fin n) :
    |fl_modifiedGramSchmidtR fp A k k -
        vecNorm2 (flMGSVectors fp A k.val k)| <=
      gamma fp (m + 1) * vecNorm2 (flMGSVectors fp A k.val k) := by
  obtain ⟨theta, htheta, hnorm⟩ :=
    fl_norm2_relative_error fp m (flMGSVectors fp A k.val k) hm
  have hsqrt :
      Real.sqrt (∑ r : Fin m,
        flMGSVectors fp A k.val k r * flMGSVectors fp A k.val k r) =
        vecNorm2 (flMGSVectors fp A k.val k) := by
    simp [vecNorm2, vecNorm2Sq, pow_two]
  rw [hsqrt] at hnorm
  rw [fl_modifiedGramSchmidtR_diag, flMGSColumnNorm, hnorm]
  have hv0 : 0 <= vecNorm2 (flMGSVectors fp A k.val k) := vecNorm2_nonneg _
  have hrearrange :
      vecNorm2 (flMGSVectors fp A k.val k) * (1 + theta) -
          vecNorm2 (flMGSVectors fp A k.val k) =
        theta * vecNorm2 (flMGSVectors fp A k.val k) := by ring
  rw [hrearrange, abs_mul, abs_of_nonneg hv0]
  exact mul_le_mul_of_nonneg_right htheta hv0

theorem gsDot_mgsExactNormalized_self {m : Nat} (x : Fin m -> Real)
    (hx : Ne (vecNorm2 x) 0) :
    gsDot (mgsExactNormalized x) x = vecNorm2 x := by
  have heq : mgsExactNormalized x = gsNormalize x (vecNorm2 x) := by
    funext i
    simp only [mgsExactNormalized, gsNormalize]
    rw [div_eq_mul_inv]
    ring
  rw [heq]
  simpa [gsColumnNorm2] using gsDot_normalize_self x hx

theorem gsProjectAway_self_mgsExactNormalized {m : Nat}
    (x : Fin m -> Real) (hx : Ne (vecNorm2 x) 0) :
    gsProjectAway x (mgsExactNormalized x) = fun _ => 0 := by
  funext i
  rw [gsProjectAway, gsDot_mgsExactNormalized_self x hx]
  simp only [mgsExactNormalized]
  field_simp
  ring

/-- Once a padded column has been processed, the literal rounded trace keeps
it unchanged at the next stage. -/
theorem flMGSPaddedFinStage_succ_processed {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (k j : Fin n) (hproc : j.val < k.val) :
    (fun r => flMGSPaddedFinStage fp A (k.val + 1) r j) =
      fun r => flMGSPaddedFinStage fp A k.val r j := by
  funext r
  cases r using Fin.addCases with
  | left i =>
      simp only [flMGSPaddedFinStage, mgsPaddedRowsToFin,
        mgsPaddedRowFromFin, flMGSPaddedStageSum]
      by_cases hi : i.val < k.val
      · have hisucc : i.val < k.val + 1 := by omega
        simp [hi, hisucc]
      · by_cases hik : i = k
        · subst i
          simp [fl_modifiedGramSchmidtR]
          omega
        · have hnotSucc : Not (i.val < k.val + 1) := by
            have hine : Ne i.val k.val := by
              intro h
              apply hik
              exact Fin.ext h
            omega
          simp [hi, hnotSucc]
  | right i =>
      simp [flMGSPaddedFinStage, mgsPaddedRowsToFin,
        mgsPaddedRowFromFin, flMGSPaddedStageSum, hproc]
      intro hkj
      omega

/-- Exact error shape for a later active column of one literal padded MGS
step: one top coefficient error stacked over the actual bottom update error. -/
theorem flMGSPaddedFinStage_succ_later_error_eq {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (k j : Fin n) (hkj : k < j) :
    (fun r => flMGSPaddedFinStage fp A (k.val + 1) r j -
      matMulVec (n + m)
        (householder (n + m)
          (mgsExactPaddedDirection (flMGSVectors fp A k.val) k) 1)
        (fun s => flMGSPaddedFinStage fp A k.val s j) r) =
      mgsPaddedVectorToFin
        (fun i => if i = k then
          fl_modifiedGramSchmidtR fp A k j -
            gsDot (mgsExactNormalized (flMGSVectors fp A k.val k))
              (flMGSVectors fp A k.val j)
          else 0)
        (fun i => flMGSVectors fp A (k.val + 1) j i -
          gsProjectAway (flMGSVectors fp A k.val j)
            (mgsExactNormalized (flMGSVectors fp A k.val k)) i) := by
  funext r
  have hactive : Not (j.val < k.val) := by omega
  cases r using Fin.addCases with
  | left i =>
      rw [mgsExactPadded_householder_active_top fp A k j hactive i]
      simp only [mgsPaddedVectorToFin, Fin.addCases_left]
      simp only [flMGSPaddedFinStage, mgsPaddedRowsToFin,
        mgsPaddedRowFromFin, flMGSPaddedStageSum]
      by_cases hik : i = k
      · subst i
        simp
      · by_cases hi : i.val < k.val
        · have hisucc : i.val < k.val + 1 := by omega
          simp [hik, hi, hisucc]
        · have hnotSucc : Not (i.val < k.val + 1) := by
            have hine : Ne i.val k.val := by
              intro h
              apply hik
              exact Fin.ext h
            omega
          simp [hik, hi, hnotSucc]
  | right i =>
      rw [mgsExactPadded_householder_active_bottom fp A k j hactive i]
      simp only [mgsPaddedVectorToFin, Fin.addCases_right]
      simp [flMGSPaddedFinStage, mgsPaddedRowsToFin,
        mgsPaddedRowFromFin, flMGSPaddedStageSum]
      omega

/-- Exact error shape for the pivot column: only the rounded norm remains in
the top pivot row; the exact normalized reflector annihilates the bottom
column. -/
theorem flMGSPaddedFinStage_succ_pivot_error_eq {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (k : Fin n) (hk : 0 < vecNorm2 (flMGSVectors fp A k.val k)) :
    (fun r => flMGSPaddedFinStage fp A (k.val + 1) r k -
      matMulVec (n + m)
        (householder (n + m)
          (mgsExactPaddedDirection (flMGSVectors fp A k.val) k) 1)
        (fun s => flMGSPaddedFinStage fp A k.val s k) r) =
      mgsPaddedVectorToFin
        (fun i => if i = k then
          fl_modifiedGramSchmidtR fp A k k -
            vecNorm2 (flMGSVectors fp A k.val k)
          else 0)
        (fun _ => 0) := by
  funext r
  have hactive : Not (k.val < k.val) := by omega
  have hdot :
      gsDot (mgsExactNormalized (flMGSVectors fp A k.val k))
          (flMGSVectors fp A k.val k) =
        vecNorm2 (flMGSVectors fp A k.val k) :=
    gsDot_mgsExactNormalized_self _ (ne_of_gt hk)
  cases r using Fin.addCases with
  | left i =>
      rw [mgsExactPadded_householder_active_top fp A k k hactive i]
      simp only [mgsPaddedVectorToFin, Fin.addCases_left]
      simp only [flMGSPaddedFinStage, mgsPaddedRowsToFin,
        mgsPaddedRowFromFin, flMGSPaddedStageSum]
      by_cases hik : i = k
      · subst i
        simp [hdot]
      · by_cases hi : i.val < k.val
        · have hisucc : i.val < k.val + 1 := by omega
          simp [hik, hi, hisucc]
        · have hnotSucc : Not (i.val < k.val + 1) := by
            have hine : Ne i.val k.val := by
              intro h
              apply hik
              exact Fin.ext h
            omega
          simp [hik, hi, hnotSucc]
  | right i =>
      rw [mgsExactPadded_householder_active_bottom fp A k k hactive i]
      have hproj := congrFun
        (gsProjectAway_self_mgsExactNormalized
          (flMGSVectors fp A k.val k) (ne_of_gt hk)) i
      simp only [mgsPaddedVectorToFin, Fin.addCases_right]
      simp [flMGSPaddedFinStage, mgsPaddedRowsToFin,
        mgsPaddedRowFromFin, flMGSPaddedStageSum, hproj]

theorem vecNorm2_fin_single {n : Nat} (k : Fin n) (z : Real) :
    vecNorm2 (fun i : Fin n => if i = k then z else 0) = |z| := by
  unfold vecNorm2 vecNorm2Sq
  simp [Real.sqrt_sq_eq_abs]

/-- Uniform relative forward-error bound for a later active column of the
literal padded trace. -/
theorem flMGSPaddedFinStage_succ_later_forward_error_norm_le {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (hm : gammaValid fp (2 * (m + 1)))
    (k j : Fin n) (hkj : k < j)
    (hk : 0 < vecNorm2 (flMGSVectors fp A k.val k)) :
    vecNorm2 (fun r => flMGSPaddedFinStage fp A (k.val + 1) r j -
      matMulVec (n + m)
        (householder (n + m)
          (mgsExactPaddedDirection (flMGSVectors fp A k.val) k) 1)
        (fun s => flMGSPaddedFinStage fp A k.val s j) r) <=
      mgsPaddedStepCoeff fp m *
        vecNorm2 (fun r => flMGSPaddedFinStage fp A k.val r j) := by
  let v := flMGSVectors fp A k.val j
  let q := mgsExactNormalized (flMGSVectors fp A k.val k)
  let topErr : Fin n -> Real := fun i => if i = k then
    fl_modifiedGramSchmidtR fp A k j - gsDot q v else 0
  let bottomErr : Fin m -> Real := fun i =>
    flMGSVectors fp A (k.val + 1) j i - gsProjectAway v q i
  have hshape := flMGSPaddedFinStage_succ_later_error_eq fp A k j hkj
  have htop : vecNorm2 topErr <=
      mgsPaddedTopStepCoeff fp m * vecNorm2 v := by
    rw [show vecNorm2 topErr =
        |fl_modifiedGramSchmidtR fp A k j - gsDot q v| by
      simpa [topErr] using vecNorm2_fin_single k
        (fl_modifiedGramSchmidtR fp A k j - gsDot q v)]
    rw [fl_modifiedGramSchmidtR_strict_upper fp A hkj]
    simpa [q, v] using
      flMGSProjection_sub_exact_normalized_dot_abs_le fp
        (flMGSVectors fp A k.val) hm k j hk
  have hbottom : vecNorm2 bottomErr <=
      mgsPaddedBottomStepCoeff fp m * vecNorm2 v := by
    simpa [bottomErr, q, v] using
      flMGSVectors_succ_later_exact_normalized_norm_le fp A hm k j hkj hk
  have hm1 : gammaValid fp (m + 1) := gammaValid_mono fp (by omega) hm
  have hgamma0 : 0 <= gamma fp (m + 1) := gamma_nonneg fp hm1
  have hcoeff0 : 0 <= mgsPaddedStepCoeff fp m :=
    mgsPaddedStepCoeff_nonneg fp m hm
  have hcoeffLe :
      mgsPaddedTopStepCoeff fp m + mgsPaddedBottomStepCoeff fp m <=
        mgsPaddedStepCoeff fp m := by
    unfold mgsPaddedStepCoeff
    linarith
  have hvle : vecNorm2 v <=
      vecNorm2 (fun r => flMGSPaddedFinStage fp A k.val r j) := by
    simpa [v] using flMGSVectors_norm_le_padded_stage_column fp A k j (by omega)
  rw [hshape]
  change vecNorm2 (mgsPaddedVectorToFin topErr bottomErr) <= _
  calc
    vecNorm2 (mgsPaddedVectorToFin topErr bottomErr) <=
        vecNorm2 topErr + vecNorm2 bottomErr :=
      mgsPaddedVectorToFin_norm_le topErr bottomErr
    _ <= mgsPaddedTopStepCoeff fp m * vecNorm2 v +
        mgsPaddedBottomStepCoeff fp m * vecNorm2 v :=
      add_le_add htop hbottom
    _ = (mgsPaddedTopStepCoeff fp m + mgsPaddedBottomStepCoeff fp m) *
        vecNorm2 v := by ring
    _ <= mgsPaddedStepCoeff fp m * vecNorm2 v :=
      mul_le_mul_of_nonneg_right hcoeffLe (vecNorm2_nonneg v)
    _ <= mgsPaddedStepCoeff fp m *
        vecNorm2 (fun r => flMGSPaddedFinStage fp A k.val r j) :=
      mul_le_mul_of_nonneg_left hvle hcoeff0

/-- Uniform relative forward-error bound for the pivot column of the literal
padded trace. -/
theorem flMGSPaddedFinStage_succ_pivot_forward_error_norm_le {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (hm : gammaValid fp (2 * (m + 1))) (k : Fin n)
    (hk : 0 < vecNorm2 (flMGSVectors fp A k.val k)) :
    vecNorm2 (fun r => flMGSPaddedFinStage fp A (k.val + 1) r k -
      matMulVec (n + m)
        (householder (n + m)
          (mgsExactPaddedDirection (flMGSVectors fp A k.val) k) 1)
        (fun s => flMGSPaddedFinStage fp A k.val s k) r) <=
      mgsPaddedStepCoeff fp m *
        vecNorm2 (fun r => flMGSPaddedFinStage fp A k.val r k) := by
  let v := flMGSVectors fp A k.val k
  let topErr : Fin n -> Real := fun i => if i = k then
    fl_modifiedGramSchmidtR fp A k k - vecNorm2 v else 0
  let bottomErr : Fin m -> Real := fun _ => 0
  have hshape := flMGSPaddedFinStage_succ_pivot_error_eq fp A k hk
  have htop : vecNorm2 topErr <= gamma fp (m + 1) * vecNorm2 v := by
    rw [show vecNorm2 topErr =
        |fl_modifiedGramSchmidtR fp A k k - vecNorm2 v| by
      simpa [topErr] using vecNorm2_fin_single k
        (fl_modifiedGramSchmidtR fp A k k - vecNorm2 v)]
    simpa [v] using
      fl_modifiedGramSchmidtR_diag_sub_stage_norm_abs_le fp A hm k
  have htopCoeff0 := mgsPaddedTopStepCoeff_nonneg fp m hm
  have hbottomCoeff0 := mgsPaddedBottomStepCoeff_nonneg fp m hm
  have hgammaLe : gamma fp (m + 1) <= mgsPaddedStepCoeff fp m := by
    unfold mgsPaddedStepCoeff
    linarith
  have hcoeff0 : 0 <= mgsPaddedStepCoeff fp m :=
    mgsPaddedStepCoeff_nonneg fp m hm
  have hvle : vecNorm2 v <=
      vecNorm2 (fun r => flMGSPaddedFinStage fp A k.val r k) := by
    simpa [v] using flMGSVectors_norm_le_padded_stage_column fp A k k (by omega)
  rw [hshape]
  change vecNorm2 (mgsPaddedVectorToFin topErr bottomErr) <= _
  calc
    vecNorm2 (mgsPaddedVectorToFin topErr bottomErr) <=
        vecNorm2 topErr + vecNorm2 bottomErr :=
      mgsPaddedVectorToFin_norm_le topErr bottomErr
    _ = vecNorm2 topErr := by simp [bottomErr, vecNorm2, vecNorm2Sq]
    _ <= gamma fp (m + 1) * vecNorm2 v := htop
    _ <= mgsPaddedStepCoeff fp m * vecNorm2 v :=
      mul_le_mul_of_nonneg_right hgammaLe (vecNorm2_nonneg v)
    _ <= mgsPaddedStepCoeff fp m *
        vecNorm2 (fun r => flMGSPaddedFinStage fp A k.val r k) :=
      mul_le_mul_of_nonneg_left hvle hcoeff0

/-- Processed columns incur exactly zero error in the next padded step. -/
theorem flMGSPaddedFinStage_succ_processed_forward_error_norm_le {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (hm : gammaValid fp (2 * (m + 1)))
    (k j : Fin n) (hproc : j.val < k.val) :
    vecNorm2 (fun r => flMGSPaddedFinStage fp A (k.val + 1) r j -
      matMulVec (n + m)
        (householder (n + m)
          (mgsExactPaddedDirection (flMGSVectors fp A k.val) k) 1)
        (fun s => flMGSPaddedFinStage fp A k.val s j) r) <=
      mgsPaddedStepCoeff fp m *
        vecNorm2 (fun r => flMGSPaddedFinStage fp A k.val r j) := by
  have hstage := flMGSPaddedFinStage_succ_processed fp A k j hproc
  have hreflect := mgsExactPadded_householder_processed fp A k j hproc
  have hzero :
      (fun r => flMGSPaddedFinStage fp A (k.val + 1) r j -
        matMulVec (n + m)
          (householder (n + m)
            (mgsExactPaddedDirection (flMGSVectors fp A k.val) k) 1)
          (fun s => flMGSPaddedFinStage fp A k.val s j) r) =
        fun _ => 0 := by
    funext r
    rw [congrFun hstage r, congrFun hreflect r]
    ring
  rw [hzero]
  have hcoeff0 := mgsPaddedStepCoeff_nonneg fp m hm
  have hright : 0 <= mgsPaddedStepCoeff fp m *
      vecNorm2 (fun r => flMGSPaddedFinStage fp A k.val r j) :=
    mul_nonneg hcoeff0 (vecNorm2_nonneg _)
  simpa [vecNorm2, vecNorm2Sq] using hright

/-- Every column of one literal padded MGS step satisfies the same relative
forward-error bound. -/
theorem flMGSPaddedFinStage_succ_forward_error_norm_le {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (hm : gammaValid fp (2 * (m + 1)))
    (hpivot : forall k : Fin n,
      Ne (fl_modifiedGramSchmidtR fp A k k) 0)
    (k j : Fin n) :
    vecNorm2 (fun r => flMGSPaddedFinStage fp A (k.val + 1) r j -
      matMulVec (n + m)
        (householder (n + m)
          (mgsExactPaddedDirection (flMGSVectors fp A k.val) k) 1)
        (fun s => flMGSPaddedFinStage fp A k.val s j) r) <=
      mgsPaddedStepCoeff fp m *
        vecNorm2 (fun r => flMGSPaddedFinStage fp A k.val r j) := by
  by_cases hproc : j.val < k.val
  · exact flMGSPaddedFinStage_succ_processed_forward_error_norm_le
      fp A hm k j hproc
  by_cases hjk : j = k
  · subst j
    exact flMGSPaddedFinStage_succ_pivot_forward_error_norm_le fp A hm k
      (flMGSVectors_pivot_norm_pos_of_diag_ne_zero fp A hm k (hpivot k))
  · have hkj : k < j := by
      have hne : Ne j.val k.val := by
        intro h
        apply hjk
        exact Fin.ext h
      omega
    exact flMGSPaddedFinStage_succ_later_forward_error_norm_le fp A hm k j hkj
      (flMGSVectors_pivot_norm_pos_of_diag_ne_zero fp A hm k (hpivot k))

/-- One actual padded MGS transition satisfies the generic source-faithful
columnwise Householder application contract. -/
theorem flMGSPaddedFinStage_step_contract {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (hm : gammaValid fp (2 * (m + 1)))
    (hpivot : forall k : Fin n,
      Ne (fl_modifiedGramSchmidtR fp A k k) 0)
    (k : Fin n) :
    HouseholderColumnwisePanelAppError (n + m) n
      (householder (n + m)
        (mgsExactPaddedDirection (flMGSVectors fp A k.val) k) 1)
      (flMGSPaddedFinStage fp A k.val)
      (flMGSPaddedFinStage fp A (k.val + 1))
      (fun _ => 0) (fun _ => 0) (mgsPaddedStepCoeff fp m) := by
  apply HouseholderColumnwisePanelAppError.of_forward_errors
  · exact mgsExactPaddedDirection_householder_orthogonal
      (flMGSVectors fp A k.val) k
      (flMGSVectors_pivot_norm_pos_of_diag_ne_zero fp A hm k (hpivot k))
  · exact mgsPaddedStepCoeff_nonneg fp m hm
  · intro j
    exact flMGSPaddedFinStage_succ_forward_error_norm_le fp A hm hpivot k j
  · simp [matMulVec, vecNorm2, vecNorm2Sq]

/-- Total exact reflector sequence determined by the literal rounded MGS
trace.  Values beyond the `n` executed steps are irrelevant and set to the
identity. -/
def mgsPaddedExactReflectorSequence {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real) (t : Nat) :
    Fin (n + m) -> Fin (n + m) -> Real :=
  if ht : t < n then
    householder (n + m)
      (mgsExactPaddedDirection (flMGSVectors fp A t) (Fin.mk t ht)) 1
  else fun i j => if i = j then 1 else 0

/-- End-to-end columnwise backward error for the literal MGS-induced padded
Householder process.  The final matrix is the actual computed block
`[Rhat;0]`; neither the orthogonal factor nor the perturbation is a premise. -/
theorem fl_modifiedGramSchmidt_padded_orthogonal_columnwise_backward_error
    {m n : Nat} (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (hm : gammaValid fp (2 * (m + 1)))
    (hpivot : forall k : Fin n,
      Ne (fl_modifiedGramSchmidtR fp A k k) 0) :
    exists (Q : Fin (n + m) -> Fin (n + m) -> Real)
        (dA : Fin (n + m) -> Fin n -> Real),
      IsOrthogonal (n + m) Q /\
      (forall i j, flMGSPaddedRBlock fp A i j =
        matMulRectLeft (matTranspose Q)
          (fun a b => mgsPaddedFinInput A a b + dA a b) i j) /\
      (forall j : Fin n,
        vecNorm2 (fun i => dA i j) <=
          ((1 + mgsPaddedStepCoeff fp m) ^ n - 1) *
            vecNorm2 (fun i => mgsPaddedFinInput A i j)) := by
  let z : Fin (n + m) -> Real := fun _ => 0
  have hc : 0 <= mgsPaddedStepCoeff fp m :=
    mgsPaddedStepCoeff_nonneg fp m hm
  have hstep : forall t, t < n ->
      HouseholderColumnwisePanelAppError (n + m) n
        (mgsPaddedExactReflectorSequence fp A t)
        (flMGSPaddedFinStage fp A t)
        (flMGSPaddedFinStage fp A (t + 1)) z z
        (mgsPaddedStepCoeff fp m) := by
    intro t ht
    simpa [mgsPaddedExactReflectorSequence, ht, z] using
      flMGSPaddedFinStage_step_contract fp A hm hpivot (Fin.mk t ht)
  obtain ⟨Q, dA, _db, hQ, hfinal, _hb, hcol, _hdb⟩ :=
    householderColumnwisePanelAppError_rect_orthogonal_columnwise_vector_sequence_geometric
      (n + m) n n (mgsPaddedFinInput A) z
      (flMGSPaddedFinStage fp A) (fun _ => z)
      (mgsPaddedExactReflectorSequence fp A)
      (mgsPaddedStepCoeff fp m) hc
      (flMGSPaddedFinStage_zero fp A) rfl hstep
  refine ⟨Q, dA, hQ, ?_, hcol⟩
  intro i j
  have hij := hfinal i j
  rw [flMGSPaddedFinStage_final fp A] at hij
  exact hij

/-- Exact all-orders relative coefficient accumulated by the literal padded
MGS process. -/
def mgsPaddedAccumulatedCoeff (fp : FPModel) (m n : Nat) : Real :=
  (1 + mgsPaddedStepCoeff fp m) ^ n - 1

theorem mgsPaddedAccumulatedCoeff_nonneg (fp : FPModel) (m n : Nat)
    (hm : gammaValid fp (2 * (m + 1))) :
    0 <= mgsPaddedAccumulatedCoeff fp m n := by
  have hc := mgsPaddedStepCoeff_nonneg fp m hm
  have hbase : (1 : Real) <= 1 + mgsPaddedStepCoeff fp m := by linarith
  have hpow : (1 : Real) <= (1 + mgsPaddedStepCoeff fp m) ^ n :=
    one_le_pow₀ hbase
  unfold mgsPaddedAccumulatedCoeff
  linarith

theorem mgsPaddedEconomyR_flMGSPaddedRBlock {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real) :
    mgsPaddedEconomyR (flMGSPaddedRBlock fp A) =
      fl_modifiedGramSchmidtR fp A := by
  ext i j
  simp [mgsPaddedEconomyR, flMGSPaddedRBlock, mgsPaddedTopBlock,
    mgsPaddedRowsFromFin, mgsPaddedRowsToFin, mgsPaddedRowFromFin,
    mgsPaddedRowToFin, mgsStackedBlocks]

theorem flMGSPaddedRBlock_bottom_zero {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real) :
    mgsPaddedBottomBlock (mgsPaddedRowsFromFin (flMGSPaddedRBlock fp A)) =
      (fun _ _ => 0 : Fin m -> Fin n -> Real) := by
  ext i j
  simp [flMGSPaddedRBlock, mgsPaddedBottomBlock, mgsPaddedRowsFromFin,
    mgsPaddedRowsToFin, mgsPaddedRowFromFin, mgsPaddedRowToFin,
    mgsStackedBlocks]

/-- Turn the accumulated transpose representation into the forward padded
product `[0;A] + dA = Q [Rhat;0]` using orthogonality of the constructed `Q`. -/
theorem mgsPadded_forward_product_of_transpose_representation {m n : Nat}
    {Q : Fin (n + m) -> Fin (n + m) -> Real}
    {R B : Fin (n + m) -> Fin n -> Real}
    (hQ : IsOrthogonal (n + m) Q)
    (hR : forall i j,
      R i j = matMulRect (n + m) (n + m) n (matTranspose Q) B i j) :
    B = matMulRect (n + m) (n + m) n Q R := by
  have hRmat :
      R = matMulRect (n + m) (n + m) n (matTranspose Q) B := by
    ext i j
    exact hR i j
  have hQQT : matMul (n + m) Q (matTranspose Q) = idMatrix (n + m) := by
    ext i j
    exact hQ.right_inv i j
  ext i j
  calc
    B i j = matMulRect (n + m) (n + m) n (idMatrix (n + m)) B i j := by
      rw [matMulRect_id_left]
    _ = matMulRect (n + m) (n + m) n
          (matMul (n + m) Q (matTranspose Q)) B i j := by rw [hQQT]
    _ = matMulRect (n + m) (n + m) n Q
          (matMulRect (n + m) (n + m) n (matTranspose Q) B) i j := by
      rw [matMulRect_assoc_square_left]
    _ = matMulRect (n + m) (n + m) n Q R i j := by rw [<- hRmat]

/-- Source-facing exact all-orders repair for the literal rounded MGS output.
The orthonormal factor and perturbation are constructed from the accumulated
padded trace and the proved Problem 19.12 CS/polar completion. -/
theorem fl_modifiedGramSchmidt_padded_repaired_factorization {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (hnm : n <= m)
    (hm : gammaValid fp (2 * (m + 1)))
    (hpivot : forall k : Fin n,
      Ne (fl_modifiedGramSchmidtR fp A k k) 0) :
    exists (Qrepair : Fin m -> Fin n -> Real)
        (dA2 : Fin m -> Fin n -> Real),
      GramSchmidtOrthonormalColumns Qrepair /\
      (fun i j => A i j + dA2 i j) =
        matMulRect m n n Qrepair (fl_modifiedGramSchmidtR fp A) /\
      (forall j : Fin n,
        columnFrob dA2 j <=
          (2 * mgsPaddedAccumulatedCoeff fp m n) * columnFrob A j) := by
  obtain ⟨Qfull, dA, hQfull, hrepr, hcol⟩ :=
    fl_modifiedGramSchmidt_padded_orthogonal_columnwise_backward_error
      fp A hm hpivot
  let Bfin : Fin (n + m) -> Fin n -> Real :=
    fun r j => mgsPaddedFinInput A r j + dA r j
  let Bsum : Sum (Fin n) (Fin m) -> Fin n -> Real :=
    mgsPaddedRowsFromFin Bfin
  let dTop : Fin n -> Fin n -> Real := mgsPaddedTopPerturbation Bsum
  let dBottom : Fin m -> Fin n -> Real :=
    mgsPaddedBottomPerturbation A Bsum
  have hforward :
      Bfin = matMulRect (n + m) (n + m) n Qfull
        (flMGSPaddedRBlock fp A) := by
    exact mgsPadded_forward_product_of_transpose_representation
      hQfull (by simpa [Bfin] using hrepr)
  have hsumprod :
      Bsum = mgsPaddedRowsFromFin
        (matMulRect (n + m) (n + m) n Qfull
          (flMGSPaddedRBlock fp A)) := by
    simpa [Bsum] using congrArg mgsPaddedRowsFromFin hforward
  have hpert : mgsPaddedPerturbedInput A dTop dBottom = Bsum := by
    exact mgsPaddedPerturbedInput_eta A Bsum
  have hprod :
      mgsPaddedPerturbedInput A dTop dBottom =
        mgsPaddedRowsFromFin
          (matMulRect (n + m) (n + m) n Qfull
            (flMGSPaddedRBlock fp A)) := hpert.trans hsumprod
  have hRbot := flMGSPaddedRBlock_bottom_zero fp A
  have hbottom0 :=
    mgsPaddedPerturbedInput_bottom_eq_economyProduct
      A dTop dBottom Qfull (flMGSPaddedRBlock fp A) hprod hRbot
  have hbottom :
      (fun i j => A i j + dBottom i j) =
        matMulRect m n n (mgsPaddedEconomyQ Qfull)
          (fl_modifiedGramSchmidtR fp A) := by
    simpa [mgsPaddedEconomyR_flMGSPaddedRBlock fp A] using hbottom0
  have htop0 :=
    mgsPaddedPerturbedInput_top_eq_economyProduct
      A dTop dBottom Qfull (flMGSPaddedRBlock fp A) hprod hRbot
  have htop :
      dTop = matMul n (mgsPaddedEconomyP11 Qfull)
        (fl_modifiedGramSchmidtR fp A) := by
    simpa [mgsPaddedEconomyR_flMGSPaddedRBlock fp A, matMulRect] using htop0
  have hcolF : forall j : Fin n,
      columnFrob dA j <= mgsPaddedAccumulatedCoeff fp m n *
        columnFrob (mgsPaddedFinInput A) j := by
    intro j
    simpa [mgsPaddedAccumulatedCoeff, columnFrob_eq_vecNorm2] using hcol j
  have hstack :
      mgsStackedPerturbationColumnwiseBound A dTop dBottom
        (mgsPaddedAccumulatedCoeff fp m n) := by
    simpa [dTop, dBottom, Bsum, Bfin] using
      mgsStackedPerturbationColumnwiseBound_of_rowsFromFin_add_padded_bound
        A dA hcolF
  let hinput : MGSProblem1912CSPolarInput m n
      (mgsPaddedEconomyP11 Qfull) (mgsPaddedEconomyQ Qfull) :=
    MGSProblem1912CSPolarInput.of_paddedEconomy_blocks hnm hQfull
  obtain ⟨Qrepair, F, hdata⟩ :=
    mgsProblem1912_correctionMapData_exists_of_csPolarInput hinput
  have hmap : MGSProblem1912CorrectionMap m n
      (mgsPaddedEconomyQ Qfull) Qrepair dTop
      (fl_modifiedGramSchmidtR fp A) F :=
    hdata.to_correctionMap htop
  have htopCol : forall j,
      columnFrob dTop j <=
        mgsPaddedAccumulatedCoeff fp m n * columnFrob A j :=
    mgsTopPerturbation_columnFrob_le_of_stackedColumnwiseBound
      A dTop dBottom hstack
  have hbottomCol : forall j,
      columnFrob dBottom j <=
        mgsPaddedAccumulatedCoeff fp m n * columnFrob A j :=
    mgsBottomPerturbation_columnFrob_le_of_stackedColumnwiseBound
      A dTop dBottom hstack
  let repairedDelta : Fin m -> Fin n -> Real := fun i j =>
    matMulRect m n n F dTop i j + dBottom i j
  have hrepairCol : forall j,
      columnFrob repairedDelta j <=
        (2 * mgsPaddedAccumulatedCoeff fp m n) * columnFrob A j := by
    intro j
    calc
      columnFrob repairedDelta j <=
          columnFrob (matMulRect m n n F dTop) j + columnFrob dBottom j := by
        simpa [repairedDelta] using
          columnFrob_add_le (matMulRect m n n F dTop) dBottom j
      _ <= 1 * columnFrob dTop j + columnFrob dBottom j :=
        add_le_add
          (columnFrob_matMulRect_le_rectOpNorm2_mul_columnFrob
            F dTop hdata.map_bound j) le_rfl
      _ <= 1 * (mgsPaddedAccumulatedCoeff fp m n * columnFrob A j) +
          mgsPaddedAccumulatedCoeff fp m n * columnFrob A j :=
        add_le_add
          (mul_le_mul_of_nonneg_left (htopCol j) (by norm_num))
          (hbottomCol j)
      _ = (2 * mgsPaddedAccumulatedCoeff fp m n) * columnFrob A j := by ring
  have hrepairNorm : rectOpNorm2Le repairedDelta (frobNormRect repairedDelta) :=
    rectOpNorm2Le_of_frobNormRect_le repairedDelta le_rfl
  obtain ⟨Qout, dAout, hQout, hfactor, _hnorm, houtCol⟩ :=
    mgsProblem1912_repair_of_correctionMap
      (A := A) (P21 := mgsPaddedEconomyQ Qfull)
      (Q := Qrepair) (dTop := dTop)
      (R := fl_modifiedGramSchmidtR fp A)
      (dBottom := dBottom) (F := F)
      (eta2 := frobNormRect repairedDelta)
      (c3 := 2 * mgsPaddedAccumulatedCoeff fp m n) (u := 1)
      hbottom hmap (by simpa [repairedDelta] using hrepairNorm)
      (by simpa [repairedDelta] using hrepairCol)
  refine ⟨Qout, dAout, hQout, hfactor, ?_⟩
  intro j
  simpa using houtCol j

/-! ## Dimension-only growth and literal product residual -/

/-- A deliberately conservative contraction-free bound for projection
removal along a unit vector.  The factor two is sufficient for an honest
dimension-only stage-growth envelope. -/
theorem gsProjectAway_norm_le_two_mul {m : Nat}
    (v q : Fin m -> Real) (hq : vecNorm2 q = 1) :
    vecNorm2 (gsProjectAway v q) <= 2 * vecNorm2 v := by
  have hdecomp : gsProjectAway v q =
      fun i => v i + (-gsDot q v) * q i := by
    funext i
    unfold gsProjectAway
    ring
  rw [hdecomp]
  have hdot := abs_vecInnerProduct_le_vecNorm2_mul q v
  calc
    vecNorm2 (fun i => v i + (-gsDot q v) * q i) <=
        vecNorm2 v + vecNorm2 (fun i => (-gsDot q v) * q i) :=
      vecNorm2_add_le _ _
    _ = vecNorm2 v + |gsDot q v| * vecNorm2 q := by
      rw [vecNorm2_smul, abs_neg]
    _ <= vecNorm2 v + (vecNorm2 q * vecNorm2 v) * vecNorm2 q :=
      add_le_add le_rfl
        (mul_le_mul_of_nonneg_right hdot (vecNorm2_nonneg q))
    _ = 2 * vecNorm2 v := by rw [hq]; ring

def mgsStageGrowthCoeff (fp : FPModel) (m : Nat) : Real :=
  2 + mgsPaddedBottomStepCoeff fp m

theorem mgsStageGrowthCoeff_nonneg (fp : FPModel) (m : Nat)
    (hm : gammaValid fp (2 * (m + 1))) :
    0 <= mgsStageGrowthCoeff fp m := by
  unfold mgsStageGrowthCoeff
  exact add_nonneg (by norm_num) (mgsPaddedBottomStepCoeff_nonneg fp m hm)

/-- One actual later-column MGS update grows its Euclidean norm by at most a
dimension/model-only factor. -/
theorem flMGSVectors_succ_later_norm_le_growth {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (hm : gammaValid fp (2 * (m + 1)))
    (k j : Fin n) (hkj : k < j)
    (hk : 0 < vecNorm2 (flMGSVectors fp A k.val k)) :
    vecNorm2 (flMGSVectors fp A (k.val + 1) j) <=
      mgsStageGrowthCoeff fp m * vecNorm2 (flMGSVectors fp A k.val j) := by
  let v := flMGSVectors fp A k.val j
  let q := mgsExactNormalized (flMGSVectors fp A k.val k)
  let e : Fin m -> Real := fun i =>
    flMGSVectors fp A (k.val + 1) j i - gsProjectAway v q i
  have hq : vecNorm2 q = 1 := by
    simpa [q] using mgsExactNormalized_norm_eq_one
      (flMGSVectors fp A k.val k) hk
  have he : vecNorm2 e <=
      mgsPaddedBottomStepCoeff fp m * vecNorm2 v := by
    simpa [e, q, v] using
      flMGSVectors_succ_later_exact_normalized_norm_le fp A hm k j hkj hk
  have hsplit : flMGSVectors fp A (k.val + 1) j =
      fun i => e i + gsProjectAway v q i := by
    funext i
    simp [e]
  rw [hsplit]
  calc
    vecNorm2 (fun i => e i + gsProjectAway v q i) <=
        vecNorm2 e + vecNorm2 (gsProjectAway v q) := vecNorm2_add_le _ _
    _ <= mgsPaddedBottomStepCoeff fp m * vecNorm2 v +
        2 * vecNorm2 v :=
      add_le_add he (gsProjectAway_norm_le_two_mul v q hq)
    _ = mgsStageGrowthCoeff fp m * vecNorm2 v := by
      simp [mgsStageGrowthCoeff]
      ring

/-- Geometric dimension-only envelope for every active stored column in the
literal rounded MGS trace. -/
theorem flMGSVectors_stage_norm_le_growth_pow {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (hm : gammaValid fp (2 * (m + 1)))
    (hpivot : forall k : Fin n,
      Ne (fl_modifiedGramSchmidtR fp A k k) 0)
    (j : Fin n) (t : Nat) (ht : t <= j.val) :
    vecNorm2 (flMGSVectors fp A t j) <=
      (mgsStageGrowthCoeff fp m) ^ t * vecNorm2 (fun i => A i j) := by
  induction t with
  | zero =>
      change vecNorm2 (fun i => A i j) <=
        (mgsStageGrowthCoeff fp m) ^ 0 * vecNorm2 (fun i => A i j)
      simp
  | succ t ih =>
      have htj : t < j.val := by omega
      have htn : t < n := lt_trans htj j.isLt
      let k : Fin n := Fin.mk t htn
      have hkj : k < j := by simpa [k] using htj
      have hkpos : 0 < vecNorm2 (flMGSVectors fp A k.val k) :=
        flMGSVectors_pivot_norm_pos_of_diag_ne_zero fp A hm k (hpivot k)
      have hstep := flMGSVectors_succ_later_norm_le_growth
        fp A hm k j hkj hkpos
      have hgrowth0 := mgsStageGrowthCoeff_nonneg fp m hm
      have hih := ih (by omega)
      calc
        vecNorm2 (flMGSVectors fp A (Nat.succ t) j) <=
            mgsStageGrowthCoeff fp m * vecNorm2 (flMGSVectors fp A t j) := by
          simpa [k, Nat.succ_eq_add_one] using hstep
        _ <= mgsStageGrowthCoeff fp m *
            ((mgsStageGrowthCoeff fp m) ^ t * vecNorm2 (fun i => A i j)) :=
          mul_le_mul_of_nonneg_left hih hgrowth0
        _ = (mgsStageGrowthCoeff fp m) ^ (Nat.succ t) *
            vecNorm2 (fun i => A i j) := by
          rw [pow_succ]
          ring

def mgsReconstructionStepCoeff (fp : FPModel) (m : Nat) : Real :=
  mgsUpdateLocalNormCap fp m +
    gamma fp m * (mgsComputedQNormCap fp m) ^ 2

theorem mgsReconstructionStepCoeff_nonneg (fp : FPModel) (m : Nat)
    (hm : gammaValid fp (2 * (m + 1))) :
    0 <= mgsReconstructionStepCoeff fp m := by
  have hm0 : gammaValid fp m := gammaValid_mono fp (by omega) hm
  have hgamma0 := gamma_nonneg fp hm0
  have hbottom0 := mgsPaddedBottomStepCoeff_nonneg fp m hm
  have heps0 := mgsNormalizationEps_nonneg fp m hm
  have hcap0 : 0 <= mgsComputedQNormCap fp m := by
    simp [mgsComputedQNormCap]
    linarith
  have hupdate0 : 0 <= mgsUpdateLocalNormCap fp m := by
    have hK0 : 0 <=
        (gamma fp m * (1 + fp.u) + fp.u) * (1 + fp.u) + fp.u := by
      exact add_nonneg
        (mul_nonneg
          (add_nonneg
            (mul_nonneg hgamma0 (add_nonneg zero_le_one fp.u_nonneg))
            fp.u_nonneg)
          (add_nonneg zero_le_one fp.u_nonneg)) fp.u_nonneg
    unfold mgsUpdateLocalNormCap
    exact add_nonneg fp.u_nonneg (mul_nonneg hK0 (sq_nonneg _))
  unfold mgsReconstructionStepCoeff
  exact add_nonneg hupdate0 (mul_nonneg hgamma0 (sq_nonneg _))

/-- Normwise reconstruction defect of one actual strict-upper MGS update. -/
theorem flMGSVectors_step_reconstruction_norm_le {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (hm : gammaValid fp (2 * (m + 1)))
    (hpivot : forall k : Fin n,
      Ne (fl_modifiedGramSchmidtR fp A k k) 0)
    (k j : Fin n) (hkj : k < j) :
    vecNorm2 (fun i =>
      (flMGSVectors fp A (k.val + 1) j i +
        fl_modifiedGramSchmidtQ fp A i k *
          fl_modifiedGramSchmidtR fp A k j) -
        flMGSVectors fp A k.val j i) <=
      mgsReconstructionStepCoeff fp m *
        vecNorm2 (flMGSVectors fp A k.val j) := by
  let Qhat := fl_modifiedGramSchmidtQ fp A
  let Rhat := fl_modifiedGramSchmidtR fp A
  let V := flMGSVectors fp A
  let qhat := gsColumn Qhat k
  let v := V k.val j
  let uerr : Fin m -> Real := fun i =>
    V (k.val + 1) j i - gsProjectAway v qhat i
  let rerr : Real := Rhat k j - gsDot qhat v
  let hstate : ModifiedGramSchmidtRoundedState fp A Qhat Rhat V :=
    fl_modifiedGramSchmidt_roundedState fp A hm hpivot
  have hm0 : gammaValid fp m := gammaValid_mono fp (by omega) hm
  have hgamma0 := gamma_nonneg fp hm0
  have hkpos := flMGSVectors_pivot_norm_pos_of_diag_ne_zero fp A hm k (hpivot k)
  have hqcap : vecNorm2 qhat <= mgsComputedQNormCap fp m := by
    simpa [qhat, Qhat, V, fl_modifiedGramSchmidtQ_col,
      mgsComputedQNormCap] using
      flMGSNormalizedColumn_norm_le fp (flMGSVectors fp A k.val) k hm hkpos
  have hupdate0 : vecNorm2 uerr <=
      mgsUpdateLocalNormCoeff fp m qhat * vecNorm2 v := by
    simpa [uerr, qhat, v, V] using hstate.update_norm_le hm0 k j hkj
  have hcap : mgsUpdateLocalNormCoeff fp m qhat <=
      mgsUpdateLocalNormCap fp m := by
    simpa [qhat, Qhat, V, fl_modifiedGramSchmidtQ_col] using
      mgsUpdateLocalNormCoeff_le_cap fp (flMGSVectors fp A k.val) k hm hkpos
  have hupdate : vecNorm2 uerr <=
      mgsUpdateLocalNormCap fp m * vecNorm2 v :=
    hupdate0.trans
      (mul_le_mul_of_nonneg_right hcap (vecNorm2_nonneg v))
  have hsum :
      (Finset.univ.sum fun r : Fin m => |qhat r| * |v r|) <=
        vecNorm2 qhat * vecNorm2 v := by
    have hcs := abs_vecInnerProduct_le_vecNorm2_mul
      (fun r : Fin m => |qhat r|) (fun r : Fin m => |v r|)
    have hs0 : 0 <= Finset.univ.sum fun r : Fin m => |qhat r| * |v r| :=
      Finset.sum_nonneg fun r _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
    simpa [abs_of_nonneg hs0, vecNorm2_abs] using hcs
  have hrerr0 : |rerr| <= gamma fp m *
      (Finset.univ.sum fun r : Fin m => |qhat r| * |v r|) := by
    simpa [rerr, Rhat, qhat, v, V] using hstate.projection k j hkj
  have hrerr : |rerr| <= gamma fp m *
      (mgsComputedQNormCap fp m * vecNorm2 v) := by
    calc
      |rerr| <= gamma fp m *
          (Finset.univ.sum fun r : Fin m => |qhat r| * |v r|) := hrerr0
      _ <= gamma fp m * (vecNorm2 qhat * vecNorm2 v) :=
        mul_le_mul_of_nonneg_left hsum hgamma0
      _ <= gamma fp m * (mgsComputedQNormCap fp m * vecNorm2 v) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hqcap (vecNorm2_nonneg v)) hgamma0
  have hrvec : vecNorm2 (fun i => qhat i * rerr) <=
      (gamma fp m * (mgsComputedQNormCap fp m) ^ 2) * vecNorm2 v := by
    calc
      vecNorm2 (fun i => qhat i * rerr) = |rerr| * vecNorm2 qhat := by
        simpa [mul_comm] using vecNorm2_smul rerr qhat
      _ <= (gamma fp m * (mgsComputedQNormCap fp m * vecNorm2 v)) *
          mgsComputedQNormCap fp m :=
        mul_le_mul hrerr hqcap (vecNorm2_nonneg qhat)
          (mul_nonneg hgamma0
            (mul_nonneg (by
              exact le_trans (vecNorm2_nonneg qhat) hqcap)
              (vecNorm2_nonneg v)))
      _ = (gamma fp m * (mgsComputedQNormCap fp m) ^ 2) * vecNorm2 v := by ring
  have hdecomp :
      (fun i => (V (k.val + 1) j i + Qhat i k * Rhat k j) - V k.val j i) =
        fun i => uerr i + qhat i * rerr := by
    funext i
    simp only [uerr, rerr, qhat, v, gsColumn, gsProjectAway]
    ring
  change vecNorm2 (fun i =>
      (V (k.val + 1) j i + Qhat i k * Rhat k j) - V k.val j i) <= _
  rw [hdecomp]
  calc
    vecNorm2 (fun i => uerr i + qhat i * rerr) <=
        vecNorm2 uerr + vecNorm2 (fun i => qhat i * rerr) :=
      vecNorm2_add_le _ _
    _ <= mgsUpdateLocalNormCap fp m * vecNorm2 v +
        (gamma fp m * (mgsComputedQNormCap fp m) ^ 2) * vecNorm2 v :=
      add_le_add hupdate hrvec
    _ = mgsReconstructionStepCoeff fp m * vecNorm2 v := by
      simp [mgsReconstructionStepCoeff]
      ring

theorem flMGS_diagonal_reconstruction_norm_le {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (hm : gammaValid fp (2 * (m + 1)))
    (hpivot : forall k : Fin n,
      Ne (fl_modifiedGramSchmidtR fp A k k) 0)
    (j : Fin n) :
    vecNorm2 (fun i =>
      fl_modifiedGramSchmidtQ fp A i j *
          fl_modifiedGramSchmidtR fp A j j -
        flMGSVectors fp A j.val j i) <=
      fp.u * vecNorm2 (flMGSVectors fp A j.val j) := by
  let hstate := fl_modifiedGramSchmidt_roundedState fp A hm hpivot
  let d : Fin m -> Real := fun i =>
    fl_modifiedGramSchmidtQ fp A i j *
        fl_modifiedGramSchmidtR fp A j j -
      flMGSVectors fp A j.val j i
  have hentry : forall i, |d i| <=
      fp.u * |flMGSVectors fp A j.val j i| := by
    intro i
    have h := hstate.diagonal_reconstruction_error hpivot j i
    simpa [d, mul_comm] using h
  calc
    vecNorm2 (fun i =>
      fl_modifiedGramSchmidtQ fp A i j *
          fl_modifiedGramSchmidtR fp A j j -
        flMGSVectors fp A j.val j i) = vecNorm2 d := by rfl
    _ <= vecNorm2 (fun i => fp.u * |flMGSVectors fp A j.val j i|) :=
      vecNorm2_le_of_abs_le _ _ hentry
    _ = fp.u * vecNorm2 (flMGSVectors fp A j.val j) := by
      rw [vecNorm2_smul, abs_of_nonneg fp.u_nonneg, vecNorm2_abs]

def mgsProductColumnCoeff (fp : FPModel) (m j : Nat) : Real :=
  fp.u * (mgsStageGrowthCoeff fp m) ^ j +
    Finset.univ.sum (fun k : Fin j =>
      mgsReconstructionStepCoeff fp m *
        (mgsStageGrowthCoeff fp m) ^ k.val)

theorem mgsProductColumnCoeff_nonneg (fp : FPModel) (m j : Nat)
    (hm : gammaValid fp (2 * (m + 1))) :
    0 <= mgsProductColumnCoeff fp m j := by
  have hg := mgsStageGrowthCoeff_nonneg fp m hm
  have hr := mgsReconstructionStepCoeff_nonneg fp m hm
  unfold mgsProductColumnCoeff
  exact add_nonneg
    (mul_nonneg fp.u_nonneg (pow_nonneg hg _))
    (Finset.sum_nonneg fun k _ => mul_nonneg hr (pow_nonneg hg _))

theorem mgs_vecNorm2_finset_sum_le {alpha : Type*} [DecidableEq alpha]
    {p : Nat} (s : Finset alpha) (x : alpha -> Fin p -> Real) :
    vecNorm2 (fun i => Finset.sum s (fun a => x a i)) <=
      Finset.sum s (fun a => vecNorm2 (x a)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [vecNorm2, vecNorm2Sq]
  | @insert a s ha ih =>
      calc
        vecNorm2 (fun i => Finset.sum (insert a s) (fun b => x b i)) =
            vecNorm2 (fun i => x a i + Finset.sum s (fun b => x b i)) := by
          congr 1
          funext i
          rw [Finset.sum_insert ha]
        _ <= vecNorm2 (x a) +
            vecNorm2 (fun i => Finset.sum s (fun b => x b i)) :=
          vecNorm2_add_le _ _
        _ <= vecNorm2 (x a) + Finset.sum s (fun b => vecNorm2 (x b)) :=
          add_le_add le_rfl ih
        _ = Finset.sum (insert a s) (fun b => vecNorm2 (x b)) := by
          rw [Finset.sum_insert ha]

theorem mgs_vecNorm2_fin_sum_le {q p : Nat} (x : Fin q -> Fin p -> Real) :
    vecNorm2 (fun i => Finset.univ.sum (fun a : Fin q => x a i)) <=
      Finset.univ.sum (fun a : Fin q => vecNorm2 (x a)) := by
  exact mgs_vecNorm2_finset_sum_le (Finset.univ : Finset (Fin q)) x

/-- Literal Algorithm 19.12 product residual with a dimension/model-only
relative column coefficient. -/
theorem fl_modifiedGramSchmidt_product_residual_column_growth_bound {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (hm : gammaValid fp (2 * (m + 1)))
    (hpivot : forall k : Fin n,
      Ne (fl_modifiedGramSchmidtR fp A k k) 0)
    (j : Fin n) :
    columnFrob
        (mgsRoundedProductResidual A
          (fl_modifiedGramSchmidtQ fp A)
          (fl_modifiedGramSchmidtR fp A)) j <=
      mgsProductColumnCoeff fp m j.val * columnFrob A j := by
  let Qhat := fl_modifiedGramSchmidtQ fp A
  let Rhat := fl_modifiedGramSchmidtR fp A
  let V := flMGSVectors fp A
  let hstate : ModifiedGramSchmidtRoundedState fp A Qhat Rhat V :=
    fl_modifiedGramSchmidt_roundedState fp A hm hpivot
  let diag : Fin m -> Real := fun i => Qhat i j * Rhat j j - V j.val j i
  let step : Fin j.val -> Fin m -> Real := fun k i =>
    let kk : Fin n := Fin.castLT k (lt_trans k.isLt j.isLt)
    (V (kk.val + 1) j i + Qhat i kk * Rhat kk j) - V kk.val j i
  have hdecomp :
      (fun i => mgsRoundedProductResidual A Qhat Rhat i j) =
        fun i => diag i + Finset.univ.sum (fun k : Fin j.val => step k i) := by
    funext i
    simpa [diag, step] using hstate.product_residual_decomposition j i
  have hdiag0 : vecNorm2 diag <= fp.u * vecNorm2 (V j.val j) := by
    simpa [diag, Qhat, Rhat, V] using
      flMGS_diagonal_reconstruction_norm_le fp A hm hpivot j
  have hdiag : vecNorm2 diag <=
      (fp.u * (mgsStageGrowthCoeff fp m) ^ j.val) *
        vecNorm2 (fun i => A i j) := by
    have hgrowth := flMGSVectors_stage_norm_le_growth_pow
      fp A hm hpivot j j.val (le_refl _)
    calc
      vecNorm2 diag <= fp.u * vecNorm2 (V j.val j) := hdiag0
      _ <= fp.u * ((mgsStageGrowthCoeff fp m) ^ j.val *
          vecNorm2 (fun i => A i j)) :=
        mul_le_mul_of_nonneg_left (by simpa [V] using hgrowth) fp.u_nonneg
      _ = (fp.u * (mgsStageGrowthCoeff fp m) ^ j.val) *
          vecNorm2 (fun i => A i j) := by ring
  have hstep : forall k : Fin j.val,
      vecNorm2 (step k) <=
        (mgsReconstructionStepCoeff fp m *
          (mgsStageGrowthCoeff fp m) ^ k.val) *
            vecNorm2 (fun i => A i j) := by
    intro k
    let kk : Fin n := Fin.castLT k (lt_trans k.isLt j.isLt)
    have hlocal := flMGSVectors_step_reconstruction_norm_le
      fp A hm hpivot kk j (by
        show kk.val < j.val
        simp [kk, k.isLt])
    have hgrowth := flMGSVectors_stage_norm_le_growth_pow
      fp A hm hpivot j k.val (Nat.le_of_lt k.isLt)
    have hr0 := mgsReconstructionStepCoeff_nonneg fp m hm
    calc
      vecNorm2 (step k) <=
          mgsReconstructionStepCoeff fp m * vecNorm2 (V k.val j) := by
        simpa [step, kk, Qhat, Rhat, V] using hlocal
      _ <= mgsReconstructionStepCoeff fp m *
          ((mgsStageGrowthCoeff fp m) ^ k.val *
            vecNorm2 (fun i => A i j)) :=
        mul_le_mul_of_nonneg_left (by simpa [V] using hgrowth) hr0
      _ = (mgsReconstructionStepCoeff fp m *
          (mgsStageGrowthCoeff fp m) ^ k.val) *
            vecNorm2 (fun i => A i j) := by ring
  rw [columnFrob_eq_vecNorm2, hdecomp]
  calc
    vecNorm2 (fun i => diag i + Finset.univ.sum
        (fun k : Fin j.val => step k i)) <=
        vecNorm2 diag + vecNorm2 (fun i =>
          Finset.univ.sum (fun k : Fin j.val => step k i)) :=
      vecNorm2_add_le _ _
    _ <= vecNorm2 diag + Finset.univ.sum
        (fun k : Fin j.val => vecNorm2 (step k)) :=
      add_le_add le_rfl (mgs_vecNorm2_fin_sum_le step)
    _ <= (fp.u * (mgsStageGrowthCoeff fp m) ^ j.val) *
          vecNorm2 (fun i => A i j) +
        Finset.univ.sum (fun k : Fin j.val =>
          (mgsReconstructionStepCoeff fp m *
            (mgsStageGrowthCoeff fp m) ^ k.val) *
              vecNorm2 (fun i => A i j)) :=
      add_le_add hdiag (Finset.sum_le_sum fun k _ => hstep k)
    _ = mgsProductColumnCoeff fp m j.val * columnFrob A j := by
      rw [columnFrob_eq_vecNorm2]
      unfold mgsProductColumnCoeff
      rw [add_mul, Finset.sum_mul]

theorem frobNormRect_le_sum_columnFrob {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    frobNormRect A <= Finset.univ.sum (fun j : Fin n => columnFrob A j) := by
  have hcol0 : forall j : Fin n, 0 <= columnFrob A j :=
    fun j => columnFrob_nonneg A j
  have hsum0 : 0 <= Finset.univ.sum (fun j : Fin n => columnFrob A j) :=
    Finset.sum_nonneg fun j _ => hcol0 j
  have hsq : frobNormSqRect A <=
      (Finset.univ.sum (fun j : Fin n => columnFrob A j)) ^ 2 := by
    rw [frobNormSqRect_eq_sum_vecNorm2Sq_cols]
    simp_rw [<- vecNorm2_sq]
    rw [show (Finset.univ.sum fun j : Fin n => columnFrob A j) =
        Finset.univ.sum (fun j : Fin n => vecNorm2 (fun i => A i j)) by
      apply Finset.sum_congr rfl
      intro j _
      exact columnFrob_eq_vecNorm2 A j]
    exact Finset.sum_sq_le_sq_sum_of_nonneg
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun j : Fin n => vecNorm2 (fun i => A i j))
      (fun j _ => vecNorm2_nonneg _)
  unfold frobNormRect
  calc
    Real.sqrt (frobNormSqRect A) <=
        Real.sqrt ((Finset.univ.sum (fun j : Fin n => columnFrob A j)) ^ 2) :=
      Real.sqrt_le_sqrt hsq
    _ = Finset.univ.sum (fun j : Fin n => columnFrob A j) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hsum0]

theorem columnFrob_le_frobNormRect {m n : Nat}
    (A : Fin m -> Fin n -> Real) (j : Fin n) :
    columnFrob A j <= frobNormRect A := by
  rw [columnFrob_eq_vecNorm2]
  unfold vecNorm2 frobNormRect vecNorm2Sq frobNormSqRect
  apply Real.sqrt_le_sqrt
  rw [Finset.sum_comm]
  exact Finset.single_le_sum
    (fun k _ => Finset.sum_nonneg fun i _ => sq_nonneg (A i k))
    (Finset.mem_univ j)

def mgsProductGlobalCoeff (fp : FPModel) (m n : Nat) : Real :=
  Finset.univ.sum (fun j : Fin n => mgsProductColumnCoeff fp m j.val)

theorem mgsProductGlobalCoeff_nonneg (fp : FPModel) (m n : Nat)
    (hm : gammaValid fp (2 * (m + 1))) :
    0 <= mgsProductGlobalCoeff fp m n := by
  unfold mgsProductGlobalCoeff
  exact Finset.sum_nonneg fun j _ => mgsProductColumnCoeff_nonneg fp m j.val hm

/-- Global Frobenius form of the literal Algorithm 19.12 residual channel. -/
theorem fl_modifiedGramSchmidt_product_residual_frob_growth_bound {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (hm : gammaValid fp (2 * (m + 1)))
    (hpivot : forall k : Fin n,
      Ne (fl_modifiedGramSchmidtR fp A k k) 0) :
    frobNormRect
        (mgsRoundedProductResidual A
          (fl_modifiedGramSchmidtQ fp A)
          (fl_modifiedGramSchmidtR fp A)) <=
      mgsProductGlobalCoeff fp m n * frobNormRect A := by
  let E := mgsRoundedProductResidual A
    (fl_modifiedGramSchmidtQ fp A) (fl_modifiedGramSchmidtR fp A)
  have hcol : forall j : Fin n,
      columnFrob E j <= mgsProductColumnCoeff fp m j.val * columnFrob A j := by
    intro j
    simpa [E] using
      fl_modifiedGramSchmidt_product_residual_column_growth_bound
        fp A hm hpivot j
  have hcoeff0 : forall j : Fin n, 0 <= mgsProductColumnCoeff fp m j.val :=
    fun j => mgsProductColumnCoeff_nonneg fp m j.val hm
  calc
    frobNormRect E <= Finset.univ.sum (fun j : Fin n => columnFrob E j) :=
      frobNormRect_le_sum_columnFrob E
    _ <= Finset.univ.sum (fun j : Fin n =>
        mgsProductColumnCoeff fp m j.val * columnFrob A j) :=
      Finset.sum_le_sum fun j _ => hcol j
    _ <= Finset.univ.sum (fun j : Fin n =>
        mgsProductColumnCoeff fp m j.val * frobNormRect A) :=
      Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (columnFrob_le_frobNormRect A j) (hcoeff0 j)
    _ = mgsProductGlobalCoeff fp m n * frobNormRect A := by
      unfold mgsProductGlobalCoeff
      rw [Finset.sum_mul]

/-! ## Exact all-orders Theorem 19.13 endpoint -/

/-- Dimension-only coefficient obtained by converting the columnwise
CS/polar repair bound to a global Frobenius bound. -/
def mgsRepairGlobalCoeff (fp : FPModel) (m n : Nat) : Real :=
  (n : Real) * (2 * mgsPaddedAccumulatedCoeff fp m n)

theorem mgsRepairGlobalCoeff_nonneg (fp : FPModel) (m n : Nat)
    (hm : gammaValid fp (2 * (m + 1))) :
    0 <= mgsRepairGlobalCoeff fp m n := by
  unfold mgsRepairGlobalCoeff
  exact mul_nonneg (Nat.cast_nonneg n)
    (mul_nonneg (by norm_num) (mgsPaddedAccumulatedCoeff_nonneg fp m n hm))

/-- A columnwise repaired perturbation satisfying the literal padded-MGS
bound also satisfies the corresponding global Frobenius bound. -/
theorem mgs_repaired_perturbation_frob_bound {m n : Nat}
    (fp : FPModel) (A dA : Fin m -> Fin n -> Real)
    (hm : gammaValid fp (2 * (m + 1)))
    (hcol : forall j : Fin n,
      columnFrob dA j <=
        (2 * mgsPaddedAccumulatedCoeff fp m n) * columnFrob A j) :
    frobNormRect dA <=
      mgsRepairGlobalCoeff fp m n * frobNormRect A := by
  have hc0 : 0 <= 2 * mgsPaddedAccumulatedCoeff fp m n :=
    mul_nonneg (by norm_num) (mgsPaddedAccumulatedCoeff_nonneg fp m n hm)
  calc
    frobNormRect dA <= Finset.univ.sum (fun j : Fin n => columnFrob dA j) :=
      frobNormRect_le_sum_columnFrob dA
    _ <= Finset.univ.sum (fun j : Fin n =>
        (2 * mgsPaddedAccumulatedCoeff fp m n) * columnFrob A j) :=
      Finset.sum_le_sum fun j _ => hcol j
    _ <= Finset.univ.sum (fun _j : Fin n =>
        (2 * mgsPaddedAccumulatedCoeff fp m n) * frobNormRect A) :=
      Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (columnFrob_le_frobNormRect A j) hc0
    _ = mgsRepairGlobalCoeff fp m n * frobNormRect A := by
      simp [mgsRepairGlobalCoeff]
      ring

/-- Exact all-orders closeness radius in the literal MGS sensitivity route.
The first factor is dimension/model-only; the second is the computable
conditioning radius of the common computed `Rhat`. -/
def mgsLiteralOrthogonalityDelta {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real) : Real :=
  (mgsProductGlobalCoeff fp m n + mgsRepairGlobalCoeff fp m n) *
    (frobNormRect A *
      frobNormRect
        (nonsingInv n (fl_modifiedGramSchmidtR fp A)))

theorem mgsLiteralOrthogonalityDelta_nonneg {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (hm : gammaValid fp (2 * (m + 1))) :
    0 <= mgsLiteralOrthogonalityDelta fp A := by
  unfold mgsLiteralOrthogonalityDelta
  exact mul_nonneg
    (add_nonneg (mgsProductGlobalCoeff_nonneg fp m n hm)
      (mgsRepairGlobalCoeff_nonneg fp m n hm))
    (mul_nonneg (frobNormRect_nonneg A)
      (frobNormRect_nonneg
        (nonsingInv n (fl_modifiedGramSchmidtR fp A))))

/-- Source-labeled exact all-orders form of Higham Theorem 19.13 for the
literal rounded Algorithm 19.12 executor.

The printed `O((u*kappa)^2)` term is represented by the explicit square in
`eq19_30_orthogonality`; no asymptotic remainder is assumed.  The inverse
factor is the canonical inverse of the actual computed `Rhat`, whose
nonsingularity follows from the operational nonbreakdown hypothesis. -/
structure LiteralMGSTheorem1913ExactCertificate (m n : Nat) (fp : FPModel)
    (A : Fin m -> Fin n -> Real) : Prop where
  upper : IsUpperTrapezoidal n n (fl_modifiedGramSchmidtR fp A)
  eq19_29_product_identity : forall i j,
    A i j +
        mgsRoundedProductResidual A
          (fl_modifiedGramSchmidtQ fp A)
          (fl_modifiedGramSchmidtR fp A) i j =
      matMulRect m n n (fl_modifiedGramSchmidtQ fp A)
        (fl_modifiedGramSchmidtR fp A) i j
  eq19_29_product_frob_bound :
    frobNormRect
        (mgsRoundedProductResidual A
          (fl_modifiedGramSchmidtQ fp A)
          (fl_modifiedGramSchmidtR fp A)) <=
      mgsProductGlobalCoeff fp m n * frobNormRect A
  eq19_30_orthogonality :
    opNorm2Le
      (gramSchmidtOrthogonalityResidual
        (fl_modifiedGramSchmidtQ fp A))
      (2 * mgsLiteralOrthogonalityDelta fp A +
        (mgsLiteralOrthogonalityDelta fp A) ^ 2)
  eq19_31_repaired_factorization :
    exists (Qrepair : Fin m -> Fin n -> Real)
        (dA2 : Fin m -> Fin n -> Real),
      GramSchmidtOrthonormalColumns Qrepair /\
      (fun i j => A i j + dA2 i j) =
        matMulRect m n n Qrepair (fl_modifiedGramSchmidtR fp A) /\
      (forall j : Fin n,
        columnFrob dA2 j <=
          (2 * mgsPaddedAccumulatedCoeff fp m n) * columnFrob A j)

/-- End-to-end producer for the exact all-orders Theorem 19.13 certificate.
All three theorem channels are consequences of the literal executor.  The
only extra condition is computed-pivot nonbreakdown, which the divisions in
Algorithm 19.12 operationally require in the repository's bare `FPModel`. -/
theorem higham19_13_literal_mgs_padded_exact_closed {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (hnm : n <= m)
    (hm : gammaValid fp (2 * (m + 1)))
    (hpivot : forall k : Fin n,
      Ne (fl_modifiedGramSchmidtR fp A k k) 0) :
    LiteralMGSTheorem1913ExactCertificate m n fp A := by
  let Qhat := fl_modifiedGramSchmidtQ fp A
  let Rhat := fl_modifiedGramSchmidtR fp A
  let E := mgsRoundedProductResidual A Qhat Rhat
  let Rinv := nonsingInv n Rhat
  have hupper : IsUpperTrapezoidal n n Rhat := by
    simpa [Rhat] using fl_modifiedGramSchmidtR_upperTrapezoidal fp A
  have hdet : Matrix.det (Rhat : Matrix (Fin n) (Fin n) Real) ≠ 0 := by
    apply det_ne_zero_of_upper_triangular_diag_ne_zero n Rhat
    · intro i j hji
      exact hupper i j hji
    · intro i
      simpa [Rhat] using hpivot i
  have hRright : matMul n Rhat Rinv = idMatrix n := by
    ext i j
    exact (isInverse_nonsingInv_of_det_ne_zero n Rhat hdet).2 i j
  have hEid :
      (fun i j => A i j + E i j) = matMulRect m n n Qhat Rhat := by
    ext i j
    simp [E, mgsRoundedProductResidual]
  have hEbound : frobNormRect E <=
      mgsProductGlobalCoeff fp m n * frobNormRect A := by
    simpa [E, Qhat, Rhat] using
      fl_modifiedGramSchmidt_product_residual_frob_growth_bound
        fp A hm hpivot
  obtain ⟨Qrepair, dA2, hQrepair, hrepair, hrepairCol⟩ :=
    fl_modifiedGramSchmidt_padded_repaired_factorization
      fp A hnm hm hpivot
  have hdA2bound : frobNormRect dA2 <=
      mgsRepairGlobalCoeff fp m n * frobNormRect A :=
    mgs_repaired_perturbation_frob_bound fp A dA2 hm hrepairCol
  have hEop : rectOpNorm2Le E
      (mgsProductGlobalCoeff fp m n * frobNormRect A) :=
    rectOpNorm2Le_of_frobNormRect_le E hEbound
  have hdA2op : rectOpNorm2Le dA2
      (mgsRepairGlobalCoeff fp m n * frobNormRect A) :=
    rectOpNorm2Le_of_frobNormRect_le dA2 hdA2bound
  have hRinvop : rectOpNorm2Le Rinv (frobNormRect Rinv) :=
    rectOpNorm2Le_of_frobNormRect_le Rinv le_rfl
  have heta : 0 <=
      mgsProductGlobalCoeff fp m n * frobNormRect A +
        mgsRepairGlobalCoeff fp m n * frobNormRect A :=
    add_nonneg
      (mul_nonneg (mgsProductGlobalCoeff_nonneg fp m n hm)
        (frobNormRect_nonneg A))
      (mul_nonneg (mgsRepairGlobalCoeff_nonneg fp m n hm)
        (frobNormRect_nonneg A))
  have hclose0 :
      rectOpNorm2Le (fun i k => Qhat i k - Qrepair i k)
        ((mgsProductGlobalCoeff fp m n * frobNormRect A +
            mgsRepairGlobalCoeff fp m n * frobNormRect A) *
          frobNormRect Rinv) :=
    commonR_difference_rectOpNorm2Le_of_perturbation_bounds_mul_right_inverse
      hEid hrepair hRright hEop hdA2op hRinvop heta
  have hclose :
      rectOpNorm2Le (fun i k => Qhat i k - Qrepair i k)
        (mgsLiteralOrthogonalityDelta fp A) := by
    have hradius :
        ((mgsProductGlobalCoeff fp m n * frobNormRect A +
            mgsRepairGlobalCoeff fp m n * frobNormRect A) *
          frobNormRect Rinv) = mgsLiteralOrthogonalityDelta fp A := by
      simp [mgsLiteralOrthogonalityDelta, Rhat, Rinv]
      ring
    rw [hradius] at hclose0
    exact hclose0
  have horth :
      opNorm2Le (gramSchmidtOrthogonalityResidual Qhat)
        (2 * mgsLiteralOrthogonalityDelta fp A +
          (mgsLiteralOrthogonalityDelta fp A) ^ 2) :=
    gramSchmidtOrthogonalityResidual_opNorm2Le_of_close_orthonormal
      hQrepair hclose (mgsLiteralOrthogonalityDelta_nonneg fp A hm)
  refine
    { upper := by simpa [Rhat] using hupper
      eq19_29_product_identity := ?_
      eq19_29_product_frob_bound := ?_
      eq19_30_orthogonality := ?_
      eq19_31_repaired_factorization := ?_ }
  · intro i j
    have hij := congrFun (congrFun hEid i) j
    simpa [E, Qhat, Rhat] using hij
  · simpa [E, Qhat, Rhat] using hEbound
  · simpa [Qhat] using horth
  · exact ⟨Qrepair, dA2, hQrepair, hrepair, hrepairCol⟩

end

end NumStability
