/-
# The lower half of the Kreiss matrix theorem

Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
Chapter 18, p. 348, quotes the finite-dimensional Kreiss matrix theorem

  phi(A) <= sup_k ||A^k||_2 <= e n phi(A),

where

  phi(A) = sup_{|z|>1} (|z|-1) ||(zI-A)^{-1}||_2.

This module proves the first inequality without assuming either a resolvent
bound or the desired conclusion.  The proof is the Banach-algebra Laurent
series argument: a uniform bound on all powers makes

  sum_{k>=0} z^(-k-1) A^k

absolutely summable for every |z|>1.  The geometric identities identify its
sum with the resolvent, and summing the norm majorant gives

  (|z|-1) ||(zI-A)^{-1}|| <= M.

The final theorem packages both suprema literally as `sSup`s whenever the
power norms are bounded above.  Thus it specializes verbatim to complex
matrices with the operator 2-norm.  The dimension-dependent reverse
inequality is deliberately not claimed here.
-/

import NumStability.Analysis.PseudospectralPowerBound
import Mathlib.Analysis.Complex.Exponential

namespace NumStability

open scoped Real Topology
open Complex Metric Set

section ComplexBanachAlgebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- A genuine uniform bound for all nonnegative powers of `a`. -/
def PowerBound (a : A) (M : ℝ) : Prop :=
  ∀ k : ℕ, ‖a ^ k‖ ≤ M

/-- An honest exterior-disk Kreiss hypothesis.  Membership in the resolvent
set is included explicitly because Mathlib's totalized resolvent is zero at a
spectral point. -/
def KreissResolventBound (a : A) (K : ℝ) : Prop :=
  ∀ z : ℂ, 1 < ‖z‖ →
    z ∈ resolventSet ℂ a ∧
      (‖z‖ - 1) * ‖resolvent a z‖ ≤ K

/-- The values whose supremum is the Kreiss resolvent constant. -/
def kreissResolventValueSet (a : A) : Set ℝ :=
  {v : ℝ | ∃ z : ℂ, 1 < ‖z‖ ∧
    v = (‖z‖ - 1) * ‖resolvent a z‖}

/-- Higham's `phi(A)`, represented as the literal supremum over `|z|>1`. -/
noncomputable def kreissConstant (a : A) : ℝ :=
  sSup (kreissResolventValueSet a)

/-- The values whose supremum is `sup_k ||a^k||`. -/
def matrixPowerNormSet (a : A) : Set ℝ :=
  {v : ℝ | ∃ k : ℕ, v = ‖a ^ k‖}

/-- The literal real supremum of the norms of all powers.  The useful exact
statement below assumes that this set is bounded above. -/
noncomputable def matrixPowerNormSup (a : A) : ℝ :=
  sSup (matrixPowerNormSet a)

omit [NormedAlgebra ℂ A] [CompleteSpace A] in
lemma powerBound_nonneg {a : A} {M : ℝ} (hM : PowerBound a M) : 0 ≤ M := by
  exact (norm_nonneg (1 : A)).trans (by simpa [PowerBound] using hM 0)

omit [CompleteSpace A] in
/-- Absolute convergence of the resolvent Laurent series from a power bound. -/
theorem summable_norm_resolventLaurent_of_powerBound
    (a : A) {M : ℝ} (hM : PowerBound a M)
    {z : ℂ} (hz : 1 < ‖z‖) :
    Summable (fun k : ℕ => ‖(z ^ (k + 1))⁻¹ • a ^ k‖) := by
  have hzpos : 0 < ‖z‖ := lt_trans zero_lt_one hz
  have hq0 : 0 ≤ ‖z‖⁻¹ := inv_nonneg.mpr (le_of_lt hzpos)
  have hq1 : ‖z‖⁻¹ < 1 := inv_lt_one_of_one_lt₀ hz
  have hmajor : Summable (fun k : ℕ => M * (‖z‖⁻¹) ^ (k + 1)) := by
    have hgeom : Summable (fun k : ℕ => (‖z‖⁻¹) ^ k) :=
      summable_geometric_of_lt_one hq0 hq1
    simpa [pow_succ', mul_assoc] using
      (hgeom.mul_left (M * ‖z‖⁻¹))
  refine Summable.of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun k => ?_) hmajor
  rw [norm_smul, norm_inv, norm_pow]
  calc
    (‖z‖ ^ (k + 1))⁻¹ * ‖a ^ k‖
        ≤ (‖z‖ ^ (k + 1))⁻¹ * M :=
          mul_le_mul_of_nonneg_left (hM k) (inv_nonneg.mpr (pow_nonneg (norm_nonneg z) _))
    _ = M * (‖z‖⁻¹) ^ (k + 1) := by
      rw [inv_pow]
      ring

/-- A power bound, rather than the stronger `||a||<|z|`, suffices for
absolute convergence of the Laurent series outside the unit circle. -/
theorem summable_resolventLaurent_of_powerBound
    (a : A) {M : ℝ} (hM : PowerBound a M)
    {z : ℂ} (hz : 1 < ‖z‖) :
    Summable (fun k : ℕ => (z ^ (k + 1))⁻¹ • a ^ k) :=
  Summable.of_norm (summable_norm_resolventLaurent_of_powerBound a hM hz)

/-- The Laurent series converges to the actual resolvent for every `|z|>1`
under a uniform power bound.  In particular, invertibility of `zI-a` is a
consequence rather than a hypothesis. -/
theorem hasSum_resolventLaurent_of_powerBound
    (a : A) {M : ℝ} (hM : PowerBound a M)
    {z : ℂ} (hz : 1 < ‖z‖) :
    HasSum (fun k : ℕ => (z ^ (k + 1))⁻¹ • a ^ k) (resolvent a z) := by
  have hz0 : z ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hz
    exact (not_lt_of_ge zero_le_one) hz
  let x : A := z⁻¹ • a
  have hsumm_x : Summable (fun k : ℕ => x ^ k) := by
    have hzpos : 0 < ‖z‖ := lt_trans zero_lt_one hz
    have hq0 : 0 ≤ ‖z‖⁻¹ := inv_nonneg.mpr (le_of_lt hzpos)
    have hq1 : ‖z‖⁻¹ < 1 := inv_lt_one_of_one_lt₀ hz
    refine Summable.of_norm (Summable.of_nonneg_of_le
      (fun _ => norm_nonneg _) (fun k => ?_)
      ((summable_geometric_of_lt_one hq0 hq1).mul_left M))
    simp only [x, smul_pow, norm_smul, norm_pow, norm_inv]
    rw [mul_comm M]
    exact mul_le_mul_of_nonneg_left (hM k)
      (pow_nonneg (inv_nonneg.mpr (norm_nonneg z)) k)
  let S : A := ∑' k : ℕ, x ^ k
  have hleft : (1 - x) * S = 1 := by
    simpa [S] using hsumm_x.one_sub_mul_tsum_pow
  have hright : S * (1 - x) = 1 := by
    simpa [S] using hsumm_x.tsum_pow_mul_one_sub
  let u : Aˣ :=
    { val := 1 - x
      inv := S
      val_inv := hleft
      inv_val := hright }
  have hxunit : IsUnit (1 - x) := by
    exact ⟨u, rfl⟩
  have hinverse : Ring.inverse (1 - x) = S := by
    calc
      Ring.inverse (1 - x) = Ring.inverse (1 - x) * 1 := by rw [mul_one]
      _ = Ring.inverse (1 - x) * ((1 - x) * S) := by rw [hleft]
      _ = (Ring.inverse (1 - x) * (1 - x)) * S := by rw [mul_assoc]
      _ = S := by rw [Ring.inverse_mul_cancel _ hxunit, one_mul]
  have hseries_x : HasSum (fun k : ℕ => x ^ k) S := by
    exact hsumm_x.hasSum
  have hscaled : HasSum (fun k : ℕ => z⁻¹ • x ^ k) (z⁻¹ • S) :=
    hseries_x.const_smul z⁻¹
  have hterms : (fun k : ℕ => z⁻¹ • x ^ k) =
      (fun k : ℕ => (z ^ (k + 1))⁻¹ • a ^ k) := by
    funext k
    simp only [x, smul_pow, smul_smul, ← inv_pow, ← pow_succ']
  have hres : resolvent a z = z⁻¹ • Ring.inverse (1 - x) := by
    have key := @spectrum.units_smul_resolvent_self ℂ A _ _ _ (Units.mk0 z hz0) a
    rw [Units.smul_def, Units.val_mk0, Units.smul_def, Units.val_inv_eq_inv_val,
      Units.val_mk0] at key
    have hone : resolvent x (1 : ℂ) = Ring.inverse (1 - x) := by
      simp only [resolvent, map_one]
    rw [← hone]
    simp only [x]
    rw [← key, inv_smul_smul₀ hz0]
  rw [hterms] at hscaled
  rwa [hres, hinverse]

/-- Norm form of the Laurent estimate. -/
theorem norm_resolvent_le_div_sub_one_of_powerBound
    (a : A) {M : ℝ} (hM : PowerBound a M)
    {z : ℂ} (hz : 1 < ‖z‖) :
    ‖resolvent a z‖ ≤ M / (‖z‖ - 1) := by
  have hsum := hasSum_resolventLaurent_of_powerBound a hM hz
  have hnormSumm : Summable
      (fun k : ℕ => ‖(z ^ (k + 1))⁻¹ • a ^ k‖) :=
    summable_norm_resolventLaurent_of_powerBound a hM hz
  calc
    ‖resolvent a z‖ = ‖∑' k : ℕ, (z ^ (k + 1))⁻¹ • a ^ k‖ := by
      rw [hsum.tsum_eq]
    _ ≤ ∑' k : ℕ, ‖(z ^ (k + 1))⁻¹ • a ^ k‖ :=
      norm_tsum_le_tsum_norm hnormSumm
    _ ≤ ∑' k : ℕ, M * (‖z‖⁻¹) ^ (k + 1) := by
      apply Summable.tsum_le_tsum
      · intro k
        rw [norm_smul, norm_inv, norm_pow]
        calc
          (‖z‖ ^ (k + 1))⁻¹ * ‖a ^ k‖
              ≤ (‖z‖ ^ (k + 1))⁻¹ * M :=
                mul_le_mul_of_nonneg_left (hM k)
                  (inv_nonneg.mpr (pow_nonneg (norm_nonneg z) _))
          _ = M * (‖z‖⁻¹) ^ (k + 1) := by rw [inv_pow]; ring
      · exact hnormSumm
      · have hzpos : 0 < ‖z‖ := lt_trans zero_lt_one hz
        have hq0 : 0 ≤ ‖z‖⁻¹ := inv_nonneg.mpr (le_of_lt hzpos)
        have hq1 : ‖z‖⁻¹ < 1 := inv_lt_one_of_one_lt₀ hz
        simpa [pow_succ', mul_assoc] using
          ((summable_geometric_of_lt_one hq0 hq1).mul_left (M * ‖z‖⁻¹))
    _ = M / (‖z‖ - 1) := by
      have hzpos : 0 < ‖z‖ := lt_trans zero_lt_one hz
      have hq0 : 0 ≤ ‖z‖⁻¹ := inv_nonneg.mpr (le_of_lt hzpos)
      have hq1 : ‖z‖⁻¹ < 1 := inv_lt_one_of_one_lt₀ hz
      rw [show (∑' k : ℕ, M * (‖z‖⁻¹) ^ (k + 1)) =
          M * ‖z‖⁻¹ * (1 - ‖z‖⁻¹)⁻¹ by
        calc
          (∑' k : ℕ, M * (‖z‖⁻¹) ^ (k + 1)) =
              ∑' k : ℕ, (M * ‖z‖⁻¹) * (‖z‖⁻¹) ^ k := by
                congr 1
                funext k
                rw [pow_succ]
                ring
          _ = (M * ‖z‖⁻¹) * (∑' k : ℕ, (‖z‖⁻¹) ^ k) :=
                tsum_mul_left
          _ = M * ‖z‖⁻¹ * (1 - ‖z‖⁻¹)⁻¹ := by
                rw [tsum_geometric_of_lt_one hq0 hq1]]
      field_simp [ne_of_gt hzpos, ne_of_gt (sub_pos.mpr hz)]

/-- Pointwise lower half of the Kreiss matrix theorem. -/
theorem kreissResolventValue_le_of_powerBound
    (a : A) {M : ℝ} (hM : PowerBound a M)
    {z : ℂ} (hz : 1 < ‖z‖) :
    (‖z‖ - 1) * ‖resolvent a z‖ ≤ M := by
  have hpos : 0 < ‖z‖ - 1 := sub_pos.mpr hz
  rw [mul_comm]
  exact (le_div_iff₀ hpos).mp
    (norm_resolvent_le_div_sub_one_of_powerBound a hM hz)

/-- `phi(a) <= M` for every genuine uniform power bound `M`. -/
theorem kreissConstant_le_of_powerBound
    (a : A) {M : ℝ} (hM : PowerBound a M) :
    kreissConstant a ≤ M := by
  apply csSup_le
  · refine ⟨(‖(2 : ℂ)‖ - 1) * ‖resolvent a (2 : ℂ)‖, ?_⟩
    change ∃ z : ℂ, 1 < ‖z‖ ∧
      (‖(2 : ℂ)‖ - 1) * ‖resolvent a (2 : ℂ)‖ =
        (‖z‖ - 1) * ‖resolvent a z‖
    refine ⟨2, ?_, ?_⟩
    · norm_num
    · rfl
  · intro v hv
    rcases hv with ⟨z, hz, rfl⟩
    exact kreissResolventValue_le_of_powerBound a hM hz

omit [NormedAlgebra ℂ A] [CompleteSpace A] in
/-- If the power norms have a finite real upper bound, their literal supremum
is itself a uniform power bound. -/
theorem powerBound_matrixPowerNormSup
    (a : A) (hbdd : BddAbove (matrixPowerNormSet a)) :
    PowerBound a (matrixPowerNormSup a) := by
  intro k
  apply le_csSup hbdd
  exact ⟨k, rfl⟩

/-- **Higham Chapter 18, lower Kreiss inequality** in literal supremum form:

`phi(a) <= sup_k ||a^k||`.

The boundedness premise merely states that the real-valued right-hand
supremum is finite; no resolvent estimate or target inequality is assumed. -/
theorem higham18_kreiss_lower
    (a : A) (hbdd : BddAbove (matrixPowerNormSet a)) :
    kreissConstant a ≤ matrixPowerNormSup a :=
  kreissConstant_le_of_powerBound a (powerBound_matrixPowerNormSup a hbdd)

/-! ## The contour part of the reverse direction

The following results isolate exactly the elementary part of the upper
Kreiss inequality.  They give the sharp contour estimate for every radius
`R>1`, and hence the standard `e (k+1) K` bound for each individual power.
The genuinely finite-dimensional step that replaces `k+1` by the matrix
dimension for all later powers is separate and is not assumed here.
-/

omit [CompleteSpace A] in
lemma kreissResolventBound_nonneg [Nontrivial A]
    {a : A} {K : ℝ} (hK : KreissResolventBound a K) : 0 ≤ K := by
  have h := (hK (2 : ℂ) (by norm_num)).2
  exact (mul_nonneg (sub_nonneg.mpr (by norm_num)) (norm_nonneg _)).trans h

/-- Cauchy's power representation on every circle of radius `R>1`, derived
from the exterior-disk resolvent premise by deformation from a larger circle.
No representation is supplied by the caller. -/
theorem pow_eq_two_pi_I_inv_smul_circleIntegral_of_kreissResolventBound
    (a : A) {K R : ℝ} (hK : KreissResolventBound a K) (hR : 1 < R)
    (k : ℕ) :
    a ^ k = (2 * Real.pi * I : ℂ)⁻¹ •
      ∮ z in C(0, R), z ^ k • resolvent a z := by
  let Rbig : ℝ := max R (‖a‖ + 1)
  have hRpos : 0 < R := zero_lt_one.trans hR
  have hRle : R ≤ Rbig := le_max_left _ _
  have haRbig : ‖a‖ < Rbig :=
    (lt_add_one ‖a‖).trans_le (le_max_right _ _)
  have hannulus : closedBall (0 : ℂ) Rbig \ ball 0 R ⊆
      resolventSet ℂ a := by
    intro z hz
    have hRz : R ≤ ‖z‖ := by
      have hznot : z ∉ ball (0 : ℂ) R := hz.2
      simpa [mem_ball, dist_zero_right, not_lt] using hznot
    exact (hK z (hR.trans_le hRz)).1
  have hcont : ContinuousOn (fun z : ℂ => z ^ k • resolvent a z)
      (closedBall (0 : ℂ) Rbig \ ball 0 R) :=
    (continuous_pow k).continuousOn.smul
      ((resolvent_continuousOn a).mono hannulus)
  have hdiff : ∀ z ∈
      (ball (0 : ℂ) Rbig \ closedBall 0 R) \ (∅ : Set ℂ),
      DifferentiableAt ℂ (fun w : ℂ => w ^ k • resolvent a w) z := by
    intro z hz
    have hRz : R < ‖z‖ := by
      have hznot : z ∉ closedBall (0 : ℂ) R := hz.1.2
      simpa [mem_closedBall, dist_zero_right, not_le] using hznot
    exact (differentiable_pow k z).smul
      (resolvent_differentiableAt a (hK z (hR.trans hRz)).1)
  have hcircle :
      (∮ z in C(0, Rbig), z ^ k • resolvent a z) =
        ∮ z in C(0, R), z ^ k • resolvent a z :=
    Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
      hRpos hRle (s := (∅ : Set ℂ)) Set.countable_empty hcont hdiff
  calc
    a ^ k = (2 * Real.pi * I : ℂ)⁻¹ •
        ∮ z in C(0, Rbig), z ^ k • resolvent a z :=
      pow_eq_two_pi_I_inv_smul_circleIntegral a k haRbig
    _ = (2 * Real.pi * I : ℂ)⁻¹ •
        ∮ z in C(0, R), z ^ k • resolvent a z := by rw [hcircle]

/-- The direct contour estimate behind the upper Kreiss theorem:

`||a^k|| <= K R^(k+1)/(R-1)` for every `R>1`. -/
theorem norm_pow_le_kreissResolventBound_circle [Nontrivial A]
    (a : A) {K R : ℝ} (hK : KreissResolventBound a K) (hR : 1 < R)
    (k : ℕ) :
    ‖a ^ k‖ ≤ K * R ^ (k + 1) / (R - 1) := by
  have hRpos : 0 ≤ R := (zero_lt_one.trans hR).le
  have hsubpos : 0 < R - 1 := sub_pos.mpr hR
  have hC : ∀ z ∈ sphere (0 : ℂ) R,
      ‖z ^ k • resolvent a z‖ ≤ R ^ k * (K / (R - 1)) := by
    intro z hz
    have hznorm : ‖z‖ = R := by
      simpa [mem_sphere, dist_zero_right] using hz
    have hres : ‖resolvent a z‖ ≤ K / (R - 1) := by
      apply (le_div_iff₀ hsubpos).2
      rw [mul_comm]
      rw [← hznorm]
      exact (hK z (by simpa [hznorm] using hR)).2
    rw [norm_smul, norm_pow, hznorm]
    exact mul_le_mul_of_nonneg_left hres (pow_nonneg hRpos k)
  rw [pow_eq_two_pi_I_inv_smul_circleIntegral_of_kreissResolventBound
    a hK hR k]
  have hML := norm_two_pi_I_inv_smul_circleIntegral_pow_smul_resolvent_le
    a 0 k hRpos hC
  calc
    ‖(2 * Real.pi * I : ℂ)⁻¹ •
        ∮ z in C(0, R), z ^ k • resolvent a z‖
        ≤ R * (R ^ k * (K / (R - 1))) := hML
    _ = K * R ^ (k + 1) / (R - 1) := by
      rw [pow_succ]
      ring

/-- The optimized elementary consequence of the contour argument.  This is
the full upper Kreiss estimate for powers `k<n`; extending it uniformly to
all `k` with `n` in place of `k+1` is the deep finite-dimensional step. -/
theorem norm_pow_le_exp_mul_succ_of_kreissResolventBound [Nontrivial A]
    (a : A) {K : ℝ} (hK : KreissResolventBound a K) (k : ℕ) :
    ‖a ^ k‖ ≤ Real.exp 1 * (k + 1) * K := by
  let m : ℝ := (k + 1 : ℕ)
  have hm : 0 < m := by positivity
  let R : ℝ := 1 + m⁻¹
  have hR : 1 < R := by
    dsimp [R]
    exact lt_add_of_pos_right _ (inv_pos.mpr hm)
  have hraw := norm_pow_le_kreissResolventBound_circle a hK hR k
  have hK0 : 0 ≤ K := kreissResolventBound_nonneg hK
  have hbase : R ≤ Real.exp (m⁻¹) := by
    dsimp [R]
    simpa [add_comm] using Real.add_one_le_exp m⁻¹
  have hR0 : 0 ≤ R := (zero_lt_one.trans hR).le
  have hexp0 : 0 ≤ Real.exp (m⁻¹) := Real.exp_pos _ |>.le
  have hpow : R ^ (k + 1) ≤ Real.exp 1 := by
    calc
      R ^ (k + 1) ≤ (Real.exp (m⁻¹)) ^ (k + 1) :=
        pow_le_pow_left₀ hR0 hbase _
      _ = Real.exp 1 := by
        rw [← Real.exp_nat_mul]
        congr 1
        dsimp [m]
        field_simp
  calc
    ‖a ^ k‖ ≤ K * R ^ (k + 1) / (R - 1) := hraw
    _ = (k + 1 : ℕ) * (K * R ^ (k + 1)) := by
      dsimp [R, m]
      field_simp
      ring
    _ ≤ (k + 1 : ℕ) * (K * Real.exp 1) := by
      gcongr
    _ = Real.exp 1 * (k + 1) * K := by
      push_cast
      ring

/-- Finite-horizon form of the printed upper bound: every one of the first
`n` powers satisfies `||a^k|| <= e n K`. -/
theorem norm_pow_le_exp_mul_dim_of_lt_of_kreissResolventBound [Nontrivial A]
    (a : A) {K : ℝ} (hK : KreissResolventBound a K)
    {k n : ℕ} (hk : k < n) :
    ‖a ^ k‖ ≤ Real.exp 1 * n * K := by
  have hsucc : (k + 1 : ℕ) ≤ n := hk
  calc
    ‖a ^ k‖ ≤ Real.exp 1 * (k + 1) * K :=
      norm_pow_le_exp_mul_succ_of_kreissResolventBound a hK k
    _ ≤ Real.exp 1 * n * K := by
      gcongr
      · exact kreissResolventBound_nonneg hK
      · exact_mod_cast hsucc

omit [CompleteSpace A] in
/-- The literal supremum `phi(a)` supplies the exterior Kreiss bound once the
exterior disk is known to lie in the resolvent set and its value set is
bounded. -/
theorem kreissResolventBound_kreissConstant
    (a : A)
    (hres : ∀ z : ℂ, 1 < ‖z‖ → z ∈ resolventSet ℂ a)
    (hbdd : BddAbove (kreissResolventValueSet a)) :
    KreissResolventBound a (kreissConstant a) := by
  intro z hz
  refine ⟨hres z hz, ?_⟩
  apply le_csSup hbdd
  exact ⟨z, hz, rfl⟩

/-- Literal-`phi` finite-horizon upper endpoint.  For an `n`-dimensional
matrix this proves the printed `e n phi(A)` estimate for every `k<n`; the
remaining `k≥n` reduction is precisely the unformalized deep step of the
finite-dimensional Kreiss theorem. -/
theorem higham18_kreiss_upper_first_dim [Nontrivial A]
    (a : A)
    (hres : ∀ z : ℂ, 1 < ‖z‖ → z ∈ resolventSet ℂ a)
    (hbdd : BddAbove (kreissResolventValueSet a))
    {k n : ℕ} (hk : k < n) :
    ‖a ^ k‖ ≤ Real.exp 1 * n * kreissConstant a :=
  norm_pow_le_exp_mul_dim_of_lt_of_kreissResolventBound a
    (kreissResolventBound_kreissConstant a hres hbdd) hk

end ComplexBanachAlgebra

end NumStability
