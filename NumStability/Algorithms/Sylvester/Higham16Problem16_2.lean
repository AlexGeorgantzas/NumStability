-- Algorithms/Sylvester/Higham16Problem16_2.lean
--
-- Higham, 2nd ed., Problem 16.2: the exponential-integral representation
-- for Sylvester equations and the positive-definite Lyapunov corollary.

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Hermitian

namespace NumStability

open Filter MeasureTheory Set Topology
open scoped ComplexOrder Matrix Pointwise
open NormedSpace

set_option backward.isDefEq.respectTransparency false

section SylvesterIntegral

variable {n : Nat}

abbrev Higham16CMatrix (n : Nat) := CStarMatrix (Fin n) (Fin n) Complex

/-- The integrand `exp(t A) C exp(t B)` in Higham's Problem 16.2.

The theorem is stated over complex matrices; the printed real theorem is the
real-entry special case.  Using `CStarMatrix` supplies a canonical Banach
algebra norm without choosing an arbitrary norm on Mathlib's bare `Matrix`
type. -/
noncomputable def higham16Problem16_2Kernel
    (A B C : Higham16CMatrix n) (t : Real) : Higham16CMatrix n :=
  exp (t • A) * C * exp (t • B)

/-- Higham's candidate `- integral_0^infinity exp(t A) C exp(t B) dt`. -/
noncomputable def higham16Problem16_2Integral
    (A B C : Higham16CMatrix n) : Higham16CMatrix n :=
  -∫ t in Ioi (0 : Real), higham16Problem16_2Kernel A B C t

/-- Precise form of the phrase in Problem 16.2 that the exponential integral
"exists for all C".  Bochner integrability is required for every matrix right
hand side. -/
def Higham16ExponentialProductIntegrable
    (A B : Higham16CMatrix n) : Prop :=
  ∀ C : Higham16CMatrix n,
    IntegrableOn (higham16Problem16_2Kernel A B C) (Ioi (0 : Real))

/-- Differential identity from the hint to Problem 16.2, in the form used by
the fundamental theorem of calculus. -/
theorem higham16_problem16_2_kernel_hasDerivAt
    (A B C : Higham16CMatrix n) (t : Real) :
    HasDerivAt (higham16Problem16_2Kernel A B C)
      (A * higham16Problem16_2Kernel A B C t +
        higham16Problem16_2Kernel A B C t * B) t := by
  have hA := hasDerivAt_exp_smul_const' A t
  have hB := hasDerivAt_exp_smul_const B t
  simpa only [higham16Problem16_2Kernel, mul_assoc] using
    (hA.mul_const C).mul hB

/-- The same differential identity factored through the Sylvester right-hand
side.  This is the form used for uniqueness of a homogeneous solution. -/
theorem higham16_problem16_2_kernel_hasDerivAt_factored
    (A B C : Higham16CMatrix n) (t : Real) :
    HasDerivAt (higham16Problem16_2Kernel A B C)
      (exp (t • A) * (A * C + C * B) * exp (t • B)) t := by
  have hA := hasDerivAt_exp_smul_const A t
  have hB := hasDerivAt_exp_smul_const' B t
  simpa only [higham16Problem16_2Kernel, mul_assoc, mul_add, add_mul] using
    (hA.mul_const C).mul hB

private theorem higham16_problem16_2_kernel_deriv_integrableOn
    (A B C : Higham16CMatrix n)
    (hInt : IntegrableOn (higham16Problem16_2Kernel A B C) (Ioi (0 : Real))) :
    IntegrableOn
      (fun t => A * higham16Problem16_2Kernel A B C t +
        higham16Problem16_2Kernel A B C t * B)
      (Ioi (0 : Real)) := by
  have hleft : IntegrableOn
      (fun t => A * higham16Problem16_2Kernel A B C t) (Ioi (0 : Real)) :=
    hInt.const_mul A
  have hright : IntegrableOn
      (fun t => higham16Problem16_2Kernel A B C t * B) (Ioi (0 : Real)) :=
    hInt.mul_const B
  change Integrable
    (fun t => A * higham16Problem16_2Kernel A B C t +
      higham16Problem16_2Kernel A B C t * B)
    (volume.restrict (Ioi (0 : Real)))
  exact Integrable.add'' (ε' := Higham16CMatrix n)
    (μ := volume.restrict (Ioi (0 : Real))) hleft hright

/-- A convergent exponential kernel tends to zero at infinity.  This is proved,
not assumed: the kernel and, by bounded left/right multiplication, its
derivative are both integrable on the half-line. -/
theorem higham16_problem16_2_kernel_tendsto_zero
    (A B C : Higham16CMatrix n)
    (hInt : IntegrableOn (higham16Problem16_2Kernel A B C) (Ioi (0 : Real))) :
    Tendsto (higham16Problem16_2Kernel A B C) atTop (𝓝 0) := by
  apply tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi
    (f' := fun t => A * higham16Problem16_2Kernel A B C t +
      higham16Problem16_2Kernel A B C t * B)
  · intro t ht
    exact higham16_problem16_2_kernel_hasDerivAt A B C t
  · exact higham16_problem16_2_kernel_deriv_integrableOn A B C hInt
  · exact hInt

/-- Problem 16.2, existence half: whenever the displayed integral is Bochner
integrable, it solves `A X + X B = C`. -/
theorem higham16_problem16_2_integral_solves
    (A B C : Higham16CMatrix n)
    (hInt : IntegrableOn (higham16Problem16_2Kernel A B C) (Ioi (0 : Real))) :
    A * higham16Problem16_2Integral A B C +
        higham16Problem16_2Integral A B C * B = C := by
  let F := higham16Problem16_2Kernel A B C
  let F' := fun t => A * F t + F t * B
  have hDeriv : ∀ t ∈ Ici (0 : Real), HasDerivAt F (F' t) t := by
    intro t ht
    exact higham16_problem16_2_kernel_hasDerivAt A B C t
  have hDerivInt : IntegrableOn F' (Ioi (0 : Real)) :=
    higham16_problem16_2_kernel_deriv_integrableOn A B C hInt
  have hZero : Tendsto F atTop (𝓝 0) :=
    higham16_problem16_2_kernel_tendsto_zero A B C hInt
  have hFTC : (∫ t in Ioi (0 : Real), F' t) = -C := by
    have h := integral_Ioi_of_hasDerivAt_of_tendsto' hDeriv hDerivInt hZero
    simpa [F, F', higham16Problem16_2Kernel] using h
  rw [higham16Problem16_2Integral]
  change A * (-(∫ t in Ioi (0 : Real), F t)) +
      (-(∫ t in Ioi (0 : Real), F t)) * B = C
  rw [mul_neg, neg_mul, ← neg_add]
  have hleft :
      A * (∫ t in Ioi (0 : Real), F t) =
        ∫ t in Ioi (0 : Real), A * F t := by
    symm
    exact integral_const_mul_of_integrable hInt
  have hright :
      (∫ t in Ioi (0 : Real), F t) * B =
        ∫ t in Ioi (0 : Real), F t * B := by
    symm
    exact integral_mul_const_of_integrable hInt
  rw [hleft, hright]
  rw [← MeasureTheory.integral_add (hInt.const_mul A) (hInt.mul_const B)]
  change -(∫ t in Ioi (0 : Real), F' t) = C
  rw [hFTC, neg_neg]

/-- Uniqueness bridge for a fixed equation.  It is enough that the exponential
kernel for the difference of the two candidates is integrable. -/
theorem higham16_problem16_2_solution_unique_of_difference_integrable
    (A B C X Y : Higham16CMatrix n)
    (hX : A * X + X * B = C) (hY : A * Y + Y * B = C)
    (hInt : IntegrableOn (higham16Problem16_2Kernel A B (X - Y)) (Ioi (0 : Real))) :
    X = Y := by
  let D := X - Y
  have hHom : A * D + D * B = 0 := by
    dsimp [D]
    calc
      A * (X - Y) + (X - Y) * B =
          (A * X + X * B) - (A * Y + Y * B) := by
            rw [mul_sub, sub_mul]
            abel
      _ = C - C := by rw [hX, hY]
      _ = 0 := sub_self C
  have hDerivZero : ∀ t : Real,
      HasDerivAt (higham16Problem16_2Kernel A B D) 0 t := by
    intro t
    convert higham16_problem16_2_kernel_hasDerivAt_factored A B D t using 1
    simp [hHom]
  have hConst : ∀ t : Real, higham16Problem16_2Kernel A B D t = D := by
    intro t
    have hdiff : Differentiable Real (higham16Problem16_2Kernel A B D) :=
      fun s => (hDerivZero s).differentiableAt
    have hc := is_const_of_deriv_eq_zero hdiff
      (fun s => (hDerivZero s).deriv) t 0
    simpa [higham16Problem16_2Kernel] using hc
  have hZero : Tendsto (higham16Problem16_2Kernel A B D) atTop (𝓝 0) :=
    higham16_problem16_2_kernel_tendsto_zero A B D hInt
  have hDZero : D = 0 := by
    have hConstTendsto : Tendsto (fun _ : Real => D) atTop (𝓝 0) :=
      hZero.congr' (Eventually.of_forall hConst)
    exact tendsto_nhds_unique tendsto_const_nhds hConstTendsto
  exact sub_eq_zero.mp hDZero

/-- Problem 16.2 exactly as worded: if the displayed expression exists for
all right-hand sides, it is the unique solution of `A X + X B = C`. -/
theorem higham16_problem16_2_integral_isUnique
    (A B : Higham16CMatrix n)
    (hAll : Higham16ExponentialProductIntegrable A B)
    (C : Higham16CMatrix n) :
    ∃! X : Higham16CMatrix n, A * X + X * B = C := by
  refine ⟨higham16Problem16_2Integral A B C,
    higham16_problem16_2_integral_solves A B C (hAll C), ?_⟩
  intro Y hY
  apply higham16_problem16_2_solution_unique_of_difference_integrable
    A B C Y (higham16Problem16_2Integral A B C) hY
    (higham16_problem16_2_integral_solves A B C (hAll C))
  exact hAll (Y - higham16Problem16_2Integral A B C)

/-!
### Hurwitz spectrum bridge

The source hypothesis that every eigenvalue lies in the open left half-plane
is represented by the genuine Banach-algebra spectrum.  Compactness supplies
a uniform negative real-part margin.  After a sufficiently large positive
scalar shift, the shifted spectrum lies in a disk of radius strictly smaller
than the shift.  Gelfand's formula then bounds all powers (including the
finite prefix), and the exponential series gives quantitative decay.
-/

noncomputable section

/-- A square complex matrix is Hurwitz when every point of its genuine
Banach-algebra spectrum has strictly negative real part. -/
def Higham16Hurwitz (A : Higham16CMatrix n) : Prop :=
  ∀ z ∈ spectrum Complex A, z.re < 0

private lemma higham16_normSq_add_real (z : Complex) (s : Real) :
    Complex.normSq (z + (s : Complex)) =
      ‖z‖ ^ 2 + s ^ 2 + 2 * s * z.re := by
  rw [Complex.normSq_add, Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
  simp
  ring

/-- A Hurwitz matrix admits a positive scalar shift whose spectral radius is
strictly smaller than the shift.  This is the disk estimate needed to turn
Gelfand's formula into exponential decay. -/
theorem higham16_hurwitz_exists_shift_spectralRadius_lt
    (A : Higham16CMatrix n) (hn : 0 < n) (hA : Higham16Hurwitz A) :
    ∃ s : Real, 0 < s ∧
      spectralRadius Complex
          (A + algebraMap Complex (Higham16CMatrix n) (s : Complex)) <
        ENNReal.ofReal s := by
  letI : Nontrivial (Higham16CMatrix n) := by
    let i : Fin n := ⟨0, hn⟩
    exact ⟨⟨0, 1, fun h => by
      have hii := congrArg (fun M : Higham16CMatrix n => M i i) h
      simpa using hii⟩⟩
  obtain ⟨zmax, hzmax, hmax⟩ :=
    (spectrum.isCompact A).exists_isMaxOn (spectrum.nonempty A)
      Complex.continuous_re.continuousOn
  let delta : Real := -zmax.re
  have hdelta : 0 < delta := neg_pos.mpr (hA zmax hzmax)
  let s : Real := (‖A‖ ^ 2 + 1) / (2 * delta)
  have hs : 0 < s := by
    dsimp [s]
    positivity
  refine ⟨s, hs, ?_⟩
  have hscale : 2 * s * delta = ‖A‖ ^ 2 + 1 := by
    dsimp [s]
    field_simp [ne_of_gt hdelta]
  have hall : ∀ w ∈ spectrum Complex
      (A + algebraMap Complex (Higham16CMatrix n) (s : Complex)),
      ‖w‖₊ < ⟨s, hs.le⟩ := by
    intro w hw
    have hwadd : w ∈ (spectrum Complex A : Set Complex) +
        ({(s : Complex)} : Set Complex) := by
      rw [spectrum.add_singleton_eq]
      exact hw
    rcases Set.mem_add.mp hwadd with ⟨z, hz, y, hy, hzy⟩
    have hy' : y = (s : Complex) := Set.mem_singleton_iff.mp hy
    subst y
    subst w
    rw [← NNReal.coe_lt_coe]
    change ‖z + (s : Complex)‖ < s
    apply (sq_lt_sq₀ (norm_nonneg _) hs.le).mp
    rw [Complex.sq_norm, higham16_normSq_add_real]
    have hznorm : ‖z‖ ≤ ‖A‖ := spectrum.norm_le_norm_of_mem hz
    have hzsq : ‖z‖ ^ 2 ≤ ‖A‖ ^ 2 := by
      nlinarith [norm_nonneg z, norm_nonneg A]
    have hzre : z.re ≤ zmax.re := hmax hz
    have hzre' : z.re ≤ -delta := by
      dsimp [delta]
      linarith
    nlinarith
  have hspec := spectrum.spectralRadius_lt_of_forall_lt
    (A + algebraMap Complex (Higham16CMatrix n) (s : Complex)) hall
  simpa [ENNReal.coe_nnreal_eq] using hspec

private theorem higham16_eventually_norm_pow_le_of_spectralRadius_lt
    {R : Type*} [NormedRing R] [NormedAlgebra Complex R] [CompleteSpace R]
    (a : R) {r : Real} (hr : 0 < r)
    (hspec : spectralRadius Complex a < ENNReal.ofReal r) :
    ∀ᶠ k : Nat in atTop, ‖a ^ k‖ ≤ r ^ k := by
  have hgel := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius a
  have hev : ∀ᶠ k : Nat in atTop,
      ENNReal.ofReal (‖a ^ k‖ ^ (1 / (k : Real))) < ENNReal.ofReal r :=
    hgel.eventually_lt_const hspec
  filter_upwards [hev, eventually_ge_atTop 1] with k hk hk1
  have hklt : ‖a ^ k‖ ^ (1 / (k : Real)) < r :=
    (ENNReal.ofReal_lt_ofReal_iff hr).mp hk
  have hknorm : 0 ≤ ‖a ^ k‖ := norm_nonneg _
  have hkpos : 0 < (k : Real) := by exact_mod_cast hk1
  have hroot : ‖a ^ k‖ = (‖a ^ k‖ ^ (1 / (k : Real))) ^ k := by
    rw [← Real.rpow_natCast (‖a ^ k‖ ^ (1 / (k : Real))) k,
      ← Real.rpow_mul hknorm, one_div,
      inv_mul_cancel₀ (ne_of_gt hkpos), Real.rpow_one]
  rw [hroot]
  exact pow_le_pow_left₀ (Real.rpow_nonneg hknorm _) (le_of_lt hklt) k

private theorem higham16_exists_uniform_geometric_power_bound
    {R : Type*} [NormedRing R] [NormedAlgebra Complex R] [CompleteSpace R]
    (a : R) {r : Real} (hr : 0 < r)
    (hspec : spectralRadius Complex a < ENNReal.ofReal r) :
    ∃ K : Real, 0 < K ∧ ∀ k : Nat, ‖a ^ k‖ ≤ K * r ^ k := by
  have hev := higham16_eventually_norm_pow_le_of_spectralRadius_lt a hr hspec
  rcases (eventually_atTop.1 hev) with ⟨N, hN⟩
  let K : Real := 1 + ∑ k ∈ Finset.range N, ‖a ^ k‖ / r ^ k
  have hsum_nonneg : 0 ≤ ∑ k ∈ Finset.range N, ‖a ^ k‖ / r ^ k := by
    positivity
  have hK : 0 < K := by
    dsimp [K]
    linarith
  refine ⟨K, hK, fun k => ?_⟩
  by_cases hk : k < N
  · have hterm : ‖a ^ k‖ / r ^ k ≤
        ∑ j ∈ Finset.range N, ‖a ^ j‖ / r ^ j := by
      exact Finset.single_le_sum
        (fun (j : Nat) _ =>
          div_nonneg (norm_nonneg (a ^ j)) (pow_nonneg hr.le j))
        (Finset.mem_range.mpr hk)
    have htermK : ‖a ^ k‖ / r ^ k ≤ K := by
      dsimp [K]
      linarith
    calc
      ‖a ^ k‖ = (‖a ^ k‖ / r ^ k) * r ^ k := by
        rw [div_mul_cancel₀]
        exact pow_ne_zero k hr.ne'
      _ ≤ K * r ^ k :=
        mul_le_mul_of_nonneg_right htermK (pow_nonneg hr.le k)
  · have hkN : N ≤ k := Nat.le_of_not_gt hk
    calc
      ‖a ^ k‖ ≤ r ^ k := hN k hkN
      _ ≤ K * r ^ k := by
        have hK1 : 1 ≤ K := by
          dsimp [K]
          linarith
        nlinarith [pow_nonneg hr.le k]

private theorem higham16_norm_exp_smul_le_of_uniform_power_bound
    {R : Type*} [NormedRing R] [NormedAlgebra Complex R] [CompleteSpace R]
    (a : R) {r K t : Real} (ht : 0 ≤ t)
    (hpow : ∀ k : Nat, ‖a ^ k‖ ≤ K * r ^ k) :
    ‖NormedSpace.exp (t • a)‖ ≤ K * Real.exp (r * t) := by
  have hmat := NormedSpace.exp_series_hasSum_exp' (𝕂 := Complex) (t • a)
  have hreal0 := NormedSpace.exp_series_hasSum_exp' (𝕂 := Real) (r * t)
  have hreal : HasSum
      (fun k : Nat => K * ((k.factorial : Real)⁻¹ * (r * t) ^ k))
      (K * Real.exp (r * t)) := by
    convert hreal0.mul_left K using 1 <;> simp [Real.exp_eq_exp_ℝ]
  apply hmat.norm_le_of_bounded hreal
  intro k
  calc
    ‖((k.factorial : Complex)⁻¹ • (t • a) ^ k)‖ =
        (k.factorial : Real)⁻¹ * t ^ k * ‖a ^ k‖ := by
          rw [smul_pow, norm_smul, norm_smul]
          simp [abs_of_nonneg ht]
          ring
    _ ≤ (k.factorial : Real)⁻¹ * t ^ k * (K * r ^ k) := by
      gcongr
      exact hpow k
    _ = K * ((k.factorial : Real)⁻¹ * (r * t) ^ k) := by
      rw [mul_pow]
      ring

/-- Quantitative spectral-to-decay bridge: a Hurwitz matrix exponential is
bounded by a strictly decaying scalar exponential on the nonnegative
half-line. -/
theorem higham16_hurwitz_exp_decay
    (A : Higham16CMatrix n) (hn : 0 < n) (hA : Higham16Hurwitz A) :
    ∃ K alpha : Real, 0 < K ∧ 0 < alpha ∧
      ∀ t : Real, 0 ≤ t → ‖NormedSpace.exp (t • A)‖ ≤
        K * Real.exp (-alpha * t) := by
  letI : NormedAlgebra ℚ (Higham16CMatrix n) :=
    NormedAlgebra.restrictScalars ℚ Complex (Higham16CMatrix n)
  letI : Nontrivial (Higham16CMatrix n) := by
    let i : Fin n := ⟨0, hn⟩
    exact ⟨⟨0, 1, fun h => by
      have hii := congrArg (fun M : Higham16CMatrix n => M i i) h
      simpa using hii⟩⟩
  obtain ⟨s, hs, hspecS⟩ :=
    higham16_hurwitz_exists_shift_spectralRadius_lt A hn hA
  let B : Higham16CMatrix n :=
    A + algebraMap Complex (Higham16CMatrix n) (s : Complex)
  let rho : Real := (spectralRadius Complex B).toReal
  have hrhoTop : spectralRadius Complex B ≠ ⊤ := ne_top_of_lt hspecS
  have hrhos : rho < s := by
    have h := (ENNReal.toReal_lt_toReal hrhoTop ENNReal.ofReal_ne_top).mpr hspecS
    simpa [rho, ENNReal.toReal_ofReal hs.le, B] using h
  let r : Real := (rho + s) / 2
  have hrho0 : 0 ≤ rho := ENNReal.toReal_nonneg
  have hr : 0 < r := by
    dsimp [r]
    linarith
  have hrhos' : rho < r := by
    dsimp [r]
    linarith
  have hrs : r < s := by
    dsimp [r]
    linarith
  have hspecR : spectralRadius Complex B < ENNReal.ofReal r := by
    apply (ENNReal.toReal_lt_toReal hrhoTop ENNReal.ofReal_ne_top).mp
    simpa [rho, ENNReal.toReal_ofReal hr.le] using hrhos'
  obtain ⟨K, hK, hpow⟩ :=
    higham16_exists_uniform_geometric_power_bound B hr hspecR
  refine ⟨K, s - r, hK, sub_pos.mpr hrs, fun t ht => ?_⟩
  have hBexp : ‖NormedSpace.exp (t • B)‖ ≤ K * Real.exp (r * t) :=
    higham16_norm_exp_smul_le_of_uniform_power_bound B ht hpow
  have hdecomp :
      t • A =
        algebraMap Complex (Higham16CMatrix n) ((-s * t : Real) : Complex) +
          t • B := by
    dsimp [B]
    simp only [Algebra.algebraMap_eq_smul_one]
    change (t : Complex) • A =
      (((-s * t : Real) : Complex) • (1 : Higham16CMatrix n)) +
        (t : Complex) • (A + (s : Complex) • (1 : Higham16CMatrix n))
    module
  have hcomm : Commute
      (algebraMap Complex (Higham16CMatrix n) ((-s * t : Real) : Complex))
      (t • B) := Algebra.commutes _ _
  rw [hdecomp, NormedSpace.exp_add_of_commute hcomm,
    ← NormedSpace.algebraMap_exp_comm]
  calc
    ‖algebraMap Complex (Higham16CMatrix n)
          (NormedSpace.exp (((-s * t : Real) : Complex))) *
        NormedSpace.exp (t • B)‖
        ≤ ‖algebraMap Complex (Higham16CMatrix n)
            (NormedSpace.exp (((-s * t : Real) : Complex)))‖ *
          ‖NormedSpace.exp (t • B)‖ := norm_mul_le _ _
    _ = Real.exp (-s * t) * ‖NormedSpace.exp (t • B)‖ := by
      rw [norm_algebraMap, ← Complex.exp_eq_exp_ℂ, Complex.norm_exp]
      simp
    _ ≤ Real.exp (-s * t) * (K * Real.exp (r * t)) := by
      gcongr
    _ = K * Real.exp (-(s - r) * t) := by
      rw [show Real.exp (-s * t) * (K * Real.exp (r * t)) =
          K * (Real.exp (-s * t) * Real.exp (r * t)) by ring,
        ← Real.exp_add]
      congr 1
      ring

private theorem higham16_kernel_integrable_of_exp_decay
    (A B C : Higham16CMatrix n)
    {KA KB alphaA alphaB : Real}
    (hKA : 0 < KA) (hKB : 0 < KB)
    (hAlphaA : 0 < alphaA) (hAlphaB : 0 < alphaB)
    (hA : ∀ t : Real, 0 ≤ t →
      ‖NormedSpace.exp (t • A)‖ ≤ KA * Real.exp (-alphaA * t))
    (hB : ∀ t : Real, 0 ≤ t →
      ‖NormedSpace.exp (t • B)‖ ≤ KB * Real.exp (-alphaB * t)) :
    IntegrableOn (higham16Problem16_2Kernel A B C) (Ioi (0 : Real)) := by
  let D : Real := KA * ‖C‖ * KB
  let alpha : Real := alphaA + alphaB
  have hAlpha : 0 < alpha := by
    dsimp [alpha]
    positivity
  have hEnv : IntegrableOn
      (fun t : Real => D * Real.exp (-alpha * t)) (Ioi (0 : Real)) := by
    exact (exp_neg_integrableOn_Ioi 0 hAlpha).const_mul D
  have hMeas : AEStronglyMeasurable
      (higham16Problem16_2Kernel A B C)
      (volume.restrict (Ioi (0 : Real))) := by
    apply Continuous.aestronglyMeasurable
    exact continuous_iff_continuousAt.mpr fun t =>
      (higham16_problem16_2_kernel_hasDerivAt A B C t).continuousAt
  apply hEnv.mono' hMeas
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 ≤ t := le_of_lt ht
  calc
    ‖higham16Problem16_2Kernel A B C t‖
        ≤ ‖NormedSpace.exp (t • A)‖ * ‖C‖ *
            ‖NormedSpace.exp (t • B)‖ := by
          unfold higham16Problem16_2Kernel
          exact (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (KA * Real.exp (-alphaA * t)) * ‖C‖ *
          (KB * Real.exp (-alphaB * t)) := by
        gcongr
        · exact hA t ht0
        · exact hB t ht0
    _ = D * Real.exp (-alpha * t) := by
      dsimp [D, alpha]
      rw [show KA * Real.exp (-alphaA * t) * ‖C‖ *
          (KB * Real.exp (-alphaB * t)) =
          (KA * ‖C‖ * KB) *
            (Real.exp (-alphaA * t) * Real.exp (-alphaB * t)) by ring,
        ← Real.exp_add]
      congr 1
      ring

/-- The literal spectral hypotheses on both Sylvester coefficients imply that
the exponential integral exists for every right-hand side. -/
theorem higham16_exponentialProductIntegrable_of_hurwitz
    (A B : Higham16CMatrix n) (hn : 0 < n)
    (hA : Higham16Hurwitz A) (hB : Higham16Hurwitz B) :
    Higham16ExponentialProductIntegrable A B := by
  obtain ⟨KA, alphaA, hKA, hAlphaA, hDecayA⟩ :=
    higham16_hurwitz_exp_decay A hn hA
  obtain ⟨KB, alphaB, hKB, hAlphaB, hDecayB⟩ :=
    higham16_hurwitz_exp_decay B hn hB
  intro C
  exact higham16_kernel_integrable_of_exp_decay A B C
    hKA hKB hAlphaA hAlphaB hDecayA hDecayB

/-- Taking adjoints preserves the Hurwitz condition: the spectrum is complex
conjugated and hence real parts are unchanged. -/
theorem Higham16Hurwitz.star {A : Higham16CMatrix n}
    (hA : Higham16Hurwitz A) : Higham16Hurwitz (star A) := by
  intro z hz
  rw [spectrum.map_star] at hz
  have hzA : starRingEnd Complex z ∈ spectrum Complex A := by
    simpa only [Set.mem_star] using hz
  have hre := hA (starRingEnd Complex z) hzA
  simpa using hre

/-- Problem 16.2 under its literal spectral premise: no integrability or decay
assumption remains in the public theorem. -/
theorem higham16_problem16_2_integral_isUnique_of_hurwitz
    (A B : Higham16CMatrix n) (hn : 0 < n)
    (hA : Higham16Hurwitz A) (hB : Higham16Hurwitz B)
    (C : Higham16CMatrix n) :
    ∃! X : Higham16CMatrix n, A * X + X * B = C :=
  higham16_problem16_2_integral_isUnique A B
    (higham16_exponentialProductIntegrable_of_hurwitz A B hn hA hB) C

end

/-!
### Positive-definite Lyapunov corollary

The printed corollary uses real matrices, transpose, and the spectral premise
that every eigenvalue of `A` has negative real part.  The endpoints below prove
the slightly more general complex-adjoint statement.  The preceding compact-
spectrum and Gelfand argument derives the required semigroup integrability
from that literal premise, so no target-bearing analytic assumption remains.
-/

/-- The positive-sign integral used for the Lyapunov equation
`A X + X A* = -C`. -/
noncomputable def higham16Problem16_2LyapunovKernel
    (A C : Higham16CMatrix n) (t : Real) : Higham16CMatrix n :=
  higham16Problem16_2Kernel A (star A) C t

/-- Higham's positive-definite Lyapunov candidate
`integral_0^infinity exp(t A) C exp(t A*) dt`. -/
noncomputable def higham16Problem16_2LyapunovIntegral
    (A C : Higham16CMatrix n) : Higham16CMatrix n :=
  ∫ t in Ioi (0 : Real), higham16Problem16_2LyapunovKernel A C t

/-- The analytic semigroup-integrability condition used by the Lyapunov
argument.  `higham16_lyapunovSemigroupIntegrable_of_hurwitz` below derives it
from the printed Hurwitz spectral premise. -/
def Higham16LyapunovSemigroupIntegrable (A : Higham16CMatrix n) : Prop :=
  Higham16ExponentialProductIntegrable A (star A)

noncomputable local instance higham16CMatrixFiniteDimensionalComplex :
    FiniteDimensional Complex (Higham16CMatrix n) :=
  FiniteDimensional.of_injective
    (CStarMatrix.ofMatrixL.symm.toLinearMap :
      Higham16CMatrix n →ₗ[Complex] Matrix (Fin n) (Fin n) Complex)
    CStarMatrix.ofMatrixL.symm.injective

noncomputable local instance higham16CMatrixFiniteDimensionalReal :
    FiniteDimensional Real (Higham16CMatrix n) :=
  Module.Finite.trans Complex (Higham16CMatrix n)

private noncomputable def higham16Problem16_2QuadraticComplexLinear
    (x : Fin n → Complex) : Higham16CMatrix n →ₗ[Complex] Complex where
  toFun M := ∑ i, ∑ j, star (x i) * M i j * x j
  map_add' M N := by
    simp [mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' z M := by
    simp [Finset.mul_sum, mul_assoc, mul_left_comm]

private lemma higham16_problem16_2_quadraticComplexLinear_apply
    (x : Fin n → Complex) (M : Higham16CMatrix n) :
    higham16Problem16_2QuadraticComplexLinear x M =
      star x ⬝ᵥ ((CStarMatrix.ofMatrix.symm M) *ᵥ x) := by
  simp [higham16Problem16_2QuadraticComplexLinear, Matrix.mulVec,
    dotProduct, Finset.mul_sum, mul_assoc]

private noncomputable def higham16Problem16_2QuadraticCLM
    (x : Fin n → Complex) : Higham16CMatrix n →L[Real] Real :=
  Complex.reCLM.comp
    ((higham16Problem16_2QuadraticComplexLinear x).toContinuousLinearMap.restrictScalars Real)

private lemma higham16_problem16_2_quadraticCLM_apply
    (x : Fin n → Complex) (M : Higham16CMatrix n) :
    higham16Problem16_2QuadraticCLM x M =
      (star x ⬝ᵥ ((CStarMatrix.ofMatrix.symm M) *ᵥ x)).re := by
  rw [higham16Problem16_2QuadraticCLM]
  change (higham16Problem16_2QuadraticComplexLinear x M).re = _
  rw [higham16_problem16_2_quadraticComplexLinear_apply]

/-- A Bochner integral of pointwise positive-definite complex matrices is
positive definite when the integrand is positive definite at every point.
Strictness is retained because every nonzero quadratic form is strictly
positive on a half-line of positive measure. -/
private theorem higham16_problem16_2_integral_posDef_of_pointwise
    (F : Real → Higham16CMatrix n)
    (hInt : IntegrableOn F (Ioi (0 : Real)))
    (hPD : ∀ t, Matrix.PosDef (CStarMatrix.ofMatrix.symm (F t))) :
    Matrix.PosDef
      (CStarMatrix.ofMatrix.symm (∫ t in Ioi (0 : Real), F t)) := by
  have hstarComm :
      (∫ t in Ioi (0 : Real), star (F t)) =
        star (∫ t in Ioi (0 : Real), F t) := by
    simpa using
      (ContinuousLinearMap.integral_comp_comm
        (starL' Real : Higham16CMatrix n ≃L[Real] Higham16CMatrix n).toContinuousLinearMap
        hInt)
  have hHermC :
      star (∫ t in Ioi (0 : Real), F t) =
        ∫ t in Ioi (0 : Real), F t := by
    rw [← hstarComm]
    apply integral_congr_ae
    exact Eventually.of_forall fun t => by
      change star (F t) = F t
      exact (hPD t).1
  have hHerm : Matrix.IsHermitian
      (CStarMatrix.ofMatrix.symm (∫ t in Ioi (0 : Real), F t)) := by
    exact hHermC
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hHerm ?_
  intro x hx
  apply Complex.pos_iff.mpr
  constructor
  · let q : Real → Real := fun t => higham16Problem16_2QuadraticCLM x (F t)
    have hqPos : ∀ t, 0 < q t := by
      intro t
      dsimp [q]
      rw [higham16_problem16_2_quadraticCLM_apply]
      exact (Complex.pos_iff.mp ((hPD t).dotProduct_mulVec_pos hx)).1
    have hqInt : Integrable q (volume.restrict (Ioi (0 : Real))) := by
      exact (higham16Problem16_2QuadraticCLM x).integrable_comp hInt
    have hsupp : Function.support q = Set.univ := by
      ext t
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact (hqPos t).ne'
    have hmeasure :
        0 < (volume.restrict (Ioi (0 : Real))) (Function.support q) := by
      rw [hsupp]
      simp
    have hqIntegralPos : 0 < ∫ t in Ioi (0 : Real), q t :=
      (integral_pos_iff_support_of_nonneg_ae
        (Eventually.of_forall fun t => (hqPos t).le) hqInt).mpr hmeasure
    have hcomm :
        (∫ t in Ioi (0 : Real), q t) =
          higham16Problem16_2QuadraticCLM x
            (∫ t in Ioi (0 : Real), F t) := by
      simpa [q] using
        (higham16Problem16_2QuadraticCLM x).integral_comp_comm hInt
    rw [← higham16_problem16_2_quadraticCLM_apply, ← hcomm]
    exact hqIntegralPos
  · exact (hHerm.im_star_dotProduct_mulVec_self x).symm

/-- The general Problem 16.2 integral with right-hand side `-C` is exactly the
positive-sign Lyapunov integral. -/
lemma higham16_problem16_2_generalIntegral_neg_eq_lyapunovIntegral
    (A C : Higham16CMatrix n) :
    higham16Problem16_2Integral A (star A) (-C) =
      higham16Problem16_2LyapunovIntegral A C := by
  unfold higham16Problem16_2Integral higham16Problem16_2LyapunovIntegral
    higham16Problem16_2LyapunovKernel higham16Problem16_2Kernel
  simp only [mul_neg, neg_mul]
  rw [integral_neg]
  simp

/-- The Lyapunov integral satisfies `A X + X A* = -C`. -/
theorem higham16_problem16_2_lyapunovIntegral_solves
    (A C : Higham16CMatrix n)
    (hInt : IntegrableOn (higham16Problem16_2LyapunovKernel A C)
      (Ioi (0 : Real))) :
    A * higham16Problem16_2LyapunovIntegral A C +
      higham16Problem16_2LyapunovIntegral A C * star A = -C := by
  have hNeg : IntegrableOn
      (higham16Problem16_2Kernel A (star A) (-C)) (Ioi (0 : Real)) := by
    apply hInt.neg.congr
    exact Eventually.of_forall fun t => by
      simp [higham16Problem16_2LyapunovKernel,
        higham16Problem16_2Kernel, mul_neg, neg_mul]
  rw [← higham16_problem16_2_generalIntegral_neg_eq_lyapunovIntegral]
  exact higham16_problem16_2_integral_solves A (star A) (-C) hNeg

/-- Every integrand in the Lyapunov representation is positive definite when
`C` is positive definite. -/
theorem higham16_problem16_2_lyapunovKernel_posDef
    (A C : Higham16CMatrix n)
    (hC : Matrix.PosDef (CStarMatrix.ofMatrix.symm C)) (t : Real) :
    Matrix.PosDef
      (CStarMatrix.ofMatrix.symm
        (higham16Problem16_2LyapunovKernel A C t)) := by
  letI : NormedAlgebra ℚ (Higham16CMatrix n) :=
    NormedAlgebra.restrictScalars ℚ Complex (Higham16CMatrix n)
  let E : Higham16CMatrix n := exp (t • A)
  have hU : IsUnit (CStarMatrix.ofMatrix.symm E) :=
    IsUnit.map
      (CStarMatrix.ofMatrixRingEquiv (n := Fin n) (A := Complex)).symm
      (isUnit_exp (t • A))
  have hstar : exp (t • star A) = star E := by
    dsimp [E]
    calc
      exp (t • star A) = exp (star (t • A)) := by
        congr 1
        simp
      _ = star (exp (t • A)) := (star_exp _).symm
  change Matrix.PosDef
    (CStarMatrix.ofMatrix.symm E * CStarMatrix.ofMatrix.symm C *
      CStarMatrix.ofMatrix.symm (exp (t • star A)))
  rw [hstar]
  exact (Matrix.IsUnit.posDef_star_right_conjugate_iff hU).mpr hC

/-- The convergent Lyapunov integral is positive definite for positive-definite
`C`. -/
theorem higham16_problem16_2_lyapunovIntegral_posDef
    (A C : Higham16CMatrix n)
    (hC : Matrix.PosDef (CStarMatrix.ofMatrix.symm C))
    (hInt : IntegrableOn (higham16Problem16_2LyapunovKernel A C)
      (Ioi (0 : Real))) :
    Matrix.PosDef
      (CStarMatrix.ofMatrix.symm
        (higham16Problem16_2LyapunovIntegral A C)) := by
  exact higham16_problem16_2_integral_posDef_of_pointwise
    (higham16Problem16_2LyapunovKernel A C) hInt
    (higham16_problem16_2_lyapunovKernel_posDef A C hC)

/-- Problem 16.2's Lyapunov conclusion, with the Hurwitz spectral premise
replaced by its explicit semigroup-integrability consequence: the displayed
integral is the unique positive-definite solution of `A X + X A* = -C`. -/
theorem higham16_problem16_2_lyapunov_spd_unique
    (A C : Higham16CMatrix n)
    (hAll : Higham16LyapunovSemigroupIntegrable A)
    (hC : Matrix.PosDef (CStarMatrix.ofMatrix.symm C)) :
    ∃! X : Higham16CMatrix n,
      (A * X + X * star A = -C) ∧
        Matrix.PosDef (CStarMatrix.ofMatrix.symm X) := by
  have hInt : IntegrableOn (higham16Problem16_2LyapunovKernel A C)
      (Ioi (0 : Real)) := hAll C
  refine ⟨higham16Problem16_2LyapunovIntegral A C,
    ⟨higham16_problem16_2_lyapunovIntegral_solves A C hInt,
      higham16_problem16_2_lyapunovIntegral_posDef A C hC hInt⟩, ?_⟩
  intro Y hY
  apply higham16_problem16_2_solution_unique_of_difference_integrable
    A (star A) (-C) Y (higham16Problem16_2LyapunovIntegral A C)
    hY.1 (higham16_problem16_2_lyapunovIntegral_solves A C hInt)
  exact hAll (Y - higham16Problem16_2LyapunovIntegral A C)

noncomputable section

/-- The literal Hurwitz spectrum premise produces the semigroup-integrability
condition used by the analytic Lyapunov theorem. -/
theorem higham16_lyapunovSemigroupIntegrable_of_hurwitz
    (A : Higham16CMatrix n) (hn : 0 < n) (hA : Higham16Hurwitz A) :
    Higham16LyapunovSemigroupIntegrable A :=
  higham16_exponentialProductIntegrable_of_hurwitz A (star A) hn hA hA.star

/-- Problem 16.2's corrected positive-definite Lyapunov conclusion under the
literal spectral hypothesis from the book.  No decay or integrability premise
is exposed to callers. -/
theorem higham16_problem16_2_lyapunov_spd_unique_of_hurwitz
    (A C : Higham16CMatrix n) (hn : 0 < n)
    (hA : Higham16Hurwitz A)
    (hC : Matrix.PosDef (CStarMatrix.ofMatrix.symm C)) :
    ∃! X : Higham16CMatrix n,
      (A * X + X * star A = -C) ∧
        Matrix.PosDef (CStarMatrix.ofMatrix.symm X) :=
  higham16_problem16_2_lyapunov_spd_unique A C
    (higham16_lyapunovSemigroupIntegrable_of_hurwitz A hn hA) hC

private theorem higham16_zero_posSemidef_not_posDef (hn : 0 < n) :
    Matrix.PosSemidef
        (CStarMatrix.ofMatrix.symm (0 : Higham16CMatrix n)) ∧
      ¬Matrix.PosDef
        (CStarMatrix.ofMatrix.symm (0 : Higham16CMatrix n)) := by
  constructor
  · simpa using (Matrix.PosSemidef.zero :
      Matrix.PosSemidef (0 : Matrix (Fin n) (Fin n) Complex))
  · intro hpd
    change Matrix.PosDef (0 : Matrix (Fin n) (Fin n) Complex) at hpd
    let i : Fin n := ⟨0, hn⟩
    let x : Fin n → Complex := fun j => if j = i then 1 else 0
    have hx : x ≠ 0 := by
      intro hx0
      have hii := congrFun hx0 i
      simpa [x] using hii
    have hpos := hpd.dotProduct_mulVec_pos hx
    simpa [Matrix.mulVec, dotProduct] using hpos

private theorem higham16_neg_one_hurwitz (hn : 0 < n) :
    Higham16Hurwitz (-(1 : Higham16CMatrix n)) := by
  letI : Nontrivial (Higham16CMatrix n) := by
    let i : Fin n := ⟨0, hn⟩
    exact ⟨⟨0, 1, fun h => by
      have hii := congrArg (fun M : Higham16CMatrix n => M i i) h
      simpa using hii⟩⟩
  intro z hz
  have hspec : spectrum Complex (-(1 : Higham16CMatrix n)) =
      {(-1 : Complex)} := by
    rw [show -(1 : Higham16CMatrix n) =
        algebraMap Complex (Higham16CMatrix n) (-1 : Complex) by simp]
    exact spectrum.scalar_eq (-1 : Complex)
  rw [hspec] at hz
  have hz' : z = (-1 : Complex) := Set.mem_singleton_iff.mp hz
  subst z
  norm_num

/-- Source discrepancy on Higham p.317: positive semidefinite `C` does not
force the Lyapunov solution to be positive definite.  For the Hurwitz matrix
`A = -I`, taking `C = 0` gives the solution `X = 0`, which is positive
semidefinite but not positive definite whenever the dimension is positive.
Problem 16.2's later hypothesis `C` positive definite is the corrected one. -/
theorem higham16_p317_psd_does_not_imply_spd (hn : 0 < n) :
    ∃ (A C X : Higham16CMatrix n),
      Higham16Hurwitz A ∧
      Matrix.PosSemidef (CStarMatrix.ofMatrix.symm C) ∧
      A * X + X * star A = -C ∧
      ¬Matrix.PosDef (CStarMatrix.ofMatrix.symm X) := by
  refine ⟨-(1 : Higham16CMatrix n), 0, 0,
    higham16_neg_one_hurwitz hn, ?_, ?_, ?_⟩
  · simpa using (higham16_zero_posSemidef_not_posDef hn).1
  · simp
  · simpa using (higham16_zero_posSemidef_not_posDef hn).2

end

end SylvesterIntegral

end NumStability
