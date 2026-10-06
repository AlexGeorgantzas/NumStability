import NumStability.Algorithms.Summation.Compensated.FiniteFormat
import NumStability.Analysis.FirstOrder.AsymptoticFamilies
import NumStability.Source.Higham.Chapter07.Corollary06.Equilibration.Basic
import NumStability.Source.Higham.Chapter08.Section04.FanInAsymptotics.Basic
import NumStability.Source.Higham.Chapter08.Section04.FanInCore.AllOrdersEnvelope
import NumStability.Source.Higham.Chapter09.DoolittleClosure
import NumStability.Source.Higham.Chapter19.Theorem06.ColumnPivot

/-!
# Chapter08 Equation14 FanInProduct Basic

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapters1To9SourceClosure` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open Filter Asymptotics
open scoped BigOperators
open scoped Topology
open scoped Matrix.Norms.Operator

namespace NumStability

/-- The named higher-order coefficient in the literal seven-operation fan-in
bound is genuinely `O(u²)`, uniformly along every fixed-dimension family whose
unit roundoff tends to zero.  This supplies the Landau statement that was
previously only described in the declaration's prose. -/
theorem higham8_18_fanIn7CoefficientRemainder_isBigO_unit_sq
    {ι : Type*} {l : Filter ι} (fp : ι → FPModel) (n : ℕ)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0)) :
    (fun t => higham8_18_fanIn7CoefficientRemainder (fp t) n) =O[l]
      (fun t => (fp t).u ^ 2) := by
  let u : ι → ℝ := fun t => (fp t).u
  let g : ι → ℝ := fun t => gamma (fp t) n
  have hu_refl : u =O[l] u := Asymptotics.isBigO_refl u l
  have hcoeff :
      (fun t => higham8_18_gammaUnitCoefficient n (u t)) =O[l]
        (fun _ : ι => (1 : ℝ)) := by
    simpa only [Function.comp_apply, u] using
      (higham8_18_gammaUnitCoefficient_continuousAt_zero n).tendsto.isBigO_one
        ℝ |>.comp_tendsto hu
  have hg : g =O[l] u := by
    have hproduct := hu_refl.mul hcoeff
    simpa only [g, u, higham8_18_gamma_eq_unit_mul_coefficient, mul_one]
      using hproduct
  have hu_one : u =O[l] (fun _ : ι => (1 : ℝ)) := hu.isBigO_one ℝ
  have hg_one : g =O[l] (fun _ : ι => (1 : ℝ)) := hg.trans hu_one
  have hg2 : (fun t => g t ^ 2) =O[l] (fun t => u t ^ 2) := by
    simpa only [pow_two] using hg.mul hg
  have hg3 : (fun t => g t ^ 3) =O[l] (fun t => u t ^ 2) := by
    convert hg2.mul hg_one using 1 <;> funext t <;> ring
  have hg4 : (fun t => g t ^ 4) =O[l] (fun t => u t ^ 2) := by
    convert hg3.mul hg_one using 1 <;> funext t <;> ring
  have hg5 : (fun t => g t ^ 5) =O[l] (fun t => u t ^ 2) := by
    convert hg4.mul hg_one using 1 <;> funext t <;> ring
  have hg6 : (fun t => g t ^ 6) =O[l] (fun t => u t ^ 2) := by
    convert hg5.mul hg_one using 1 <;> funext t <;> ring
  have hg7 : (fun t => g t ^ 7) =O[l] (fun t => u t ^ 2) := by
    convert hg6.mul hg_one using 1 <;> funext t <;> ring
  have hgammaRemainder :
      (fun t => (((n : ℝ) * u t) ^ 2) / (1 - (n : ℝ) * u t)) =O[l]
        (fun t => u t ^ 2) := by
    have hproduct := (hu_refl.mul hg).const_mul_left (n : ℝ)
    convert hproduct using 1
    · funext t
      dsimp only [g, u]
      unfold gamma
      ring
    · funext t
      ring
  have hsum :=
    (((((hgammaRemainder.const_mul_left 7).add
      (hg2.const_mul_left 21)).add
      (hg3.const_mul_left 35)).add
      (hg4.const_mul_left 35)).add
      (hg5.const_mul_left 21)).add
      (hg6.const_mul_left 7) |>.add hg7
  convert hsum using 1

/-- The five terms of the fan-in tree that are linear in one local
perturbation.  Here `A=M₇M₆`, `B=M₅M₄`, `C=M₃M₂`, and `D=M₁`, while
`a,b,c,d,e` denote `Δ₇₆,Δ₅₄,Δ₃₂,Δ₁,Δ₇₆₅₄`. -/
noncomputable def higham8_14_fanIn7LocalLinearMatrix {n : ℕ}
    (A B C D a b c d e : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  a * B * C * D + A * b * C * D + e * C * D +
    A * B * c * D + A * B * C * d

/-- Every term omitted from the local linearization contains at least two
local perturbations.  The grouped form keeps that fact syntactically visible. -/
noncomputable def higham8_14_fanIn7LocalQuadraticRemainderMatrix {n : ℕ}
    (A B C D a b c d e : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  a * b * (C * D) + (A * B) * (c * d) +
    (a * B + A * b + e) * (c * D + C * d) +
    (a * B + A * b + e) * (c * d) +
    (a * b) * (c * D + C * d) +
    (a * b) * (c * d)

/-- Exact noncommutative expansion of the source's equation (8.14). -/
theorem higham8_14_fanIn7_local_exact_linear_quadratic_expansion {n : ℕ}
    (A B C D a b c d e : Matrix (Fin n) (Fin n) ℝ) :
    ((A + a) * (B + b) + e) * ((C + c) * (D + d)) =
      A * B * C * D +
        higham8_14_fanIn7LocalLinearMatrix A B C D a b c d e +
        higham8_14_fanIn7LocalQuadraticRemainderMatrix A B C D a b c d e := by
  unfold higham8_14_fanIn7LocalLinearMatrix
    higham8_14_fanIn7LocalQuadraticRemainderMatrix
  noncomm_ring

/-- Bridge between the chapter's explicit finite-sum multiplication and the
native `Matrix` multiplication used by the noncommutative polynomial proof. -/
theorem higham8_matMul_eq_matrix_mul {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) : matMul n A B = A * B := by
  ext i j
  simp [matMul, Matrix.mul_apply]

/-- Equation (8.14) itself is therefore exactly the unperturbed fan-in
product, plus its five local linear terms, plus the named cross-term
remainder. -/
theorem higham8_14_fanIn7RoundedMatrix_eq_exact_add_localLinear_add_remainder
    (n : ℕ)
    (M1 M2 M3 M4 M5 M6 M7 Δ1 Δ32 Δ54 Δ76 Δ7654 :
      Matrix (Fin n) (Fin n) ℝ) :
    higham8_14_fanIn7RoundedMatrix n
        M1 M2 M3 M4 M5 M6 M7 Δ1 Δ32 Δ54 Δ76 Δ7654 =
      fun i j =>
        higham8_13_fanIn7Matrix n M1 M2 M3 M4 M5 M6 M7 i j +
          higham8_14_fanIn7LocalLinearMatrix
            (M7 * M6) (M5 * M4) (M3 * M2) M1
            Δ76 Δ54 Δ32 Δ1 Δ7654 i j +
          higham8_14_fanIn7LocalQuadraticRemainderMatrix
            (M7 * M6) (M5 * M4) (M3 * M2) M1
            Δ76 Δ54 Δ32 Δ1 Δ7654 i j := by
  unfold higham8_14_fanIn7RoundedMatrix higham8_13_fanIn7Matrix
  simp only [higham8_matMul_eq_matrix_mul]
  change
    (((M7 * M6 + Δ76) * (M5 * M4 + Δ54) + Δ7654) *
        ((M3 * M2 + Δ32) * (M1 + Δ1))) =
      (M7 * M6) * (M5 * M4) * ((M3 * M2) * M1) +
        higham8_14_fanIn7LocalLinearMatrix
          (M7 * M6) (M5 * M4) (M3 * M2) M1
          Δ76 Δ54 Δ32 Δ1 Δ7654 +
        higham8_14_fanIn7LocalQuadraticRemainderMatrix
          (M7 * M6) (M5 * M4) (M3 * M2) M1
          Δ76 Δ54 Δ32 Δ1 Δ7654
  unfold higham8_14_fanIn7LocalLinearMatrix
    higham8_14_fanIn7LocalQuadraticRemainderMatrix
  noncomm_ring

/-- A rounded matrix product of two entrywise `O(1)` matrix families remains
entrywise `O(1)` when the fixed inner dimension is used and `u → 0`. -/
theorem higham8_fl_matMul_family_isBigO_one
    {ι : Type*} {l : Filter ι} (fp : ι → FPModel)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0))
    (n : ℕ) (hvalid : ∀ t, gammaValid (fp t) n)
    (A B : ι → Matrix (Fin n) (Fin n) ℝ)
    (hA : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) A)
    (hB : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) B) :
    Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ))
      (fun t => fl_matMul (fp t) n n n (A t) (B t)) := by
  have hg := higham8_18_gamma_family_isBigO_unit fp n hu
  have hu_one : (fun t => (fp t).u) =O[l] (fun _ : ι => (1 : ℝ)) :=
    hu.isBigO_one ℝ
  let Aabs : ι → Matrix (Fin n) (Fin n) ℝ := fun t i j => |A t i j|
  let Babs : ι → Matrix (Fin n) (Fin n) ℝ := fun t i j => |B t i j|
  have hAabs : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) Aabs :=
    hA.abs
  have hBabs : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) Babs :=
    hB.abs
  have hprod : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ))
      (fun t => A t * B t) := by
    simpa only [one_mul] using hA.mul hB
  have habsProd : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ))
      (fun t => Aabs t * Babs t) := by
    simpa only [one_mul] using hAabs.mul hBabs
  intro i j
  let E : ι → ℝ := fun t =>
    ∑ k : Fin n, |A t i k| * |B t k j|
  have hE : E =O[l] (fun _ : ι => (1 : ℝ)) := by
    simpa only [E, Aabs, Babs, Matrix.mul_apply] using habsProd i j
  have hbudget : (fun t => gamma (fp t) n * E t) =O[l]
      (fun t => (fp t).u) := by
    simpa only [mul_one] using hg.mul hE
  have herrBudget :
      (fun t => fl_matMul (fp t) n n n (A t) (B t) i j -
        (A t * B t) i j) =O[l]
        (fun t => gamma (fp t) n * E t) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [] with t
    have hγ : 0 ≤ gamma (fp t) n := gamma_nonneg (fp t) (hvalid t)
    have hE0 : 0 ≤ E t :=
      Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have herr := matMul_error_bound (fp t) n n n (A t) (B t) (hvalid t) i j
    simpa only [Real.norm_eq_abs, one_mul, abs_of_nonneg hγ,
      abs_of_nonneg hE0, abs_mul, E, higham8_matMul_eq_matrix_mul] using herr
  have herrOne := (herrBudget.trans hbudget).trans hu_one
  have hsum := herrOne.add (hprod i j)
  convert hsum using 1
  funext t
  ring

/-- A local perturbation bounded by `gamma_n` times a nonnegative `O(1)`
matrix envelope is entrywise `O(u)`. -/
theorem higham8_localDelta_family_isBigO_unit_of_gamma_envelope
    {ι : Type*} {l : Filter ι} (fp : ι → FPModel)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0))
    (n : ℕ) (hvalid : ∀ t, gammaValid (fp t) n)
    (Δ E : ι → Matrix (Fin n) (Fin n) ℝ)
    (hE : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) E)
    (hE_nonneg : ∀ t i j, 0 ≤ E t i j)
    (hΔ : ∀ t i j, |Δ t i j| ≤ gamma (fp t) n * E t i j) :
    Higham8MatrixFamilyIsBigO l (fun t => (fp t).u) Δ := by
  have hg := higham8_18_gamma_family_isBigO_unit fp n hu
  intro i j
  have hbudget : (fun t => gamma (fp t) n * E t i j) =O[l]
      (fun t => (fp t).u) := by
    simpa only [mul_one] using hg.mul (hE i j)
  have hcompare : (fun t => Δ t i j) =O[l]
      (fun t => gamma (fp t) n * E t i j) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [] with t
    have hγ : 0 ≤ gamma (fp t) n := gamma_nonneg (fp t) (hvalid t)
    simpa only [Real.norm_eq_abs, one_mul, abs_mul, abs_of_nonneg hγ,
      abs_of_nonneg (hE_nonneg t i j)] using hΔ t i j
  exact hcompare.trans hbudget

/-- The cross terms in the exact local expansion are uniformly `O(u²)` as
soon as each of the five local perturbation matrices is entrywise `O(u)`.
This is precisely the step hidden by the source's `+ O(u²)` notation. -/
theorem higham8_14_fanIn7LocalQuadraticRemainder_isBigO_unit_sq
    {ι : Type*} {l : Filter ι} {n : ℕ} (u : ι → ℝ)
    (hu : Tendsto u l (𝓝 0))
    (A B C D : Matrix (Fin n) (Fin n) ℝ)
    (a b c d e : ι → Matrix (Fin n) (Fin n) ℝ)
    (ha : Higham8MatrixFamilyIsBigO l u a)
    (hb : Higham8MatrixFamilyIsBigO l u b)
    (hc : Higham8MatrixFamilyIsBigO l u c)
    (hd : Higham8MatrixFamilyIsBigO l u d)
    (he : Higham8MatrixFamilyIsBigO l u e) :
    Higham8MatrixFamilyIsBigO l (fun t => u t ^ 2)
      (fun t => higham8_14_fanIn7LocalQuadraticRemainderMatrix
        A B C D (a t) (b t) (c t) (d t) (e t)) := by
  let A₀ : ι → Matrix (Fin n) (Fin n) ℝ := fun _ => A
  let B₀ : ι → Matrix (Fin n) (Fin n) ℝ := fun _ => B
  let C₀ : ι → Matrix (Fin n) (Fin n) ℝ := fun _ => C
  let D₀ : ι → Matrix (Fin n) (Fin n) ℝ := fun _ => D
  have hA₀ : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) A₀ :=
    Higham8MatrixFamilyIsBigO.const A
  have hB₀ : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) B₀ :=
    Higham8MatrixFamilyIsBigO.const B
  have hC₀ : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) C₀ :=
    Higham8MatrixFamilyIsBigO.const C
  have hD₀ : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) D₀ :=
    Higham8MatrixFamilyIsBigO.const D
  let leftLinear : ι → Matrix (Fin n) (Fin n) ℝ :=
    fun t => a t * B + A * b t + e t
  let rightLinear : ι → Matrix (Fin n) (Fin n) ℝ :=
    fun t => c t * D + C * d t
  let ab : ι → Matrix (Fin n) (Fin n) ℝ := fun t => a t * b t
  let cd : ι → Matrix (Fin n) (Fin n) ℝ := fun t => c t * d t
  have hleft : Higham8MatrixFamilyIsBigO l u leftLinear := by
    exact ((ha.unit_mul_one hB₀).add (hA₀.one_mul_unit hb)).add he
  have hright : Higham8MatrixFamilyIsBigO l u rightLinear := by
    exact (hc.unit_mul_one hD₀).add (hC₀.one_mul_unit hd)
  have hab : Higham8MatrixFamilyIsBigO l (fun t => u t ^ 2) ab :=
    ha.unit_mul_unit hb
  have hcd : Higham8MatrixFamilyIsBigO l (fun t => u t ^ 2) cd :=
    hc.unit_mul_unit hd
  have hCD : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ))
      (fun _ => C * D) := Higham8MatrixFamilyIsBigO.const (C * D)
  have hAB : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ))
      (fun _ => A * B) := Higham8MatrixFamilyIsBigO.const (A * B)
  have h1 := hab.sq_mul_one hCD
  have h2 := hAB.one_mul_sq hcd
  have h3 := hleft.unit_mul_unit hright
  have h4 := (hleft.unit_to_one hu).one_mul_sq hcd
  have h5 := hab.sq_mul_one (hright.unit_to_one hu)
  have h6 := hab.sq_mul_one (hcd.sq_to_one hu)
  have hsum := ((((h1.add h2).add h3).add h4).add h5).add h6
  simpa only [higham8_14_fanIn7LocalQuadraticRemainderMatrix,
    leftLinear, rightLinear, ab, cd, A₀, B₀, C₀, D₀] using hsum

/-- Literal-producer closure for the local expansion.  For an actual family
of fan-in executions, one can choose the five perturbation matrices in (8.14)
simultaneously so that every one is entrywise `O(u)` and the complete omitted
cross-term matrix is entrywise `O(u²)`. -/
theorem higham8_14_fanIn7Executor_has_local_O_unit_expansion
    {ι : Type*} {l : Filter ι} (fp : ι → FPModel)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0))
    (n : ℕ) (M1 M2 M3 M4 M5 M6 M7 : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ) (hvalid : ∀ t, gammaValid (fp t) n) :
    ∃ Δ1 Δ32 Δ54 Δ76 Δ7654 : ι → Matrix (Fin n) (Fin n) ℝ,
      (∀ t,
        higham8_14_fanIn7Executor (fp t) n M1 M2 M3 M4 M5 M6 M7 b =
          higham8_14_fanIn7RoundedApply n
            M1 M2 M3 M4 M5 M6 M7
            (Δ1 t) (Δ32 t) (Δ54 t) (Δ76 t) (Δ7654 t) b) ∧
      Higham8MatrixFamilyIsBigO l (fun t => (fp t).u) Δ1 ∧
      Higham8MatrixFamilyIsBigO l (fun t => (fp t).u) Δ32 ∧
      Higham8MatrixFamilyIsBigO l (fun t => (fp t).u) Δ54 ∧
      Higham8MatrixFamilyIsBigO l (fun t => (fp t).u) Δ76 ∧
      Higham8MatrixFamilyIsBigO l (fun t => (fp t).u) Δ7654 ∧
      Higham8MatrixFamilyIsBigO l (fun t => (fp t).u ^ 2)
        (fun t => higham8_14_fanIn7LocalQuadraticRemainderMatrix
          (M7 * M6) (M5 * M4) (M3 * M2) M1
          (Δ76 t) (Δ54 t) (Δ32 t) (Δ1 t) (Δ7654 t)) := by
  classical
  have hp := fun t => higham8_14_fanIn7Executor_eq_roundedApply
    (fp t) n M1 M2 M3 M4 M5 M6 M7 b (hvalid t)
  choose Δ1 Δ32 Δ54 Δ76 Δ7654 hrest using hp
  let C32 : ι → Matrix (Fin n) (Fin n) ℝ :=
    fun t => fl_matMul (fp t) n n n M3 M2
  let C54 : ι → Matrix (Fin n) (Fin n) ℝ :=
    fun t => fl_matMul (fp t) n n n M5 M4
  let C76 : ι → Matrix (Fin n) (Fin n) ℝ :=
    fun t => fl_matMul (fp t) n n n M7 M6
  let C7654 : ι → Matrix (Fin n) (Fin n) ℝ :=
    fun t => fl_matMul (fp t) n n n (C76 t) (C54 t)
  have hC32 : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) C32 := by
    exact higham8_fl_matMul_family_isBigO_one fp hu n hvalid
      (fun _ => M3) (fun _ => M2)
      (Higham8MatrixFamilyIsBigO.const M3)
      (Higham8MatrixFamilyIsBigO.const M2)
  have hC54 : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) C54 := by
    exact higham8_fl_matMul_family_isBigO_one fp hu n hvalid
      (fun _ => M5) (fun _ => M4)
      (Higham8MatrixFamilyIsBigO.const M5)
      (Higham8MatrixFamilyIsBigO.const M4)
  have hC76 : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) C76 := by
    exact higham8_fl_matMul_family_isBigO_one fp hu n hvalid
      (fun _ => M7) (fun _ => M6)
      (Higham8MatrixFamilyIsBigO.const M7)
      (Higham8MatrixFamilyIsBigO.const M6)
  have hC7654 : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) C7654 := by
    exact higham8_fl_matMul_family_isBigO_one fp hu n hvalid C76 C54 hC76 hC54
  let E1₀ : Matrix (Fin n) (Fin n) ℝ := fun i j => |M1 i j|
  let E1 : ι → Matrix (Fin n) (Fin n) ℝ := fun _ => E1₀
  have hE1 : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) E1 :=
    Higham8MatrixFamilyIsBigO.const E1₀
  have hΔ1 : Higham8MatrixFamilyIsBigO l (fun t => (fp t).u) Δ1 := by
    apply higham8_localDelta_family_isBigO_unit_of_gamma_envelope
      fp hu n hvalid Δ1 E1 hE1
    · intro t i j
      exact abs_nonneg (M1 i j)
    · intro t i j
      simpa only [E1, E1₀] using (hrest t).2.1 i j
  let E54₀ : Matrix (Fin n) (Fin n) ℝ :=
    fun i j => ∑ k : Fin n, |M5 i k| * |M4 k j|
  let E54 : ι → Matrix (Fin n) (Fin n) ℝ := fun _ => E54₀
  have hE54 : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) E54 :=
    Higham8MatrixFamilyIsBigO.const E54₀
  have hΔ54 : Higham8MatrixFamilyIsBigO l (fun t => (fp t).u) Δ54 := by
    apply higham8_localDelta_family_isBigO_unit_of_gamma_envelope
      fp hu n hvalid Δ54 E54 hE54
    · intro t i j
      exact Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    · intro t i j
      simpa only [E54, E54₀] using (hrest t).2.2.2.1 i j
  let E76₀ : Matrix (Fin n) (Fin n) ℝ :=
    fun i j => ∑ k : Fin n, |M7 i k| * |M6 k j|
  let E76 : ι → Matrix (Fin n) (Fin n) ℝ := fun _ => E76₀
  have hE76 : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) E76 :=
    Higham8MatrixFamilyIsBigO.const E76₀
  have hΔ76 : Higham8MatrixFamilyIsBigO l (fun t => (fp t).u) Δ76 := by
    apply higham8_localDelta_family_isBigO_unit_of_gamma_envelope
      fp hu n hvalid Δ76 E76 hE76
    · intro t i j
      exact Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    · intro t i j
      simpa only [E76, E76₀] using (hrest t).2.2.2.2.1 i j
  let E32₀ : Matrix (Fin n) (Fin n) ℝ :=
    fun i j => ∑ k : Fin n, |M3 i k| * |M2 k j|
  let C32abs : ι → Matrix (Fin n) (Fin n) ℝ := fun t i j => |C32 t i j|
  let E32 : ι → Matrix (Fin n) (Fin n) ℝ := fun t => E32₀ + C32abs t
  have hE32₀ : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ))
      (fun _ => E32₀) := Higham8MatrixFamilyIsBigO.const E32₀
  have hC32abs : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) C32abs :=
    hC32.abs
  have hE32 : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) E32 :=
    hE32₀.add hC32abs
  have hΔ32 : Higham8MatrixFamilyIsBigO l (fun t => (fp t).u) Δ32 := by
    apply higham8_localDelta_family_isBigO_unit_of_gamma_envelope
      fp hu n hvalid Δ32 E32 hE32
    · intro t i j
      exact add_nonneg
        (Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)))
        (abs_nonneg (C32 t i j))
    · intro t i j
      calc
        |Δ32 t i j| ≤
            gamma (fp t) n * E32₀ i j + gamma (fp t) n * |C32 t i j| := by
          simpa only [E32₀, C32] using (hrest t).2.2.1 i j
        _ = gamma (fp t) n * E32 t i j := by
          simp only [E32, C32abs, Matrix.add_apply]
          ring
  let C54abs : ι → Matrix (Fin n) (Fin n) ℝ := fun t i j => |C54 t i j|
  let C76abs : ι → Matrix (Fin n) (Fin n) ℝ := fun t i j => |C76 t i j|
  let C7654abs : ι → Matrix (Fin n) (Fin n) ℝ := fun t i j => |C7654 t i j|
  let E7654 : ι → Matrix (Fin n) (Fin n) ℝ :=
    fun t => C76abs t * C54abs t + C7654abs t
  have hC54abs : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) C54abs :=
    hC54.abs
  have hC76abs : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) C76abs :=
    hC76.abs
  have hC7654abs : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) C7654abs :=
    hC7654.abs
  have hC76C54abs : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ))
      (fun t => C76abs t * C54abs t) := by
    simpa only [one_mul] using hC76abs.mul hC54abs
  have hE7654 : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) E7654 :=
    hC76C54abs.add hC7654abs
  have hΔ7654 : Higham8MatrixFamilyIsBigO l (fun t => (fp t).u) Δ7654 := by
    apply higham8_localDelta_family_isBigO_unit_of_gamma_envelope
      fp hu n hvalid Δ7654 E7654 hE7654
    · intro t i j
      have hprod : 0 ≤ (C76abs t * C54abs t) i j := by
        rw [Matrix.mul_apply]
        exact Finset.sum_nonneg
          (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
      exact add_nonneg hprod (abs_nonneg (C7654 t i j))
    · intro t i j
      calc
        |Δ7654 t i j| ≤
            gamma (fp t) n *
                (∑ k : Fin n, |C76 t i k| * |C54 t k j|) +
              gamma (fp t) n * |C7654 t i j| := by
          simpa only [C76, C54, C7654] using (hrest t).2.2.2.2.2 i j
        _ = gamma (fp t) n * E7654 t i j := by
          simp only [E7654, C76abs, C54abs, C7654abs,
            Matrix.add_apply, Matrix.mul_apply]
          ring
  have hquadratic :=
    higham8_14_fanIn7LocalQuadraticRemainder_isBigO_unit_sq
      (fun t => (fp t).u) hu (M7 * M6) (M5 * M4) (M3 * M2) M1
      Δ76 Δ54 Δ32 Δ1 Δ7654 hΔ76 hΔ54 hΔ32 hΔ1 hΔ7654
  exact ⟨Δ1, Δ32, Δ54, Δ76, Δ7654,
    fun t => (hrest t).1, hΔ1, hΔ32, hΔ54, hΔ76, hΔ7654, hquadratic⟩

end NumStability
