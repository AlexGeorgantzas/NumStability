import NumStability.Analysis.FloatingPointArithmetic.IeeeSpecialValueOperations.Results
import NumStability.Source.Higham.Chapter02.Problem25.NonzeroEvaluation.Basic

/-!
# Chapter02 Problem19 GradualUnderflowExactness Basic

Canonical destination for material split out of
`NumStability.Analysis.HighamChapter2GradualUnderflowExact` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace FloatingPointFormat

/-- Hauser's lattice lemma for addition: two finite operands whose exact sum
lies below the smallest normal magnitude have a finite exact sum. -/
theorem finiteSystem_add_finiteSystem_of_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x y : Real}
    (hx : fmt.finiteSystem x) (hy : fmt.finiteSystem y)
    (hunder : fmt.finiteUnderflowRange (x + y)) :
    fmt.finiteSystem (x + y) := by
  obtain ⟨kx, hkx⟩ :=
    fmt.finiteSystem_exists_int_mul_minSubnormalMagnitude hx
  obtain ⟨ky, hky⟩ :=
    fmt.finiteSystem_exists_int_mul_minSubnormalMagnitude hy
  let k : Int := kx + ky
  have hrepr : x + y = (k : Real) * fmt.minSubnormalMagnitude := by
    rw [hkx, hky]
    simp [k]
    ring
  have heta_pos : 0 < fmt.minSubnormalMagnitude :=
    fmt.minSubnormalMagnitude_pos
  have hcoefficient_real :
      |(k : Real)| < (fmt.minNormalMantissa : Real) := by
    rw [finiteUnderflowRange, hrepr,
      fmt.minNormalMagnitude_eq_minNormalMantissa_mul_minSubnormalMagnitude,
      abs_mul, abs_of_pos heta_pos] at hunder
    exact lt_of_mul_lt_mul_right hunder (le_of_lt heta_pos)
  have hnatabs_cast : ((k.natAbs : Nat) : Real) = |(k : Real)| := by
    norm_num [Int.cast_abs]
  have hk_small_real :
      ((k.natAbs : Nat) : Real) < (fmt.minNormalMantissa : Real) := by
    rw [hnatabs_cast]
    exact hcoefficient_real
  have hk_small : k.natAbs < fmt.minNormalMantissa := by
    exact_mod_cast hk_small_real
  have hk_mantissa : k.natAbs < fmt.beta ^ fmt.t :=
    lt_trans hk_small fmt.minNormalMantissa_lt_mantissaBound
  have hemin : fmt.exponentInRange fmt.emin :=
    ⟨le_rfl, fmt.emin_le_emax⟩
  have hfinite :=
    fmt.scaledIntegerValue_finiteSystem_of_natAbs_lt_mantissaBound
      (negative := false) (k := k) (e := fmt.emin) hemin hk_mantissa
  rw [hrepr]
  simpa [signValue, minSubnormalMagnitude] using hfinite

/-- Subtraction form of the Hauser lattice lemma. -/
theorem finiteSystem_sub_finiteSystem_of_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x y : Real}
    (hx : fmt.finiteSystem x) (hy : fmt.finiteSystem y)
    (hunder : fmt.finiteUnderflowRange (x - y)) :
    fmt.finiteSystem (x - y) := by
  have hyneg : fmt.finiteSystem (-y) := fmt.finiteSystem_neg hy
  have hunder' : fmt.finiteUnderflowRange (x + (-y)) := by
    simpa [sub_eq_add_neg] using hunder
  simpa [sub_eq_add_neg] using
    fmt.finiteSystem_add_finiteSystem_of_finiteUnderflowRange hx hyneg hunder'

/-- **Higham Problem 2.19 (Hauser), addition.**  Under gradual underflow,
correct round-to-even addition of finite operands is exact whenever the exact
sum lies in the underflow range. -/
theorem finiteRoundToEvenOp_add_eq_exact_of_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x y : Real}
    (hx : fmt.finiteSystem x) (hy : fmt.finiteSystem y)
    (hunder : fmt.finiteUnderflowRange (x + y)) :
    fmt.finiteRoundToEvenOp BasicOp.add x y = x + y := by
  have hfinite : fmt.finiteSystem (BasicOp.exact BasicOp.add x y) := by
    simpa [BasicOp.exact] using
      fmt.finiteSystem_add_finiteSystem_of_finiteUnderflowRange hx hy hunder
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem hfinite)

/-- **Higham Problem 2.19 (Hauser), subtraction.**  Under gradual underflow,
correct round-to-even subtraction of finite operands is exact whenever the
exact difference lies in the underflow range. -/
theorem finiteRoundToEvenOp_sub_eq_exact_of_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x y : Real}
    (hx : fmt.finiteSystem x) (hy : fmt.finiteSystem y)
    (hunder : fmt.finiteUnderflowRange (x - y)) :
    fmt.finiteRoundToEvenOp BasicOp.sub x y = x - y := by
  have hfinite : fmt.finiteSystem (BasicOp.exact BasicOp.sub x y) := by
    simpa [BasicOp.exact] using
      fmt.finiteSystem_sub_finiteSystem_of_finiteUnderflowRange hx hy hunder
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem hfinite)

/-- Gradual-underflow form of Higham Theorem 2.4: the printed Ferguson
magnitude/exponent condition already reconstructs a finite exact difference,
so the explicit no-underflow proviso is unnecessary. -/
theorem finiteRoundToEvenOp_sub_eq_exact_of_fergusonMagnitudeExponentConditionLe_gradualUnderflow
    {fmt : FloatingPointFormat} {x y : Real}
    (hcond : fmt.fergusonMagnitudeExponentConditionLe x y) :
    fmt.finiteRoundToEvenOp BasicOp.sub x y = x - y := by
  have hfinite : fmt.finiteSystem (BasicOp.exact BasicOp.sub x y) := by
    simpa [BasicOp.exact] using
      fmt.fergusonMagnitudeExponentConditionLe_sub_finiteSystem hcond
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem hfinite)

/-- Joint body-level corollary: gradual underflow removes the proviso from
Ferguson's Theorem 2.4 and Sterbenz's Theorem 2.5. -/
theorem higham2_gradualUnderflow_removes_theorems2_4_and2_5_provisos
    {fmt : FloatingPointFormat} {x y : Real}
    (hx : fmt.finiteSystem x) (hy : fmt.finiteSystem y)
    (hferguson : fmt.fergusonMagnitudeExponentConditionLe x y)
    (hsterbenz : fmt.sterbenzRatioConditionLe x y) :
    fmt.finiteRoundToEvenOp BasicOp.sub x y = x - y ∧
      fmt.finiteRoundToEvenOp BasicOp.sub x y = x - y := by
  exact ⟨
    fmt.finiteRoundToEvenOp_sub_eq_exact_of_fergusonMagnitudeExponentConditionLe_gradualUnderflow
      hferguson,
    fmt.finiteRoundToEvenOp_sub_finiteSystem_eq_exact_of_sterbenzRatioConditionLe
      hx hy hsterbenz⟩

end FloatingPointFormat
end NumStability
