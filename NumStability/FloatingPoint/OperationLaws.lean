import NumStability.Analysis.FloatingPointArithmetic

namespace NumStability

noncomputable section

namespace FloatingPointFormat

/-!
# Finite round-to-even operation laws

Source-independent algebraic laws for the repository's finite real-valued
round-to-even operation layer. IEEE special values and exception behavior are
outside this module's scope.
-/

/-- Rounded addition commutes because its exact real arguments agree. -/
theorem finiteRoundToEvenOp_add_comm
    (fmt : FloatingPointFormat) (a b : ℝ) :
    fmt.finiteRoundToEvenOp BasicOp.add a b =
      fmt.finiteRoundToEvenOp BasicOp.add b a := by
  simp [finiteRoundToEvenOp, BasicOp.exact, add_comm]

/-- Rounded multiplication commutes because its exact real arguments agree. -/
theorem finiteRoundToEvenOp_mul_comm
    (fmt : FloatingPointFormat) (a b : ℝ) :
    fmt.finiteRoundToEvenOp BasicOp.mul a b =
      fmt.finiteRoundToEvenOp BasicOp.mul b a := by
  simp [finiteRoundToEvenOp, BasicOp.exact, mul_comm]

/-- Exact finite subtraction is odd under interchange of its arguments. -/
theorem finiteRoundToEvenOp_sub_sign_symmetry_of_exact_finiteSystem
    {fmt : FloatingPointFormat} {a b : ℝ}
    (hab : fmt.finiteSystem (a - b)) :
    fmt.finiteRoundToEvenOp BasicOp.sub b a =
      -fmt.finiteRoundToEvenOp BasicOp.sub a b := by
  have hba : fmt.finiteSystem (b - a) := by
    have hneg := fmt.finiteSystem_neg hab
    convert hneg using 1
    ring
  have hleft :
      fmt.finiteRoundToEvenOp BasicOp.sub b a = b - a := by
    simpa [BasicOp.exact] using
      (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.sub) (x := b) (y := a) hba)
  have hright :
      fmt.finiteRoundToEvenOp BasicOp.sub a b = a - b := by
    simpa [BasicOp.exact] using
      (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.sub) (x := a) (y := b) hab)
  rw [hleft, hright]
  ring

/-- Total finite subtraction is odd outside the finite-normal range. -/
theorem finiteRoundToEvenOp_sub_sign_symmetry_of_not_finiteNormalRange
    {fmt : FloatingPointFormat} {a b : ℝ}
    (hab : ¬ fmt.finiteNormalRange (a - b)) :
    fmt.finiteRoundToEvenOp BasicOp.sub b a =
      -fmt.finiteRoundToEvenOp BasicOp.sub a b := by
  simp [finiteRoundToEvenOp, BasicOp.exact]
  rw [show b - a = -(a - b) by ring]
  exact fmt.finiteRoundToEven_neg_of_not_finiteNormalRange hab

/-- Total finite subtraction is odd for binary-style round-to-even formats. -/
theorem finiteRoundToEvenOp_sub_sign_symmetry
    {fmt : FloatingPointFormat}
    (hbeta : evenMantissa fmt.beta) (ht : 1 < fmt.t)
    (a b : ℝ) :
    fmt.finiteRoundToEvenOp BasicOp.sub b a =
      -fmt.finiteRoundToEvenOp BasicOp.sub a b := by
  simp [finiteRoundToEvenOp, BasicOp.exact]
  rw [show b - a = -(a - b) by ring]
  exact fmt.finiteRoundToEven_neg hbeta ht (a - b)

/-- Rounding `a + a` agrees with rounding `2 * a`. -/
theorem finiteRoundToEvenOp_add_self_eq_mul_two
    (fmt : FloatingPointFormat) (a : ℝ) :
    fmt.finiteRoundToEvenOp BasicOp.add a a =
      fmt.finiteRoundToEvenOp BasicOp.mul 2 a := by
  simp [finiteRoundToEvenOp, BasicOp.exact, two_mul]

/-- Rounding `(1 / 2) * a` agrees with rounding `a / 2`. -/
theorem finiteRoundToEvenOp_half_mul_eq_div_two
    (fmt : FloatingPointFormat) (a : ℝ) :
    fmt.finiteRoundToEvenOp BasicOp.mul (1 / 2 : ℝ) a =
      fmt.finiteRoundToEvenOp BasicOp.div a 2 := by
  simp [finiteRoundToEvenOp, BasicOp.exact]
  ring_nf

end FloatingPointFormat

end

end NumStability
