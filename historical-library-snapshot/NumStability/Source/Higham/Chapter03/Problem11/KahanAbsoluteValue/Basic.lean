import Mathlib.Tactic
import NumStability.Source.Higham.Chapter01.Section12.InstabilityWithoutCancellation.PivotingExample
import NumStability.Source.Higham.Chapter02.Problem09.DoubleRounding.Counterexample.Results

/-!
# Chapter03 Problem11 KahanAbsoluteValue Basic

Canonical destination for material split out of
`NumStability.Algorithms.KahanAbsolute` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

/-- Exact real analogue of the MATLAB absolute-value routine after `k + 1`
square-root steps and `k` square steps. -/
noncomputable def kahanAbsoluteExactFromSquareSteps (k : ℕ) (x : ℝ) : ℝ :=
  repeatedSquare k (repeatedSqrt (k + 1) (x ^ 2))

/-- One extra square root followed by one fewer square always leaves
`sqrt(x^2) = |x|` in exact real arithmetic. -/
theorem kahanAbsoluteExactFromSquareSteps_eq_abs (k : ℕ) (x : ℝ) :
    kahanAbsoluteExactFromSquareSteps k x = |x| := by
  induction k with
  | zero =>
      simp [kahanAbsoluteExactFromSquareSteps, repeatedSquare, repeatedSqrt,
        Real.sqrt_sq_eq_abs]
  | succ k ih =>
      have hsquare :
          repeatedSqrt (k + 1 + 1) (x ^ 2) ^ 2 =
            repeatedSqrt (k + 1) (x ^ 2) := by
        simp [repeatedSqrt]
      calc
        kahanAbsoluteExactFromSquareSteps (k + 1) x
            = repeatedSquare k (repeatedSqrt (k + 1 + 1) (x ^ 2) ^ 2) := by
                simp [kahanAbsoluteExactFromSquareSteps, repeatedSquare]
        _ = repeatedSquare k (repeatedSqrt (k + 1) (x ^ 2)) := by
                rw [hsquare]
        _ = |x| := ih

/-- Exact baseline for the `m = 50` experiment in Problem 3.11. -/
theorem kahanAbsoluteExact_fifty_eq_abs (x : ℝ) :
    kahanAbsoluteExactFromSquareSteps 49 x = |x| :=
  kahanAbsoluteExactFromSquareSteps_eq_abs 49 x

/-- Exact baseline for the `m = 75` experiment in Problem 3.11. -/
theorem kahanAbsoluteExact_seventyFive_eq_abs (x : ℝ) :
    kahanAbsoluteExactFromSquareSteps 74 x = |x| :=
  kahanAbsoluteExactFromSquareSteps_eq_abs 74 x

/-- The six displayed source inputs in Problem 3.11. -/
noncomputable def kahanAbsoluteProblem311Inputs : Fin 6 → ℝ :=
  ![(1 / 4 : ℝ), (1 / 2 : ℝ), (3 / 4 : ℝ), (5 / 4 : ℝ), (3 / 2 : ℝ), (2 : ℝ)]

/-- The displayed Sun SPARCstation `m = 75` outputs in Problem 3.11. -/
noncomputable def kahanAbsoluteProblem311SunM75Outputs : Fin 6 → ℝ :=
  ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ)]

/-- The displayed 486DX `m = 75` outputs in Problem 3.11. -/
noncomputable def kahanAbsoluteProblem311I486M75Outputs : Fin 6 → ℝ :=
  fun _ => 1

/-- The displayed 486DX `m = 50` outputs in Problem 3.11, encoded as the
four-decimal values printed by the source. -/
noncomputable def kahanAbsoluteProblem311I486M50Outputs : Fin 6 → ℝ :=
  ![(2528 / 10000 : ℝ), (5028 / 10000 : ℝ), (7788 / 10000 : ℝ),
    (12840 / 10000 : ℝ), (14550 / 10000 : ℝ), (21170 / 10000 : ℝ)]

/-- Half of one unit in the fourth displayed decimal place. -/
noncomputable def decimal4HalfUlp : ℝ :=
  1 / (2 * (10 : ℝ) ^ 4)

/-- A sufficient interval certificate for a real number to display as `d` to
four decimal places.  This records the numerical display row without committing
to a full MATLAB `format short` formatter or a tie-breaking policy. -/
def decimal4DisplaysAs (x d : ℝ) : Prop :=
  d - decimal4HalfUlp ≤ x ∧ x < d + decimal4HalfUlp

/-- Componentwise four-decimal display certificate for finite vectors. -/
def vectorDecimal4DisplaysAs {n : ℕ} (x d : Fin n → ℝ) : Prop :=
  ∀ i, decimal4DisplaysAs (x i) (d i)

/-- The four-decimal display half-ulp is positive. -/
theorem decimal4HalfUlp_pos : 0 < decimal4HalfUlp := by
  norm_num [decimal4HalfUlp]

/-- A displayed row certifies itself under the four-decimal interval predicate. -/
theorem decimal4DisplaysAs_self (x : ℝ) : decimal4DisplaysAs x x := by
  have hpos := decimal4HalfUlp_pos
  constructor <;> dsimp [decimal4DisplaysAs] <;> linarith

/-- Componentwise self-certification for the four-decimal display predicate. -/
theorem vectorDecimal4DisplaysAs_self {n : ℕ} (x : Fin n → ℝ) :
    vectorDecimal4DisplaysAs x x := by
  intro i
  exact decimal4DisplaysAs_self (x i)

/-- The Sun SPARCstation `m = 75` displayed row satisfies the local
four-decimal interval predicate. -/
theorem kahanAbsoluteProblem311_sunM75_display4_self :
    vectorDecimal4DisplaysAs kahanAbsoluteProblem311SunM75Outputs
      kahanAbsoluteProblem311SunM75Outputs :=
  vectorDecimal4DisplaysAs_self kahanAbsoluteProblem311SunM75Outputs

/-- The 486DX `m = 75` displayed row satisfies the local four-decimal interval
predicate. -/
theorem kahanAbsoluteProblem311_i486M75_display4_self :
    vectorDecimal4DisplaysAs kahanAbsoluteProblem311I486M75Outputs
      kahanAbsoluteProblem311I486M75Outputs :=
  vectorDecimal4DisplaysAs_self kahanAbsoluteProblem311I486M75Outputs

/-- The 486DX `m = 50` displayed row satisfies the local four-decimal interval
predicate. -/
theorem kahanAbsoluteProblem311_i486M50_display4_self :
    vectorDecimal4DisplaysAs kahanAbsoluteProblem311I486M50Outputs
      kahanAbsoluteProblem311I486M50Outputs :=
  vectorDecimal4DisplaysAs_self kahanAbsoluteProblem311I486M50Outputs

/-- A two-phase rounded trace for the Chapter 3 routine, after collecting all
square-root steps into `sqrtPhase` and all following square steps into
`squarePhase`.  The phase input is `x^2`, matching the MATLAB first line
`y = x.^2`. -/
noncomputable def kahanAbsolutePhaseTrace
    (sqrtPhase squarePhase : ℝ → ℝ) (x : ℝ) : ℝ :=
  squarePhase (sqrtPhase (x ^ 2))

/-- The six-input trace vector induced by a pair of rounded phases. -/
noncomputable def kahanAbsoluteProblem311TraceVector
    (sqrtPhase squarePhase : ℝ → ℝ) : Fin 6 → ℝ :=
  fun i => kahanAbsolutePhaseTrace sqrtPhase squarePhase
    (kahanAbsoluteProblem311Inputs i)

/-- Apply the finite round-to-even square-root primitive `k` times. -/
noncomputable def kahanAbsoluteFiniteSqrtSteps
    (fmt : FloatingPointFormat) : ℕ → ℝ → ℝ
  | 0, y => y
  | k + 1, y => fmt.finiteRoundToEvenSqrt
      (kahanAbsoluteFiniteSqrtSteps fmt k y)

/-- Peeling one finite square-root step from the front of an iterated
square-root chain. -/
theorem kahanAbsoluteFiniteSqrtSteps_succ_eq_steps_after_one
    (fmt : FloatingPointFormat) (k : ℕ) (y : ℝ) :
    kahanAbsoluteFiniteSqrtSteps fmt (k + 1) y =
      kahanAbsoluteFiniteSqrtSteps fmt k (fmt.finiteRoundToEvenSqrt y) := by
  induction k generalizing y with
  | zero =>
      simp [kahanAbsoluteFiniteSqrtSteps]
  | succ k ih =>
      change
        fmt.finiteRoundToEvenSqrt
            (kahanAbsoluteFiniteSqrtSteps fmt (k + 1) y) =
          fmt.finiteRoundToEvenSqrt
            (kahanAbsoluteFiniteSqrtSteps fmt k
              (fmt.finiteRoundToEvenSqrt y))
      exact congrArg fmt.finiteRoundToEvenSqrt (ih y)

/-- Apply the finite round-to-even squaring primitive `k` times. -/
noncomputable def kahanAbsoluteFiniteSquareSteps
    (fmt : FloatingPointFormat) : ℕ → ℝ → ℝ
  | 0, y => y
  | k + 1, y => kahanAbsoluteFiniteSquareSteps fmt k
      (fmt.finiteRoundToEvenOp BasicOp.mul y y)

/-- Concrete finite round-to-even version of the MATLAB routine: first round the
initial `x*x`, then take `m` rounded square roots and `m-1` rounded squares. -/
noncomputable def kahanAbsoluteFiniteRoundToEvenTrace
    (fmt : FloatingPointFormat) (m : ℕ) (x : ℝ) : ℝ :=
  kahanAbsoluteFiniteSquareSteps fmt (m - 1)
    (kahanAbsoluteFiniteSqrtSteps fmt m
      (fmt.finiteRoundToEvenOp BasicOp.mul x x))

/-- The Problem 3.11 six-input finite round-to-even trace vector. -/
noncomputable def kahanAbsoluteProblem311FiniteTraceVector
    (fmt : FloatingPointFormat) (m : ℕ) : Fin 6 → ℝ :=
  fun i => kahanAbsoluteFiniteRoundToEvenTrace fmt m
    (kahanAbsoluteProblem311Inputs i)

/-- The IEEE-double predecessor of `1`, the below-one fixed point that appears
in the Sun `m = 75` root phase. -/
noncomputable def kahanAbsoluteIeeeDoublePredOne : ℝ :=
  (1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ)

/-- The next IEEE-double value below `kahanAbsoluteIeeeDoublePredOne`, i.e. two
below-one ulps below `1`. -/
noncomputable def kahanAbsoluteIeeeDoubleTwoUlpsBelowOne : ℝ :=
  (1 : ℝ) - (2 : ℝ) ^ (-52 : ℤ)

/-- The fourth IEEE-double below-one ulp below `1`, reached by the second
rounded square in the predecessor-square cascade. -/
noncomputable def kahanAbsoluteIeeeDoubleFourUlpsBelowOne : ℝ :=
  (1 : ℝ) - (2 : ℝ) ^ (-51 : ℤ)

/-- The eighth IEEE-double below-one ulp below `1`, reached by the third
rounded square in the predecessor-square cascade. -/
noncomputable def kahanAbsoluteIeeeDoubleEightUlpsBelowOne : ℝ :=
  (1 : ℝ) - (2 : ℝ) ^ (-50 : ℤ)

/-- The sixteenth IEEE-double below-one ulp below `1`, reached by the fourth
rounded square in the predecessor-square cascade. -/
noncomputable def kahanAbsoluteIeeeDoubleSixteenUlpsBelowOne : ℝ :=
  (1 : ℝ) - (2 : ℝ) ^ (-49 : ℤ)

/-- The thirty-second IEEE-double below-one ulp below `1`, reached by the fifth
rounded square in the predecessor-square cascade. -/
noncomputable def kahanAbsoluteIeeeDoubleThirtyTwoUlpsBelowOne : ℝ :=
  (1 : ℝ) - (2 : ℝ) ^ (-48 : ℤ)

/-- The sixty-fourth IEEE-double below-one ulp below `1`, reached by the sixth
rounded square in the predecessor-square cascade. -/
noncomputable def kahanAbsoluteIeeeDoubleSixtyFourUlpsBelowOne : ℝ :=
  (1 : ℝ) - (2 : ℝ) ^ (-47 : ℤ)

/-- The one-hundred-twenty-eighth IEEE-double below-one ulp below `1`, reached
by the seventh rounded square in the predecessor-square cascade. -/
noncomputable def kahanAbsoluteIeeeDoubleOneHundredTwentyEightUlpsBelowOne : ℝ :=
  (1 : ℝ) - (2 : ℝ) ^ (-46 : ℤ)

/-- The two-hundred-fifty-sixth IEEE-double below-one ulp below `1`, reached by
the eighth rounded square in the predecessor-square cascade. -/
noncomputable def kahanAbsoluteIeeeDoubleTwoHundredFiftySixUlpsBelowOne : ℝ :=
  (1 : ℝ) - (2 : ℝ) ^ (-45 : ℤ)

/-- The five-hundred-twelfth IEEE-double below-one ulp below `1`, reached by
the ninth rounded square in the predecessor-square cascade. -/
noncomputable def kahanAbsoluteIeeeDoubleFiveHundredTwelveUlpsBelowOne : ℝ :=
  (1 : ℝ) - (2 : ℝ) ^ (-44 : ℤ)

/-- The one-thousand-twenty-fourth IEEE-double below-one ulp below `1`, reached
by the tenth rounded square in the predecessor-square cascade. -/
noncomputable def kahanAbsoluteIeeeDoubleOneThousandTwentyFourUlpsBelowOne : ℝ :=
  (1 : ℝ) - (2 : ℝ) ^ (-43 : ℤ)

/-- The two-thousand-forty-eighth IEEE-double below-one ulp below `1`, reached
by the eleventh rounded square in the predecessor-square cascade. -/
noncomputable def kahanAbsoluteIeeeDoubleTwoThousandFortyEightUlpsBelowOne : ℝ :=
  (1 : ℝ) - (2 : ℝ) ^ (-42 : ℤ)

/-- The four-thousand-ninety-sixth IEEE-double below-one ulp below `1`, reached
by the twelfth rounded square in the predecessor-square cascade. -/
noncomputable def kahanAbsoluteIeeeDoubleFourThousandNinetySixUlpsBelowOne : ℝ :=
  (1 : ℝ) - (2 : ℝ) ^ (-41 : ℤ)

/-- The eight-thousand-one-hundred-ninety-second IEEE-double below-one ulp below
`1`, reached by the thirteenth rounded square in the predecessor-square
cascade. -/
noncomputable def kahanAbsoluteIeeeDoubleEightThousandOneHundredNinetyTwoUlpsBelowOne : ℝ :=
  (1 : ℝ) - (2 : ℝ) ^ (-40 : ℤ)

/-- The sixteen-thousand-three-hundred-eighty-fourth IEEE-double below-one ulp
below `1`, reached by the fourteenth rounded square in the predecessor-square
cascade. -/
noncomputable def kahanAbsoluteIeeeDoubleSixteenThousandThreeHundredEightyFourUlpsBelowOne : ℝ :=
  (1 : ℝ) - (2 : ℝ) ^ (-39 : ℤ)

/-- The thirty-two-thousand-seven-hundred-sixty-eighth IEEE-double below-one
ulp below `1`, reached by the fifteenth rounded square in the
predecessor-square cascade. -/
noncomputable def kahanAbsoluteIeeeDoubleThirtyTwoThousandSevenHundredSixtyEightUlpsBelowOne : ℝ :=
  (1 : ℝ) - (2 : ℝ) ^ (-38 : ℤ)

/-- The sixty-five-thousand-five-hundred-thirty-sixth IEEE-double below-one
ulp below `1`, reached by the sixteenth rounded square in the
predecessor-square cascade. -/
noncomputable def kahanAbsoluteIeeeDoubleSixtyFiveThousandFiveHundredThirtySixUlpsBelowOne : ℝ :=
  (1 : ℝ) - (2 : ℝ) ^ (-37 : ℤ)

/-- The one-hundred-thirty-one-thousand-seventy-second IEEE-double below-one
ulp below `1`, reached by the seventeenth rounded square in the
predecessor-square cascade. -/
noncomputable def kahanAbsoluteIeeeDoubleOneHundredThirtyOneThousandSeventyTwoUlpsBelowOne : ℝ :=
  (1 : ℝ) - (2 : ℝ) ^ (-36 : ℤ)

/-- The two-hundred-sixty-two-thousand-one-hundred-forty-fourth IEEE-double
below-one ulp below `1`, reached by the eighteenth rounded square in the
predecessor-square cascade. -/
noncomputable def kahanAbsoluteIeeeDoubleTwoHundredSixtyTwoThousandOneHundredFortyFourUlpsBelowOne : ℝ :=
  (1 : ℝ) - (2 : ℝ) ^ (-35 : ℤ)

/-- The five-hundred-twenty-four-thousand-two-hundred-eighty-eighth IEEE-double
below-one ulp below `1`, reached by the nineteenth rounded square in the
predecessor-square cascade. -/
noncomputable def kahanAbsoluteIeeeDoubleFiveHundredTwentyFourThousandTwoHundredEightyEightUlpsBelowOne : ℝ :=
  (1 : ℝ) - (2 : ℝ) ^ (-34 : ℤ)

/-- The one-million-forty-eight-thousand-five-hundred-seventy-sixth
IEEE-double below-one ulp below `1`, reached by the twentieth rounded square in
the predecessor-square cascade. -/
noncomputable def kahanAbsoluteIeeeDoubleOneMillionFortyEightThousandFiveHundredSeventySixUlpsBelowOne : ℝ :=
  (1 : ℝ) - (2 : ℝ) ^ (-33 : ℤ)

/-- The two-million-ninety-seven-thousand-one-hundred-fifty-second IEEE-double
below-one ulp below `1`, reached by the twenty-first rounded square in the
predecessor-square cascade. -/
noncomputable def kahanAbsoluteIeeeDoubleTwoMillionNinetySevenThousandOneHundredFiftyTwoUlpsBelowOne : ℝ :=
  (1 : ℝ) - (2 : ℝ) ^ (-32 : ℤ)

/-- The four-million-one-hundred-ninety-four-thousand-three-hundred-fourth
IEEE-double below-one ulp below `1`, reached by the twenty-second rounded
square in the predecessor-square cascade. -/
noncomputable def kahanAbsoluteIeeeDoubleFourMillionOneHundredNinetyFourThousandThreeHundredFourUlpsBelowOne : ℝ :=
  (1 : ℝ) - (2 : ℝ) ^ (-31 : ℤ)

/-- The eight-million-three-hundred-eighty-eight-thousand-six-hundred-eighth
IEEE-double below-one ulp below `1`, reached by the twenty-third rounded
square in the predecessor-square cascade. -/
noncomputable def kahanAbsoluteIeeeDoubleEightMillionThreeHundredEightyEightThousandSixHundredEightUlpsBelowOne : ℝ :=
  (1 : ℝ) - (2 : ℝ) ^ (-30 : ℤ)

/-- The sixteen-million-seven-hundred-seventy-seven-thousand-two-hundred-sixteenth
IEEE-double below-one ulp below `1`, reached by the twenty-fourth rounded
square in the predecessor-square cascade. -/
noncomputable def kahanAbsoluteIeeeDoubleSixteenMillionSevenHundredSeventySevenThousandTwoHundredSixteenUlpsBelowOne : ℝ :=
  (1 : ℝ) - (2 : ℝ) ^ (-29 : ℤ)

/-- The thirty-three-million-five-hundred-fifty-four-thousand-four-hundred-thirty-second
IEEE-double below-one ulp below `1`, reached by the twenty-fifth rounded
square in the predecessor-square cascade. -/
noncomputable def kahanAbsoluteIeeeDoubleThirtyThreeMillionFiveHundredFiftyFourThousandFourHundredThirtyTwoUlpsBelowOne : ℝ :=
  (1 : ℝ) - (2 : ℝ) ^ (-28 : ℤ)

/-- The sixty-seven-million-one-hundred-eight-thousand-eight-hundred-sixty-fourth
IEEE-double below-one ulp below `1`, reached by the twenty-sixth rounded
square in the predecessor-square cascade. -/
noncomputable def kahanAbsoluteIeeeDoubleSixtySevenMillionOneHundredEightThousandEightHundredSixtyFourUlpsBelowOne : ℝ :=
  (1 : ℝ) - (2 : ℝ) ^ (-27 : ℤ)

/-- The one-hundred-thirty-four-million-two-hundred-seventeen-thousand-seven-hundred-twenty-eighth
IEEE-double below-one ulp below `1`, reached by the twenty-seventh rounded
square in the predecessor-square cascade. -/
noncomputable def kahanAbsoluteIeeeDoubleOneHundredThirtyFourMillionTwoHundredSeventeenThousandSevenHundredTwentyEightUlpsBelowOne : ℝ :=
  (1 : ℝ) - (2 : ℝ) ^ (-26 : ℤ)

/-- The two-hundred-sixty-eight-million-four-hundred-thirty-five-thousand-four-hundred-fifty-fourth
IEEE-double below-one ulp below `1`, reached by the twenty-eighth rounded
square in the predecessor-square cascade.  This is the exact representable
square of `1 - 2^-26`, not the endpoint `1 - 2^-25`. -/
noncomputable def kahanAbsoluteIeeeDoubleTwoHundredSixtyEightMillionFourHundredThirtyFiveThousandFourHundredFiftyFourUlpsBelowOne : ℝ :=
  (1 : ℝ) - 134217727 * (2 : ℝ) ^ (-52 : ℤ)

/-- The five-hundred-thirty-six-million-eight-hundred-seventy-thousand-nine-hundredth
IEEE-double below-one ulp below `1`, reached by the twenty-ninth rounded
square in the predecessor-square cascade.  This is the upper adjacent
IEEE-double endpoint to the exact square of
`1 - 134217727 * 2^-52`. -/
noncomputable def kahanAbsoluteIeeeDoubleFiveHundredThirtySixMillionEightHundredSeventyThousandNineHundredUlpsBelowOne : ℝ :=
  (1 : ℝ) - 536870900 * (2 : ℝ) ^ (-53 : ℤ)

/-- The one-billion-seventy-three-million-seven-hundred-forty-one-thousand-seven-hundred-sixty-eighth
IEEE-double below-one ulp below `1`, reached by the thirtieth rounded square in
the predecessor-square cascade. -/
noncomputable def kahanAbsoluteIeeeDoubleOneBillionSeventyThreeMillionSevenHundredFortyOneThousandSevenHundredSixtyEightUlpsBelowOne : ℝ :=
  (1 : ℝ) - 1073741768 * (2 : ℝ) ^ (-53 : ℤ)

/-- The two-billion-one-hundred-forty-seven-million-four-hundred-eighty-three-thousand-four-hundred-eighth
IEEE-double below-one ulp below `1`, reached by the thirty-first rounded square
in the predecessor-square cascade. -/
noncomputable def kahanAbsoluteIeeeDoubleTwoBillionOneHundredFortySevenMillionFourHundredEightyThreeThousandFourHundredEightUlpsBelowOne : ℝ :=
  (1 : ℝ) - 2147483408 * (2 : ℝ) ^ (-53 : ℤ)

/-- The four-billion-two-hundred-ninety-four-million-nine-hundred-sixty-six-thousand-three-hundred-fourth
IEEE-double below-one ulp below `1`, reached by the thirty-second rounded
square in the predecessor-square cascade. -/
noncomputable def kahanAbsoluteIeeeDoubleFourBillionTwoHundredNinetyFourMillionNineHundredSixtySixThousandThreeHundredFourUlpsBelowOne : ℝ :=
  (1 : ℝ) - 4294966304 * (2 : ℝ) ^ (-53 : ℤ)

/-- The eight-billion-five-hundred-eighty-nine-million-nine-hundred-thirty-thousand-five-hundred-sixtieth
IEEE-double below-one ulp below `1`, reached by the thirty-third rounded square
in the predecessor-square cascade. -/
noncomputable def kahanAbsoluteIeeeDoubleEightBillionFiveHundredEightyNineMillionNineHundredThirtyThousandFiveHundredSixtyUlpsBelowOne : ℝ :=
  (1 : ℝ) - 8589930560 * (2 : ℝ) ^ (-53 : ℤ)

/-- The seventeen-billion-one-hundred-seventy-nine-million-eight-hundred-fifty-two-thousand-nine-hundred-twenty-eighth
IEEE-double below-one ulp below `1`, reached by the thirty-fourth rounded square
in the predecessor-square cascade. -/
noncomputable def kahanAbsoluteIeeeDoubleSeventeenBillionOneHundredSeventyNineMillionEightHundredFiftyTwoThousandNineHundredTwentyEightUlpsBelowOne : ℝ :=
  (1 : ℝ) - 17179852928 * (2 : ℝ) ^ (-53 : ℤ)

/-- The IEEE-double predecessor of `1` is a fixed point of the rounded
square-root wrapper. -/
theorem kahanAbsoluteIeeeDouble_sqrt_predOne :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenSqrt
        kahanAbsoluteIeeeDoublePredOne =
      kahanAbsoluteIeeeDoublePredOne := by
  simpa [kahanAbsoluteIeeeDoublePredOne] using
    FloatingPointFormat.problem2_9_direct_double_sqrt_rounds_to_predecessor

/-- Once the IEEE-double root phase reaches the predecessor of `1`, every
further rounded square-root step stays there. -/
theorem kahanAbsoluteFiniteSqrtSteps_ieeeDouble_predOne (k : ℕ) :
    kahanAbsoluteFiniteSqrtSteps FloatingPointFormat.ieeeDoubleFormat k
        kahanAbsoluteIeeeDoublePredOne =
      kahanAbsoluteIeeeDoublePredOne := by
  induction k with
  | zero =>
      simp [kahanAbsoluteFiniteSqrtSteps]
  | succ k ih =>
      simp [kahanAbsoluteFiniteSqrtSteps, ih, kahanAbsoluteIeeeDouble_sqrt_predOne]

/-- Squaring `0` in the finite IEEE-double operation wrapper returns `0`. -/
theorem kahanAbsoluteIeeeDouble_square_zero :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp
        BasicOp.mul (0 : ℝ) 0 =
      0 := by
  have hfin :
      FloatingPointFormat.ieeeDoubleFormat.finiteSystem
        (BasicOp.exact BasicOp.mul (0 : ℝ) 0) := by
    norm_num [BasicOp.exact]
    exact FloatingPointFormat.ieeeDoubleFormat.finiteSystem_zero
  have h :=
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.mul) (x := (0 : ℝ)) (y := (0 : ℝ)) hfin
  simpa [BasicOp.exact] using h

/-- Once the IEEE-double square phase reaches `0`, every further rounded square
step stays at `0`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_zero (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat k
        (0 : ℝ) =
      0 := by
  induction k with
  | zero =>
      simp [kahanAbsoluteFiniteSquareSteps]
  | succ k ih =>
      simp [kahanAbsoluteFiniteSquareSteps, kahanAbsoluteIeeeDouble_square_zero, ih]

/-- The twenty-eighth rounded IEEE-double square in the predecessor-square
cascade is exactly representable:
`fl((1 - 2^-26)^2) = 1 - 134217727 * 2^-52`. -/
theorem kahanAbsoluteIeeeDouble_square_oneHundredThirtyFourMillionTwoHundredSeventeenThousandSevenHundredTwentyEightUlpsBelowOne_eq_twoHundredSixtyEightMillionFourHundredThirtyFiveThousandFourHundredFiftyFourUlpsBelowOne :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp
        BasicOp.mul kahanAbsoluteIeeeDoubleOneHundredThirtyFourMillionTwoHundredSeventeenThousandSevenHundredTwentyEightUlpsBelowOne
          kahanAbsoluteIeeeDoubleOneHundredThirtyFourMillionTwoHundredSeventeenThousandSevenHundredTwentyEightUlpsBelowOne =
      kahanAbsoluteIeeeDoubleTwoHundredSixtyEightMillionFourHundredThirtyFiveThousandFourHundredFiftyFourUlpsBelowOne := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let x : ℝ := BasicOp.exact BasicOp.mul
    kahanAbsoluteIeeeDoubleOneHundredThirtyFourMillionTwoHundredSeventeenThousandSevenHundredTwentyEightUlpsBelowOne
      kahanAbsoluteIeeeDoubleOneHundredThirtyFourMillionTwoHundredSeventeenThousandSevenHundredTwentyEightUlpsBelowOne
  have hx_value :
      x = kahanAbsoluteIeeeDoubleTwoHundredSixtyEightMillionFourHundredThirtyFiveThousandFourHundredFiftyFourUlpsBelowOne := by
    simp [x, BasicOp.exact,
      kahanAbsoluteIeeeDoubleOneHundredThirtyFourMillionTwoHundredSeventeenThousandSevenHundredTwentyEightUlpsBelowOne,
      kahanAbsoluteIeeeDoubleTwoHundredSixtyEightMillionFourHundredThirtyFiveThousandFourHundredFiftyFourUlpsBelowOne]
    norm_num [zpow_neg]
  have hfinite : fmt.finiteSystem x := by
    refine Or.inr (Or.inl ?_)
    refine ⟨false, fmt.maxNormalMantissa - 268435453, (0 : ℤ), ?_, ?_, ?_⟩
    · norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.mantissaInRange,
        FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
    · norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
        FloatingPointFormat.exponentInRange]
    · rw [hx_value]
      norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
        FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
        FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa,
        kahanAbsoluteIeeeDoubleTwoHundredSixtyEightMillionFourHundredThirtyFiveThousandFourHundredFiftyFourUlpsBelowOne,
        zpow_neg]
  have hround : fmt.finiteRoundToEven x = x :=
    fmt.finiteRoundToEven_eq_self_of_finiteSystem hfinite
  simpa [FloatingPointFormat.finiteRoundToEvenOp, x, fmt, hx_value] using hround

/-- Peeling one rounded square step from `1 - 2^-26` rewrites the remaining
IEEE-double square cascade to the cascade from the exact twenty-eighth state
`1 - 134217727 * 2^-52`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_oneHundredThirtyFourMillionTwoHundredSeventeenThousandSevenHundredTwentyEightUlpsBelowOne_succ
    (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 1) kahanAbsoluteIeeeDoubleOneHundredThirtyFourMillionTwoHundredSeventeenThousandSevenHundredTwentyEightUlpsBelowOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleTwoHundredSixtyEightMillionFourHundredThirtyFiveThousandFourHundredFiftyFourUlpsBelowOne := by
  simp [kahanAbsoluteFiniteSquareSteps,
    kahanAbsoluteIeeeDouble_square_oneHundredThirtyFourMillionTwoHundredSeventeenThousandSevenHundredTwentyEightUlpsBelowOne_eq_twoHundredSixtyEightMillionFourHundredThirtyFiveThousandFourHundredFiftyFourUlpsBelowOne]

/-- If the exact square of the current IEEE-double square phase is strictly
below half the smallest subnormal magnitude, the finite round-to-even squaring
operation underflows to zero. -/
theorem kahanAbsoluteIeeeDouble_square_eq_zero_of_abs_mul_lt_half_minSubnormal
    {x : ℝ}
    (hsmall :
      |x * x| < (1 / 2 : ℝ) *
        FloatingPointFormat.ieeeDoubleFormat.minSubnormalMagnitude) :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp
        BasicOp.mul x x =
      0 := by
  have hnear :=
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp_nearestRoundingToFinite
      BasicOp.mul x x
  exact
    FloatingPointFormat.ieeeDoubleFormat.nearestRoundingToFinite_eq_zero_of_abs_lt_half_minSubnormalMagnitude
      hnear (by simpa [BasicOp.exact, pow_two] using hsmall)

/-- Once one exact square in the IEEE-double square phase is strictly below the
half-min-subnormal threshold, that rounded square is zero and all later square
steps stay zero. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_eq_zero_of_abs_mul_lt_half_minSubnormal
    (k : ℕ) {x : ℝ}
    (hsmall :
      |x * x| < (1 / 2 : ℝ) *
        FloatingPointFormat.ieeeDoubleFormat.minSubnormalMagnitude) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 1) x =
      0 := by
  have hzero :=
    kahanAbsoluteIeeeDouble_square_eq_zero_of_abs_mul_lt_half_minSubnormal
      (x := x) hsmall
  simp [kahanAbsoluteFiniteSquareSteps, hzero,
    kahanAbsoluteFiniteSquareSteps_ieeeDouble_zero]

/-- The reduced Sun `m = 75` finite-trace vector after discharging the exact
initial square and the first exact square-root step. -/
noncomputable def kahanAbsoluteProblem311IeeeDoubleReducedM75TraceVector :
    Fin 6 → ℝ :=
  fun i =>
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat 74
      (kahanAbsoluteFiniteSqrtSteps FloatingPointFormat.ieeeDoubleFormat 74
        (kahanAbsoluteProblem311Inputs i))

/-- The exact Lean target for closing the Sun SPARCstation `m = 75` finite
IEEE-double trace route.  This proposition is intentionally not proved here:
it isolates the remaining 75-step square-root/square platform computation. -/
noncomputable def kahanAbsoluteProblem311SunM75IeeeDoubleTraceTarget : Prop :=
  kahanAbsoluteProblem311FiniteTraceVector
    FloatingPointFormat.ieeeDoubleFormat 75 =
      kahanAbsoluteProblem311SunM75Outputs

/-- The smaller equivalent target for the Sun SPARCstation `m = 75`
IEEE-double route after the exact first square-root reduction. -/
noncomputable def kahanAbsoluteProblem311SunM75IeeeDoubleReducedTraceTarget :
    Prop :=
  kahanAbsoluteProblem311IeeeDoubleReducedM75TraceVector =
    kahanAbsoluteProblem311SunM75Outputs

/-- Once the concrete Sun `m = 75` IEEE-double trace target is proved, the
reported four-decimal display row follows from the local display interval
certificate. -/
theorem kahanAbsoluteProblem311_sunM75_display4_of_ieeeDouble_trace_target
    (htrace : kahanAbsoluteProblem311SunM75IeeeDoubleTraceTarget) :
    vectorDecimal4DisplaysAs
      (kahanAbsoluteProblem311FiniteTraceVector
        FloatingPointFormat.ieeeDoubleFormat 75)
      kahanAbsoluteProblem311SunM75Outputs := by
  change kahanAbsoluteProblem311FiniteTraceVector
    FloatingPointFormat.ieeeDoubleFormat 75 =
      kahanAbsoluteProblem311SunM75Outputs at htrace
  intro i
  rw [htrace]
  exact decimal4DisplaysAs_self _

/-- Conditional explanation of the Sun SPARCstation `m = 75` output pattern.

If the combined square-root and square phases satisfy the same source-style
threshold laws as the HP 48G surrogate, but applied to the initial value `x^2`,
then the six displayed inputs produce exactly the reported
`0,0,0,1,1,1` row. -/
theorem kahanAbsoluteProblem311_sunM75_outputs_of_phase_laws
    {sqrtPhase squarePhase : ℝ → ℝ}
    (hlaws : Hp48gSqrtSquareSurrogateLaws sqrtPhase squarePhase) :
    ∀ i : Fin 6,
      kahanAbsolutePhaseTrace sqrtPhase squarePhase
          (kahanAbsoluteProblem311Inputs i) =
        kahanAbsoluteProblem311SunM75Outputs i := by
  have hphase : ∀ t : ℝ, 0 ≤ t →
      squarePhase (sqrtPhase t) = hp48gSqrtSquareSurrogate t := by
    intro t ht
    simpa [hp48gSqrtSquareTrace] using
      hp48gSqrtSquareTrace_eq_surrogate_of_laws hlaws ht
  intro i
  fin_cases i <;>
    simp [kahanAbsolutePhaseTrace, kahanAbsoluteProblem311Inputs,
      kahanAbsoluteProblem311SunM75Outputs] <;>
    rw [hphase _ (by norm_num)] <;>
    norm_num [hp48gSqrtSquareSurrogate]

/-- The conditional Sun `m = 75` trace also satisfies the four-decimal display
predicate for the displayed source row. -/
theorem kahanAbsoluteProblem311_sunM75_display4_of_phase_laws
    {sqrtPhase squarePhase : ℝ → ℝ}
    (hlaws : Hp48gSqrtSquareSurrogateLaws sqrtPhase squarePhase) :
    vectorDecimal4DisplaysAs
      (kahanAbsoluteProblem311TraceVector sqrtPhase squarePhase)
      kahanAbsoluteProblem311SunM75Outputs := by
  intro i
  rw [kahanAbsoluteProblem311TraceVector,
    kahanAbsoluteProblem311_sunM75_outputs_of_phase_laws hlaws i]
  exact decimal4DisplaysAs_self _

/-- Phase laws sufficient to explain a rounded trace that collapses every
positive source input in the displayed experiment to `1`. -/
structure KahanAbsoluteAllOnePhaseLaws
    (sqrtPhase squarePhase : ℝ → ℝ) : Prop where
  sqrt_square_pos_eq_one :
    ∀ {x : ℝ}, 0 < x → sqrtPhase (x ^ 2) = 1
  square_one_eq_one :
    squarePhase 1 = 1

/-- Under all-one phase laws, every positive input is mapped to `1`. -/
theorem kahanAbsolutePhaseTrace_eq_one_of_allOne_laws
    {sqrtPhase squarePhase : ℝ → ℝ}
    (hlaws : KahanAbsoluteAllOnePhaseLaws sqrtPhase squarePhase)
    {x : ℝ} (hx : 0 < x) :
    kahanAbsolutePhaseTrace sqrtPhase squarePhase x = 1 := by
  rw [kahanAbsolutePhaseTrace, hlaws.sqrt_square_pos_eq_one hx,
    hlaws.square_one_eq_one]

/-- Conditional explanation of the 486DX `m = 75` output pattern.

Once the platform-specific rounded square-root phase has collapsed each
positive displayed input's `x^2` to `1`, the following square phase keeps it at
`1`, giving the reported all-ones row. -/
theorem kahanAbsoluteProblem311_i486M75_outputs_of_allOne_phase_laws
    {sqrtPhase squarePhase : ℝ → ℝ}
    (hlaws : KahanAbsoluteAllOnePhaseLaws sqrtPhase squarePhase) :
    ∀ i : Fin 6,
      kahanAbsolutePhaseTrace sqrtPhase squarePhase
          (kahanAbsoluteProblem311Inputs i) =
        kahanAbsoluteProblem311I486M75Outputs i := by
  intro i
  fin_cases i <;>
    simp [kahanAbsoluteProblem311Inputs, kahanAbsoluteProblem311I486M75Outputs] <;>
    exact kahanAbsolutePhaseTrace_eq_one_of_allOne_laws hlaws (by norm_num)

/-- The conditional 486DX `m = 75` trace also satisfies the four-decimal display
predicate for the displayed all-ones row. -/
theorem kahanAbsoluteProblem311_i486M75_display4_of_allOne_phase_laws
    {sqrtPhase squarePhase : ℝ → ℝ}
    (hlaws : KahanAbsoluteAllOnePhaseLaws sqrtPhase squarePhase) :
    vectorDecimal4DisplaysAs
      (kahanAbsoluteProblem311TraceVector sqrtPhase squarePhase)
      kahanAbsoluteProblem311I486M75Outputs := by
  intro i
  rw [kahanAbsoluteProblem311TraceVector,
    kahanAbsoluteProblem311_i486M75_outputs_of_allOne_phase_laws hlaws i]
  exact decimal4DisplaysAs_self _

end NumStability
