import NumStability.Algorithms.LeastSquares.Higham20Theorem20_7ActualAssembly

/-!
# Higham Theorem 19.6: canonical actual-source exports

The bare-`FPModel`, source-constructed, fully swap-aware implementation proof
was originally assembled while developing Theorem 20.7.  These Chapter 19
exports make that route discoverable under its source theorem: no
`StageDataReady`, `StrongStageModel`, row-policy, or target-bearing local
budget is assumed.
-/

namespace NumStability

namespace Theorem19_6

/-- The actual source-constructed pivoted stored-QR trace produces the
rowwise backward-error certificate. -/
alias sourceConstructed_actual_rowwise_backward_error :=
  Theorem20_7.fl_sourceConstructedPivotedStoredQR_actual_rowwise_backward_error

/-- The actual source-constructed pivoted stored-QR trace, with the explicit
numerical compression guard, yields the final linear-rate Theorem 19.6
bound. -/
alias sourceConstructed_actual_closed_linearRate :=
  Theorem20_7.higham19_6_sourceConstructed_actual_closed_linearRate

end Theorem19_6

end NumStability
