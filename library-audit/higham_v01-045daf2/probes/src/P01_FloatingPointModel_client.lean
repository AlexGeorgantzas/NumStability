import NumStability.FloatingPoint.Model

#check NumStability.FPModel.model_basicOp

open NumStability

example (fp : FPModel) (op : BasicOp) (x y : ℝ)
    (hy : op = BasicOp.div → y ≠ 0) :
    ∃ δ : ℝ,
      |δ| ≤ fp.u ∧
      fp.round op x y = BasicOp.exact op x y * (1 + δ) := by
  exact fp.model_basicOp op x y hy
