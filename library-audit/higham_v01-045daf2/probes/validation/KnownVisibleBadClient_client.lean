import NumStability.Analysis.Rounding

#check NumStability.gamma_nonneg

-- Deliberately ill-typed negative control: visibility must not be confused with
-- successful client use.
example : False := by
  exact True.intro
