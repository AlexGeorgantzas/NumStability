import Mathlib

open scoped BigOperators

namespace HighamBench

abbrev P54Vector (n : ℕ) := Fin n → ℝ

/-- The squared modified coordinate from equation (3.2). -/
noncomputable def p54SecularWeight {n : ℕ}
    (d lambda : P54Vector n) (i : Fin n) : ℝ :=
  (∏ j, (lambda j - d i)) /
    (∏ j ∈ Finset.univ.erase i, (d j - d i))

/-- The secular function used in Lemma 1 and Sections 3--4. -/
noncomputable def p54Secular {n : ℕ}
    (d weight : P54Vector n) (x : ℝ) : ℝ :=
  1 + ∑ i, weight i / (d i - x)

/-- The product formula (3.3) for the modified coordinate. -/
noncomputable def p54ModifiedCoordinate {n : ℕ}
    (d lambda : P54Vector n) (i : Fin n) : ℝ :=
  Real.sqrt (p54SecularWeight d lambda i)

/-- The product on either side of the determinant identity preceding (3.2). -/
noncomputable def p54Characteristic {n : ℕ}
    (v : P54Vector n) : Polynomial ℝ :=
  ∏ i, (Polynomial.C (v i) - Polynomial.X)

/-- The factor left after removing the pole indexed by `i` from the diagonal
characteristic product. -/
noncomputable def p54DeletedCharacteristic {n : ℕ}
    (d : P54Vector n) (i : Fin n) : Polynomial ℝ :=
  ∏ j ∈ Finset.univ.erase i, (Polynomial.C (d j) - Polynomial.X)

end HighamBench
