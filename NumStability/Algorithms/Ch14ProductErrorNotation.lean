import NumStability.Algorithms.MatMul
import NumStability.Algorithms.MatrixInversion

namespace NumStability

open scoped BigOperators

/-!
# Higham Chapter 14: product-error notation for arbitrary evaluation trees

Higham writes `Delta(A1, ..., Ak)` for the error made while evaluating a
matrix product in any binary order.  The legacy square `Ch14ProductTree`
records that order, and the source-facing `Ch14RectProductTree` below extends
the construction to heterogeneous compatible dimensions.  Every internal
node is evaluated by the repository's concrete `fl_matMul`.

The error majorant below is recursive.  This is intentional: different leaves
have different depths in an arbitrary product tree, so a single flat gamma
coefficient would discard the evaluation-order information.  The recurrence
uses only the absolute exact-product trees, previously accumulated envelopes,
and the local `matMul_error_bound` certificate at each internal node.
-/

/-- A full binary parenthesization of square real matrices.  Leaves are the
factors, and each node is one matrix multiplication in the chosen evaluation
order. -/
inductive Ch14ProductTree (n : Nat) where
  | leaf (A : Fin n -> Fin n -> Real) : Ch14ProductTree n
  | node (left right : Ch14ProductTree n) : Ch14ProductTree n

namespace Ch14ProductTree

/-- The factors in their left-to-right source order. -/
def factors {n : Nat} : Ch14ProductTree n -> List (Fin n -> Fin n -> Real)
  | leaf A => [A]
  | node left right => factors left ++ factors right

/-- Number of source factors in a full binary product tree. -/
def leafCount {n : Nat} : Ch14ProductTree n -> Nat
  | leaf _ => 1
  | node left right => leafCount left + leafCount right

/-- Canonical right-associated exact product of a source factor list.  The
empty product is the identity; product trees themselves are always nonempty. -/
noncomputable def exactListProduct {n : Nat} :
    List (Fin n -> Fin n -> Real) -> Fin n -> Fin n -> Real
  | [] => idMatrix n
  | A :: rest => matMul n A (exactListProduct rest)

/-- Evaluate the selected parenthesization in exact arithmetic. -/
noncomputable def exactEval {n : Nat} :
    Ch14ProductTree n -> Fin n -> Fin n -> Real
  | leaf A => A
  | node left right => matMul n (exactEval left) (exactEval right)

/-- Evaluate every internal multiplication in floating-point arithmetic. -/
noncomputable def roundedEval {n : Nat} (fp : FPModel) :
    Ch14ProductTree n -> Fin n -> Fin n -> Real
  | leaf A => A
  | node left right =>
      fl_matMul fp n n n (roundedEval fp left) (roundedEval fp right)

/-- The exact product tree after replacing every source factor by its
componentwise absolute value. -/
noncomputable def exactAbsProduct {n : Nat} :
    Ch14ProductTree n -> Fin n -> Fin n -> Real
  | leaf A => absMatrix n A
  | node left right =>
      matMul n (exactAbsProduct left) (exactAbsProduct right)

/-- Higham's `Delta(A1, ..., Ak)` for the selected evaluation tree. -/
noncomputable def productDelta {n : Nat} (fp : FPModel)
    (tree : Ch14ProductTree n) : Fin n -> Fin n -> Real :=
  fun i j => roundedEval fp tree i j - exactEval tree i j

/-- Recursive componentwise product-error envelope.

At a node, let `B_left = exactAbsProduct left + errorEnvelope left`, and
similarly on the right.  The three terms are respectively:

* the local `fl_matMul` error `gamma_n B_left B_right`;
* the propagated left-subtree error `E_left B_right`;
* the propagated right-subtree error `|P_left| E_right`.

Thus all coefficients and all effects of the chosen parenthesization remain
explicit. -/
noncomputable def errorEnvelope {n : Nat} (fp : FPModel) :
    Ch14ProductTree n -> Fin n -> Fin n -> Real
  | leaf _ => fun _ _ => 0
  | node left right =>
      let Eleft := errorEnvelope fp left
      let Eright := errorEnvelope fp right
      let Bleft := fun i j => exactAbsProduct left i j + Eleft i j
      let Bright := fun i j => exactAbsProduct right i j + Eright i j
      fun i j =>
        gamma fp n * matMul n Bleft Bright i j +
          matMul n Eleft Bright i j +
          matMul n (exactAbsProduct left) Eright i j

@[simp] theorem factors_leaf {n : Nat} (A : Fin n -> Fin n -> Real) :
    factors (.leaf A) = [A] := rfl

@[simp] theorem factors_node {n : Nat}
    (left right : Ch14ProductTree n) :
    factors (.node left right) = factors left ++ factors right := rfl

@[simp] theorem leafCount_leaf {n : Nat} (A : Fin n -> Fin n -> Real) :
    leafCount (.leaf A) = 1 := rfl

@[simp] theorem leafCount_node {n : Nat}
    (left right : Ch14ProductTree n) :
    leafCount (.node left right) = leafCount left + leafCount right := rfl

@[simp] theorem exactListProduct_nil {n : Nat} :
    exactListProduct ([] : List (Fin n -> Fin n -> Real)) = idMatrix n := rfl

@[simp] theorem exactListProduct_cons {n : Nat}
    (A : Fin n -> Fin n -> Real)
    (rest : List (Fin n -> Fin n -> Real)) :
    exactListProduct (A :: rest) = matMul n A (exactListProduct rest) := rfl

/-- Canonical exact products distribute over concatenation. -/
theorem exactListProduct_append {n : Nat}
    (left right : List (Fin n -> Fin n -> Real)) :
    exactListProduct (left ++ right) =
      matMul n (exactListProduct left) (exactListProduct right) := by
  induction left with
  | nil =>
      simp only [List.nil_append, exactListProduct_nil]
      exact (matMul_id_left n (exactListProduct right)).symm
  | cons A rest ih =>
      simp only [List.cons_append, exactListProduct_cons]
      rw [ih]
      exact (matMul_assoc n A (exactListProduct rest) (exactListProduct right)).symm

@[simp] theorem exactEval_leaf {n : Nat} (A : Fin n -> Fin n -> Real) :
    exactEval (.leaf A) = A := rfl

@[simp] theorem exactEval_node {n : Nat}
    (left right : Ch14ProductTree n) :
    exactEval (.node left right) = matMul n (exactEval left) (exactEval right) := rfl

@[simp] theorem roundedEval_leaf {n : Nat} (fp : FPModel)
    (A : Fin n -> Fin n -> Real) :
    roundedEval fp (.leaf A) = A := rfl

@[simp] theorem roundedEval_node {n : Nat} (fp : FPModel)
    (left right : Ch14ProductTree n) :
    roundedEval fp (.node left right) =
      fl_matMul fp n n n (roundedEval fp left) (roundedEval fp right) := rfl

@[simp] theorem exactAbsProduct_leaf {n : Nat}
    (A : Fin n -> Fin n -> Real) :
    exactAbsProduct (.leaf A) = absMatrix n A := rfl

@[simp] theorem exactAbsProduct_node {n : Nat}
    (left right : Ch14ProductTree n) :
    exactAbsProduct (.node left right) =
      matMul n (exactAbsProduct left) (exactAbsProduct right) := rfl

@[simp] theorem errorEnvelope_leaf {n : Nat} (fp : FPModel)
    (A : Fin n -> Fin n -> Real) :
    errorEnvelope fp (.leaf A) = fun _ _ => 0 := rfl

/-- Exact evaluation of a product tree is the canonical product of its source
factor list.  Consequently, exact arithmetic is independent of the selected
binary parenthesization. -/
theorem exactEval_eq_exactListProduct_factors {n : Nat}
    (tree : Ch14ProductTree n) :
    exactEval tree = exactListProduct (factors tree) := by
  induction tree with
  | leaf A =>
      simp only [exactEval_leaf, factors_leaf, exactListProduct_cons,
        exactListProduct_nil]
      exact (matMul_id_right n A).symm
  | node left right ihLeft ihRight =>
      simp only [exactEval_node, factors_node, exactListProduct_append,
        ihLeft, ihRight]

/-- Two full binary parenthesizations of the same left-to-right factors have
the same exact product. -/
theorem exactEval_eq_of_factors_eq {n : Nat}
    {left right : Ch14ProductTree n} (hFactors : factors left = factors right) :
    exactEval left = exactEval right := by
  rw [exactEval_eq_exactListProduct_factors,
    exactEval_eq_exactListProduct_factors, hFactors]

/-- The explicit product perturbation gives the source decomposition
`fl(A1 ... Ak) = A1 ... Ak + Delta(A1, ..., Ak)`. -/
theorem roundedEval_eq_exactEval_add_productDelta {n : Nat} (fp : FPModel)
    (tree : Ch14ProductTree n) :
    roundedEval fp tree =
      fun i j => exactEval tree i j + productDelta fp tree i j := by
  ext i j
  simp only [productDelta]
  ring

/-- Each internal node carries the standard local componentwise
`fl_matMul` certificate, with no assumed product-error conclusion. -/
theorem roundedEval_node_local_MatProdError {n : Nat} (fp : FPModel)
    (left right : Ch14ProductTree n) (hn : gammaValid fp n) :
    MatProdError n
      (roundedEval fp (.node left right))
      (matMul n (roundedEval fp left) (roundedEval fp right))
      (gamma fp n)
      (matMul n (absMatrix n (roundedEval fp left))
        (absMatrix n (roundedEval fp right))) := by
  intro i j
  simpa [roundedEval, matMul, absMatrix] using
    matMul_error_bound fp n n n (roundedEval fp left) (roundedEval fp right) hn i j

/-- Products of absolute-value factors are entrywise nonnegative. -/
theorem exactAbsProduct_nonneg {n : Nat} (tree : Ch14ProductTree n) :
    forall i j, 0 <= exactAbsProduct tree i j := by
  induction tree with
  | leaf A =>
      intro i j
      exact abs_nonneg (A i j)
  | node left right ihLeft ihRight =>
      intro i j
      simp only [exactAbsProduct_node, matMul]
      exact Finset.sum_nonneg fun k _ => mul_nonneg (ihLeft i k) (ihRight k j)

/-- The absolute exact evaluation is bounded by the exact product tree of the
absolute source factors. -/
theorem abs_exactEval_le_exactAbsProduct {n : Nat}
    (tree : Ch14ProductTree n) :
    forall i j, |exactEval tree i j| <= exactAbsProduct tree i j := by
  induction tree with
  | leaf A =>
      intro i j
      rfl
  | node left right ihLeft ihRight =>
      intro i j
      simp only [exactEval_node, exactAbsProduct_node, matMul]
      calc
        |Finset.univ.sum fun k : Fin n => exactEval left i k * exactEval right k j|
            <= Finset.univ.sum fun k : Fin n =>
              |exactEval left i k * exactEval right k j| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = Finset.univ.sum fun k : Fin n =>
              |exactEval left i k| * |exactEval right k j| := by
          apply Finset.sum_congr rfl
          intro k _
          exact abs_mul _ _
        _ <= Finset.univ.sum fun k : Fin n =>
              exactAbsProduct left i k * exactAbsProduct right k j := by
          apply Finset.sum_le_sum
          intro k _
          calc
            |exactEval left i k| * |exactEval right k j|
                <= exactAbsProduct left i k * |exactEval right k j| :=
              mul_le_mul_of_nonneg_right (ihLeft i k) (abs_nonneg _)
            _ <= exactAbsProduct left i k * exactAbsProduct right k j :=
              mul_le_mul_of_nonneg_left (ihRight k j)
                (exactAbsProduct_nonneg left i k)

/-- The recursively accumulated error envelope is entrywise nonnegative. -/
theorem errorEnvelope_nonneg {n : Nat} (fp : FPModel)
    (hn : gammaValid fp n) (tree : Ch14ProductTree n) :
    forall i j, 0 <= errorEnvelope fp tree i j := by
  induction tree with
  | leaf A =>
      intro i j
      simp
  | node left right ihLeft ihRight =>
      intro i j
      have hgamma : 0 <= gamma fp n := gamma_nonneg fp hn
      have hBleft : forall a b,
          0 <= exactAbsProduct left a b + errorEnvelope fp left a b := by
        intro a b
        exact add_nonneg (exactAbsProduct_nonneg left a b) (ihLeft a b)
      have hBright : forall a b,
          0 <= exactAbsProduct right a b + errorEnvelope fp right a b := by
        intro a b
        exact add_nonneg (exactAbsProduct_nonneg right a b) (ihRight a b)
      simp only [errorEnvelope]
      apply add_nonneg
      · apply add_nonneg
        · exact mul_nonneg hgamma <|
            Finset.sum_nonneg fun k _ => mul_nonneg (hBleft i k) (hBright k j)
        · exact Finset.sum_nonneg fun k _ => mul_nonneg (ihLeft i k) (hBright k j)
      · exact Finset.sum_nonneg fun k _ =>
          mul_nonneg (exactAbsProduct_nonneg left i k) (ihRight k j)

/-- A subtree's rounded value is bounded by its exact absolute-product tree
plus its recursively accumulated error envelope. -/
theorem abs_roundedEval_le_exactAbsProduct_add_errorEnvelope {n : Nat}
    (fp : FPModel) (tree : Ch14ProductTree n) (i j : Fin n)
    (hDelta : |productDelta fp tree i j| <= errorEnvelope fp tree i j) :
    |roundedEval fp tree i j| <=
      exactAbsProduct tree i j + errorEnvelope fp tree i j := by
  calc
    |roundedEval fp tree i j|
        = |exactEval tree i j + productDelta fp tree i j| := by
          congr 1
          simp only [productDelta]
          ring
    _ <= |exactEval tree i j| + |productDelta fp tree i j| := abs_add_le _ _
    _ <= exactAbsProduct tree i j + errorEnvelope fp tree i j :=
      add_le_add (abs_exactEval_le_exactAbsProduct tree i j) hDelta

/-- Main Chapter 14 product-notation theorem.  For every full binary
parenthesization, the concrete all-`fl_matMul` evaluation has error bounded by
the recursively propagated source-facing envelope. -/
theorem productDelta_abs_le_errorEnvelope {n : Nat} (fp : FPModel)
    (hn : gammaValid fp n) (tree : Ch14ProductTree n) :
    forall i j, |productDelta fp tree i j| <= errorEnvelope fp tree i j := by
  induction tree with
  | leaf A =>
      intro i j
      simp [productDelta]
  | node left right ihLeft ihRight =>
      intro i j
      let Lhat := roundedEval fp left
      let Rhat := roundedEval fp right
      let L := exactEval left
      let R := exactEval right
      let EL := errorEnvelope fp left
      let ER := errorEnvelope fp right
      let BL := fun a b => exactAbsProduct left a b + EL a b
      let BR := fun a b => exactAbsProduct right a b + ER a b
      have hgamma : 0 <= gamma fp n := gamma_nonneg fp hn
      have hEL : forall a b, 0 <= EL a b := by
        intro a b
        exact errorEnvelope_nonneg fp hn left a b
      have hER : forall a b, 0 <= ER a b := by
        intro a b
        exact errorEnvelope_nonneg fp hn right a b
      have hBL : forall a b, 0 <= BL a b := by
        intro a b
        exact add_nonneg (exactAbsProduct_nonneg left a b) (hEL a b)
      have hBR : forall a b, 0 <= BR a b := by
        intro a b
        exact add_nonneg (exactAbsProduct_nonneg right a b) (hER a b)
      have hLhat : forall a b, |Lhat a b| <= BL a b := by
        intro a b
        exact abs_roundedEval_le_exactAbsProduct_add_errorEnvelope
          fp left a b (ihLeft a b)
      have hRhat : forall a b, |Rhat a b| <= BR a b := by
        intro a b
        exact abs_roundedEval_le_exactAbsProduct_add_errorEnvelope
          fp right a b (ihRight a b)
      have hlocalMajorant :
          (Finset.univ.sum fun k : Fin n => |Lhat i k| * |Rhat k j|) <=
            matMul n BL BR i j := by
        simp only [matMul]
        apply Finset.sum_le_sum
        intro k _
        calc
          |Lhat i k| * |Rhat k j| <= BL i k * |Rhat k j| :=
            mul_le_mul_of_nonneg_right (hLhat i k) (abs_nonneg _)
          _ <= BL i k * BR k j :=
            mul_le_mul_of_nonneg_left (hRhat k j) (hBL i k)
      have hlocal :
          |fl_matMul fp n n n Lhat Rhat i j - matMul n Lhat Rhat i j| <=
            gamma fp n * matMul n BL BR i j := by
        have hraw := matMul_error_bound fp n n n Lhat Rhat hn i j
        have hraw' :
            |fl_matMul fp n n n Lhat Rhat i j - matMul n Lhat Rhat i j| <=
              gamma fp n *
                (Finset.univ.sum fun k : Fin n => |Lhat i k| * |Rhat k j|) := by
          simpa [matMul] using hraw
        exact hraw'.trans (mul_le_mul_of_nonneg_left hlocalMajorant hgamma)
      have hproductPropagation :
          |matMul n Lhat Rhat i j - matMul n L R i j| <=
            matMul n EL BR i j + matMul n (exactAbsProduct left) ER i j := by
        simp only [matMul]
        rw [<- Finset.sum_sub_distrib]
        calc
          |Finset.univ.sum fun k : Fin n => Lhat i k * Rhat k j - L i k * R k j|
              <= Finset.univ.sum fun k : Fin n =>
                |Lhat i k * Rhat k j - L i k * R k j| :=
            Finset.abs_sum_le_sum_abs _ _
          _ <= Finset.univ.sum fun k : Fin n =>
                (EL i k * BR k j + exactAbsProduct left i k * ER k j) := by
            apply Finset.sum_le_sum
            intro k _
            calc
              |Lhat i k * Rhat k j - L i k * R k j|
                  = |(Lhat i k - L i k) * Rhat k j +
                      L i k * (Rhat k j - R k j)| := by
                    congr 1
                    ring
              _ <= |(Lhat i k - L i k) * Rhat k j| +
                    |L i k * (Rhat k j - R k j)| := abs_add_le _ _
              _ = |Lhat i k - L i k| * |Rhat k j| +
                    |L i k| * |Rhat k j - R k j| := by
                    rw [abs_mul, abs_mul]
              _ <= EL i k * BR k j + exactAbsProduct left i k * ER k j := by
                    apply add_le_add
                    · calc
                        |Lhat i k - L i k| * |Rhat k j|
                            <= EL i k * |Rhat k j| :=
                          mul_le_mul_of_nonneg_right (ihLeft i k) (abs_nonneg _)
                        _ <= EL i k * BR k j :=
                          mul_le_mul_of_nonneg_left (hRhat k j) (hEL i k)
                    · calc
                        |L i k| * |Rhat k j - R k j|
                            <= exactAbsProduct left i k * |Rhat k j - R k j| :=
                          mul_le_mul_of_nonneg_right
                            (abs_exactEval_le_exactAbsProduct left i k) (abs_nonneg _)
                        _ <= exactAbsProduct left i k * ER k j :=
                          mul_le_mul_of_nonneg_left (ihRight k j)
                            (exactAbsProduct_nonneg left i k)
          _ = (Finset.univ.sum fun k : Fin n => EL i k * BR k j) +
                Finset.univ.sum fun k : Fin n =>
                  exactAbsProduct left i k * ER k j := by
            exact Finset.sum_add_distrib
      change
        |fl_matMul fp n n n Lhat Rhat i j - matMul n L R i j| <=
          gamma fp n * matMul n BL BR i j +
            matMul n EL BR i j + matMul n (exactAbsProduct left) ER i j
      calc
        |fl_matMul fp n n n Lhat Rhat i j - matMul n L R i j|
            = |(fl_matMul fp n n n Lhat Rhat i j - matMul n Lhat Rhat i j) +
                (matMul n Lhat Rhat i j - matMul n L R i j)| := by
              congr 1
              ring
        _ <= |fl_matMul fp n n n Lhat Rhat i j - matMul n Lhat Rhat i j| +
              |matMul n Lhat Rhat i j - matMul n L R i j| := abs_add_le _ _
        _ <= gamma fp n * matMul n BL BR i j +
              (matMul n EL BR i j + matMul n (exactAbsProduct left) ER i j) :=
          add_le_add hlocal hproductPropagation
        _ = gamma fp n * matMul n BL BR i j +
              matMul n EL BR i j + matMul n (exactAbsProduct left) ER i j := by
          ring

/-- `MatProdError` adapter for the arbitrary-tree theorem.  The scalar slot is
`1`; all gamma factors and parenthesization-dependent coefficients are retained
inside the exact recursive `errorEnvelope`. -/
theorem roundedEval_MatProdError {n : Nat} (fp : FPModel)
    (hn : gammaValid fp n) (tree : Ch14ProductTree n) :
    MatProdError n (roundedEval fp tree) (exactEval tree) 1
      (errorEnvelope fp tree) := by
  intro i j
  simpa [productDelta] using productDelta_abs_le_errorEnvelope fp hn tree i j

end Ch14ProductTree

/-!
## Compatible rectangular products

The square tree above is retained for compatibility with the original Chapter
14 development.  The indexed tree below is the source-facing result: its type
forces every adjacent product to have compatible dimensions, while allowing a
different row, contraction, and column dimension at every internal node.
-/

/-- A full binary parenthesization of compatible rectangular matrices.

`Ch14RectProductTree m n` evaluates to an `m`-by-`n` matrix.  In a node, the
hidden index `r` is exactly the local inner dimension charged by that matrix
multiplication. -/
inductive Ch14RectProductTree : Nat -> Nat -> Type where
  | leaf {m n : Nat} (A : Fin m -> Fin n -> Real) : Ch14RectProductTree m n
  | node {m r n : Nat}
      (left : Ch14RectProductTree m r)
      (right : Ch14RectProductTree r n) : Ch14RectProductTree m n

namespace Ch14RectProductTree

/-- Exact evaluation in the selected compatible rectangular
parenthesization. -/
noncomputable def exactEval {m n : Nat} :
    Ch14RectProductTree m n -> Fin m -> Fin n -> Real
  | .leaf A => A
  | .node left right => rectMatMul (exactEval left) (exactEval right)

/-- Concrete floating-point evaluation: every internal node is one
`fl_matMul`, using that node's actual inner dimension. -/
noncomputable def roundedEval (fp : FPModel) {m n : Nat} :
    Ch14RectProductTree m n -> Fin m -> Fin n -> Real
  | .leaf A => A
  | @node _ r _ left right =>
      fl_matMul fp m r n (roundedEval fp left) (roundedEval fp right)

/-- Exact product in the selected tree after replacing every leaf by its
componentwise absolute value. -/
noncomputable def exactAbsProduct {m n : Nat} :
    Ch14RectProductTree m n -> Fin m -> Fin n -> Real
  | .leaf A => absMatrixRect A
  | .node left right =>
      rectMatMul (exactAbsProduct left) (exactAbsProduct right)

/-- The sum of all internal contraction dimensions.  This is Higham's `p`
for the represented binary evaluation order. -/
def operationBudget {m n : Nat} : Ch14RectProductTree m n -> Nat
  | .leaf _ => 0
  | @node _ r _ left right =>
      operationBudget left + operationBudget right + r

/-- Exact evaluation-order coefficient assembled from the local
`gamma_(inner dimension)` factors.

If `cL` and `cR` are the subtree coefficients, then their joint coefficient is
`cLR = cL + cR + cL*cR`; the node combines `cLR` with its local gamma factor in
the same way.  Equivalently,

`1 + cNode = (1 + cL) * (1 + cR) * (1 + gamma_r)`.
-/
noncomputable def orderCoefficient (fp : FPModel) {m n : Nat} :
    Ch14RectProductTree m n -> Real
  | .leaf _ => 0
  | @node _ r _ left right =>
      let cLeft := orderCoefficient fp left
      let cRight := orderCoefficient fp right
      let cBoth := cLeft + cRight + cLeft * cRight
      cBoth + gamma fp r + cBoth * gamma fp r

/-- Higham's rectangular `Delta(A1, ..., Ak)` for this concrete evaluation
tree. -/
noncomputable def productDelta (fp : FPModel) {m n : Nat}
    (tree : Ch14RectProductTree m n) : Fin m -> Fin n -> Real :=
  fun i j => roundedEval fp tree i j - exactEval tree i j

/-- Rectangular analogue of the legacy square `MatProdError` predicate. -/
def RectMatProdError {m n : Nat}
    (computed exact : Fin m -> Fin n -> Real) (coefficient : Real)
    (absProduct : Fin m -> Fin n -> Real) : Prop :=
  forall i j, |computed i j - exact i j| <= coefficient * absProduct i j

@[simp] theorem exactEval_leaf {m n : Nat} (A : Fin m -> Fin n -> Real) :
    exactEval (.leaf A) = A := rfl

@[simp] theorem exactEval_node {m r n : Nat}
    (left : Ch14RectProductTree m r) (right : Ch14RectProductTree r n) :
    exactEval (.node left right) = rectMatMul (exactEval left) (exactEval right) := rfl

@[simp] theorem roundedEval_leaf {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) :
    roundedEval fp (.leaf A) = A := rfl

@[simp] theorem roundedEval_node {m r n : Nat} (fp : FPModel)
    (left : Ch14RectProductTree m r) (right : Ch14RectProductTree r n) :
    roundedEval fp (.node left right) =
      fl_matMul fp m r n (roundedEval fp left) (roundedEval fp right) := rfl

@[simp] theorem exactAbsProduct_leaf {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    exactAbsProduct (.leaf A) = absMatrixRect A := rfl

@[simp] theorem exactAbsProduct_node {m r n : Nat}
    (left : Ch14RectProductTree m r) (right : Ch14RectProductTree r n) :
    exactAbsProduct (.node left right) =
      rectMatMul (exactAbsProduct left) (exactAbsProduct right) := rfl

@[simp] theorem operationBudget_leaf {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    operationBudget (.leaf A) = 0 := rfl

@[simp] theorem operationBudget_node {m r n : Nat}
    (left : Ch14RectProductTree m r) (right : Ch14RectProductTree r n) :
    operationBudget (.node left right) =
      operationBudget left + operationBudget right + r := rfl

@[simp] theorem orderCoefficient_leaf {m n : Nat} (fp : FPModel)
    (A : Fin m -> Fin n -> Real) :
    orderCoefficient fp (.leaf A) = 0 := rfl

/-- Exact rectangular arithmetic is invariant under one generating
reassociation of full binary trees. -/
theorem exactEval_rotate {a b c d : Nat}
    (A : Ch14RectProductTree a b) (B : Ch14RectProductTree b c)
    (C : Ch14RectProductTree c d) :
    exactEval (.node (.node A B) C) = exactEval (.node A (.node B C)) := by
  simpa using rectMatMul_assoc (exactEval A) (exactEval B) (exactEval C)

/-- The absolute exact product has the same generating reassociation law. -/
theorem exactAbsProduct_rotate {a b c d : Nat}
    (A : Ch14RectProductTree a b) (B : Ch14RectProductTree b c)
    (C : Ch14RectProductTree c d) :
    exactAbsProduct (.node (.node A B) C) =
      exactAbsProduct (.node A (.node B C)) := by
  simpa using
    rectMatMul_assoc (exactAbsProduct A) (exactAbsProduct B) (exactAbsProduct C)

/-- Higham's summed inner-dimension budget is invariant under the generating
reassociation of compatible products. -/
theorem operationBudget_rotate {a b c d : Nat}
    (A : Ch14RectProductTree a b) (B : Ch14RectProductTree b c)
    (C : Ch14RectProductTree c d) :
    operationBudget (.node (.node A B) C) =
      operationBudget (.node A (.node B C)) := by
  simp [operationBudget]
  omega

/-- The exact local-gamma coefficient is likewise invariant under the
generating reassociation; its factors are tied to the same inner dimensions. -/
theorem orderCoefficient_rotate {a b c d : Nat} (fp : FPModel)
    (A : Ch14RectProductTree a b) (B : Ch14RectProductTree b c)
    (C : Ch14RectProductTree c d) :
    orderCoefficient fp (.node (.node A B) C) =
      orderCoefficient fp (.node A (.node B C)) := by
  simp only [orderCoefficient]
  ring

/-- The explicit perturbation gives
`fl(A1 ... Ak) = A1 ... Ak + Delta(A1, ..., Ak)`. -/
theorem roundedEval_eq_exactEval_add_productDelta {m n : Nat} (fp : FPModel)
    (tree : Ch14RectProductTree m n) :
    roundedEval fp tree =
      fun i j => exactEval tree i j + productDelta fp tree i j := by
  ext i j
  simp only [productDelta]
  ring

/-- Every internal node obtains its local rectangular certificate directly
from `matMul_error_bound`. -/
theorem roundedEval_node_local_error {m r n : Nat} (fp : FPModel)
    (left : Ch14RectProductTree m r) (right : Ch14RectProductTree r n)
    (hr : gammaValid fp r) :
    forall i j,
      |roundedEval fp (.node left right) i j -
          rectMatMul (roundedEval fp left) (roundedEval fp right) i j| <=
        gamma fp r *
          rectMatMul (absMatrixRect (roundedEval fp left))
            (absMatrixRect (roundedEval fp right)) i j := by
  intro i j
  simpa [roundedEval, rectMatMul, absMatrixRect] using
    matMul_error_bound fp m r n (roundedEval fp left) (roundedEval fp right) hr i j

/-- Products of rectangular absolute-value factors are entrywise
nonnegative. -/
theorem exactAbsProduct_nonneg {m n : Nat}
    (tree : Ch14RectProductTree m n) :
    forall i j, 0 <= exactAbsProduct tree i j := by
  induction tree with
  | leaf A =>
      intro i j
      exact abs_nonneg (A i j)
  | node left right ihLeft ihRight =>
      intro i j
      simp only [exactAbsProduct_node, rectMatMul]
      exact Finset.sum_nonneg fun k _ => mul_nonneg (ihLeft i k) (ihRight k j)

/-- The absolute exact rectangular evaluation is bounded by the compatible
product of the absolute source factors. -/
theorem abs_exactEval_le_exactAbsProduct {m n : Nat}
    (tree : Ch14RectProductTree m n) :
    forall i j, |exactEval tree i j| <= exactAbsProduct tree i j := by
  induction tree with
  | leaf A =>
      intro i j
      rfl
  | node left right ihLeft ihRight =>
      intro i j
      simp only [exactEval_node, exactAbsProduct_node, rectMatMul]
      calc
        |Finset.univ.sum fun k => exactEval left i k * exactEval right k j|
            <= Finset.univ.sum fun k =>
              |exactEval left i k * exactEval right k j| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = Finset.univ.sum fun k =>
              |exactEval left i k| * |exactEval right k j| := by
          apply Finset.sum_congr rfl
          intro k _
          exact abs_mul _ _
        _ <= Finset.univ.sum fun k =>
              exactAbsProduct left i k * exactAbsProduct right k j := by
          apply Finset.sum_le_sum
          intro k _
          calc
            |exactEval left i k| * |exactEval right k j|
                <= exactAbsProduct left i k * |exactEval right k j| :=
              mul_le_mul_of_nonneg_right (ihLeft i k) (abs_nonneg _)
            _ <= exactAbsProduct left i k * exactAbsProduct right k j :=
              mul_le_mul_of_nonneg_left (ihRight k j)
                (exactAbsProduct_nonneg left i k)

/-- Product form of the exact evaluation-order coefficient. -/
theorem orderCoefficient_node_product_form {m r n : Nat} (fp : FPModel)
    (left : Ch14RectProductTree m r) (right : Ch14RectProductTree r n) :
    1 + orderCoefficient fp (.node left right) =
      (1 + orderCoefficient fp left) * (1 + orderCoefficient fp right) *
        (1 + gamma fp r) := by
  simp only [orderCoefficient]
  ring

/-- The order-specific coefficient is nonnegative whenever its complete
operation budget is valid. -/
theorem orderCoefficient_nonneg {m n : Nat} (fp : FPModel)
    (tree : Ch14RectProductTree m n)
    (hvalid : gammaValid fp (operationBudget tree)) :
    0 <= orderCoefficient fp tree := by
  revert hvalid
  induction tree with
  | leaf A =>
      intro _
      simp
  | @node m r n left right ihLeft ihRight =>
      intro hvalid
      have hLeftValid : gammaValid fp (operationBudget left) :=
        gammaValid_mono fp (by simp [operationBudget]; omega) hvalid
      have hRightValid : gammaValid fp (operationBudget right) :=
        gammaValid_mono fp (by simp [operationBudget]; omega) hvalid
      have hLocalValid : gammaValid fp r :=
        gammaValid_mono fp (by simp [operationBudget]) hvalid
      have hcLeft := ihLeft hLeftValid
      have hcRight := ihRight hRightValid
      have hgamma := gamma_nonneg fp hLocalValid
      simp only [orderCoefficient]
      positivity

/-- The exact evaluation-order coefficient is bounded by one accumulated
`gamma_p`, where `p` is the sum of all local inner dimensions. -/
theorem orderCoefficient_le_gamma_operationBudget {m n : Nat} (fp : FPModel)
    (tree : Ch14RectProductTree m n)
    (hvalid : gammaValid fp (operationBudget tree)) :
    orderCoefficient fp tree <= gamma fp (operationBudget tree) := by
  revert hvalid
  induction tree with
  | leaf A =>
      intro _
      simp [gamma]
  | @node m r n left right ihLeft ihRight =>
      intro hvalid
      let pLeft := operationBudget left
      let pRight := operationBudget right
      let cLeft := orderCoefficient fp left
      let cRight := orderCoefficient fp right
      let cBoth := cLeft + cRight + cLeft * cRight
      have hLeftValid : gammaValid fp pLeft :=
        gammaValid_mono fp (by simp [pLeft, operationBudget]; omega) hvalid
      have hRightValid : gammaValid fp pRight :=
        gammaValid_mono fp (by simp [pRight, operationBudget]; omega) hvalid
      have hBothValid : gammaValid fp (pLeft + pRight) :=
        gammaValid_mono fp (by simp [pLeft, pRight, operationBudget]) hvalid
      have hLocalValid : gammaValid fp r :=
        gammaValid_mono fp (by simp [operationBudget]) hvalid
      have hcLeft : cLeft <= gamma fp pLeft := by
        simpa [cLeft, pLeft] using ihLeft hLeftValid
      have hcRight : cRight <= gamma fp pRight := by
        simpa [cRight, pRight] using ihRight hRightValid
      have hcLeftNonneg : 0 <= cLeft := by
        simpa [cLeft] using orderCoefficient_nonneg fp left hLeftValid
      have hcRightNonneg : 0 <= cRight := by
        simpa [cRight] using orderCoefficient_nonneg fp right hRightValid
      have hgammaLeft : 0 <= gamma fp pLeft := gamma_nonneg fp hLeftValid
      have hmul : cLeft * cRight <= gamma fp pLeft * gamma fp pRight :=
        mul_le_mul hcLeft hcRight hcRightNonneg hgammaLeft
      have hcBothToParts :
          cBoth <= gamma fp pLeft + gamma fp pRight +
            gamma fp pLeft * gamma fp pRight := by
        dsimp [cBoth]
        linarith
      have hcBoth : cBoth <= gamma fp (pLeft + pRight) :=
        hcBothToParts.trans (gamma_sum_le fp pLeft pRight hBothValid)
      have hmulLocal :
          cBoth * gamma fp r <= gamma fp (pLeft + pRight) * gamma fp r :=
        mul_le_mul_of_nonneg_right hcBoth (gamma_nonneg fp hLocalValid)
      have hcombined :
          cBoth + gamma fp r + cBoth * gamma fp r <=
            gamma fp (pLeft + pRight) + gamma fp r +
              gamma fp (pLeft + pRight) * gamma fp r := by
        linarith
      have hbudgetGamma :=
        gamma_sum_le fp (pLeft + pRight) r (by
          simpa [pLeft, pRight, operationBudget] using hvalid)
      change cBoth + gamma fp r + cBoth * gamma fp r <=
        gamma fp (operationBudget left + operationBudget right + r)
      exact hcombined.trans (by simpa [pLeft, pRight] using hbudgetGamma)

/-- One rectangular rounded product composes two source-shaped subtree error
certificates.  This is the algebraic induction step used below; its conclusion
is derived from `matMul_error_bound`, not assumed. -/
theorem fl_rectMatMul_error_compose {m r n : Nat} (fp : FPModel)
    (Lhat L Labs : Fin m -> Fin r -> Real)
    (Rhat R Rabs : Fin r -> Fin n -> Real)
    (cLeft cRight : Real)
    (hr : gammaValid fp r)
    (hcLeft : 0 <= cLeft)
    (hLabs : forall i k, 0 <= Labs i k)
    (hLexact : forall i k, |L i k| <= Labs i k)
    (hRexact : forall k j, |R k j| <= Rabs k j)
    (hLerror : forall i k, |Lhat i k - L i k| <= cLeft * Labs i k)
    (hRerror : forall k j, |Rhat k j - R k j| <= cRight * Rabs k j) :
    forall i j,
      |fl_matMul fp m r n Lhat Rhat i j - rectMatMul L R i j| <=
        ((cLeft + cRight + cLeft * cRight) + gamma fp r +
            (cLeft + cRight + cLeft * cRight) * gamma fp r) *
          rectMatMul Labs Rabs i j := by
  intro i j
  have hgamma : 0 <= gamma fp r := gamma_nonneg fp hr
  have hOneLeft : 0 <= 1 + cLeft := by linarith
  have hLhat : forall a k,
      |Lhat a k| <= (1 + cLeft) * Labs a k := by
    intro a k
    calc
      |Lhat a k| = |L a k + (Lhat a k - L a k)| := by
        congr 1
        ring
      _ <= |L a k| + |Lhat a k - L a k| := abs_add_le _ _
      _ <= Labs a k + cLeft * Labs a k :=
        add_le_add (hLexact a k) (hLerror a k)
      _ = (1 + cLeft) * Labs a k := by ring
  have hRhat : forall k b,
      |Rhat k b| <= (1 + cRight) * Rabs k b := by
    intro k b
    calc
      |Rhat k b| = |R k b + (Rhat k b - R k b)| := by
        congr 1
        ring
      _ <= |R k b| + |Rhat k b - R k b| := abs_add_le _ _
      _ <= Rabs k b + cRight * Rabs k b :=
        add_le_add (hRexact k b) (hRerror k b)
      _ = (1 + cRight) * Rabs k b := by ring
  have hlocalMajorant :
      (Finset.univ.sum fun k : Fin r => |Lhat i k| * |Rhat k j|) <=
        (1 + cLeft) * (1 + cRight) * rectMatMul Labs Rabs i j := by
    calc
      (Finset.univ.sum fun k : Fin r => |Lhat i k| * |Rhat k j|)
          <= Finset.univ.sum fun k : Fin r =>
              ((1 + cLeft) * Labs i k) * ((1 + cRight) * Rabs k j) := by
        apply Finset.sum_le_sum
        intro k _
        calc
          |Lhat i k| * |Rhat k j|
              <= ((1 + cLeft) * Labs i k) * |Rhat k j| :=
            mul_le_mul_of_nonneg_right (hLhat i k) (abs_nonneg _)
          _ <= ((1 + cLeft) * Labs i k) * ((1 + cRight) * Rabs k j) :=
            mul_le_mul_of_nonneg_left (hRhat k j)
              (mul_nonneg hOneLeft (hLabs i k))
      _ = (1 + cLeft) * (1 + cRight) * rectMatMul Labs Rabs i j := by
        unfold rectMatMul
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
  have hlocal :
      |fl_matMul fp m r n Lhat Rhat i j - rectMatMul Lhat Rhat i j| <=
        gamma fp r * ((1 + cLeft) * (1 + cRight) *
          rectMatMul Labs Rabs i j) := by
    have hraw := matMul_error_bound fp m r n Lhat Rhat hr i j
    have hraw' :
        |fl_matMul fp m r n Lhat Rhat i j - rectMatMul Lhat Rhat i j| <=
          gamma fp r *
            (Finset.univ.sum fun k : Fin r => |Lhat i k| * |Rhat k j|) := by
      simpa [rectMatMul] using hraw
    exact hraw'.trans (mul_le_mul_of_nonneg_left hlocalMajorant hgamma)
  have hpropagation :
      |rectMatMul Lhat Rhat i j - rectMatMul L R i j| <=
        (cLeft * (1 + cRight) + cRight) * rectMatMul Labs Rabs i j := by
    unfold rectMatMul
    rw [<- Finset.sum_sub_distrib]
    calc
      |Finset.univ.sum fun k : Fin r => Lhat i k * Rhat k j - L i k * R k j|
          <= Finset.univ.sum fun k : Fin r =>
              |Lhat i k * Rhat k j - L i k * R k j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= Finset.univ.sum fun k : Fin r =>
            (cLeft * (1 + cRight) + cRight) * (Labs i k * Rabs k j) := by
        apply Finset.sum_le_sum
        intro k _
        calc
          |Lhat i k * Rhat k j - L i k * R k j|
              = |(Lhat i k - L i k) * Rhat k j +
                  L i k * (Rhat k j - R k j)| := by
                congr 1
                ring
          _ <= |(Lhat i k - L i k) * Rhat k j| +
                |L i k * (Rhat k j - R k j)| := abs_add_le _ _
          _ = |Lhat i k - L i k| * |Rhat k j| +
                |L i k| * |Rhat k j - R k j| := by
                rw [abs_mul, abs_mul]
          _ <= (cLeft * Labs i k) * ((1 + cRight) * Rabs k j) +
                Labs i k * (cRight * Rabs k j) := by
            apply add_le_add
            · calc
                |Lhat i k - L i k| * |Rhat k j|
                    <= (cLeft * Labs i k) * |Rhat k j| :=
                  mul_le_mul_of_nonneg_right (hLerror i k) (abs_nonneg _)
                _ <= (cLeft * Labs i k) * ((1 + cRight) * Rabs k j) :=
                  mul_le_mul_of_nonneg_left (hRhat k j)
                    (mul_nonneg hcLeft (hLabs i k))
            · calc
                |L i k| * |Rhat k j - R k j|
                    <= Labs i k * |Rhat k j - R k j| :=
                  mul_le_mul_of_nonneg_right (hLexact i k) (abs_nonneg _)
                _ <= Labs i k * (cRight * Rabs k j) :=
                  mul_le_mul_of_nonneg_left (hRerror k j) (hLabs i k)
          _ = (cLeft * (1 + cRight) + cRight) *
                (Labs i k * Rabs k j) := by ring
      _ = (cLeft * (1 + cRight) + cRight) *
            Finset.univ.sum fun k : Fin r => Labs i k * Rabs k j := by
        rw [Finset.mul_sum]
  calc
    |fl_matMul fp m r n Lhat Rhat i j - rectMatMul L R i j|
        = |(fl_matMul fp m r n Lhat Rhat i j - rectMatMul Lhat Rhat i j) +
            (rectMatMul Lhat Rhat i j - rectMatMul L R i j)| := by
          congr 1
          ring
    _ <= |fl_matMul fp m r n Lhat Rhat i j - rectMatMul Lhat Rhat i j| +
          |rectMatMul Lhat Rhat i j - rectMatMul L R i j| := abs_add_le _ _
    _ <= gamma fp r * ((1 + cLeft) * (1 + cRight) *
            rectMatMul Labs Rabs i j) +
          (cLeft * (1 + cRight) + cRight) * rectMatMul Labs Rabs i j :=
      add_le_add hlocal hpropagation
    _ = ((cLeft + cRight + cLeft * cRight) + gamma fp r +
          (cLeft + cRight + cLeft * cRight) * gamma fp r) *
            rectMatMul Labs Rabs i j := by ring

/-- Source-facing arbitrary-parenthesization theorem with the exact
evaluation-order coefficient.  Every hypothesis is a validity guard derived
from the one global operation budget; no product-error conclusion is assumed. -/
theorem productDelta_abs_le_orderCoefficient {m n : Nat} (fp : FPModel)
    (tree : Ch14RectProductTree m n)
    (hvalid : gammaValid fp (operationBudget tree)) :
    forall i j,
      |productDelta fp tree i j| <=
        orderCoefficient fp tree * exactAbsProduct tree i j := by
  revert hvalid
  induction tree with
  | leaf A =>
      intro _ i j
      simp [productDelta]
  | @node m r n left right ihLeft ihRight =>
      intro hvalid
      have hLeftValid : gammaValid fp (operationBudget left) :=
        gammaValid_mono fp (by simp [operationBudget]; omega) hvalid
      have hRightValid : gammaValid fp (operationBudget right) :=
        gammaValid_mono fp (by simp [operationBudget]; omega) hvalid
      have hLocalValid : gammaValid fp r :=
        gammaValid_mono fp (by simp [operationBudget]) hvalid
      have hcLeft : 0 <= orderCoefficient fp left :=
        orderCoefficient_nonneg fp left hLeftValid
      have hcompose :=
        fl_rectMatMul_error_compose fp
          (roundedEval fp left) (exactEval left) (exactAbsProduct left)
          (roundedEval fp right) (exactEval right) (exactAbsProduct right)
          (orderCoefficient fp left) (orderCoefficient fp right)
          hLocalValid hcLeft
          (exactAbsProduct_nonneg left)
          (abs_exactEval_le_exactAbsProduct left)
          (abs_exactEval_le_exactAbsProduct right)
          (by
            intro i k
            simpa [productDelta] using ihLeft hLeftValid i k)
          (by
            intro k j
            simpa [productDelta] using ihRight hRightValid k j)
      intro i j
      simpa [productDelta, roundedEval, exactEval, exactAbsProduct,
        orderCoefficient] using hcompose i j

/-- The arbitrary rectangular tree satisfies the transparent rectangular
product-error contract at its exact order-specific coefficient. -/
theorem roundedEval_RectMatProdError_orderCoefficient {m n : Nat}
    (fp : FPModel) (tree : Ch14RectProductTree m n)
    (hvalid : gammaValid fp (operationBudget tree)) :
    RectMatProdError (roundedEval fp tree) (exactEval tree)
      (orderCoefficient fp tree) (exactAbsProduct tree) := by
  intro i j
  simpa [productDelta] using productDelta_abs_le_orderCoefficient fp tree hvalid i j

/-- Higham's `p`-budget form:

`|Delta(A1, ..., Ak)| <= gamma_p |A1| ... |Ak|`,

where `p` is the sum of the inner dimensions at the internal nodes of the
chosen binary evaluation tree. -/
theorem productDelta_abs_le_gamma_operationBudget {m n : Nat} (fp : FPModel)
    (tree : Ch14RectProductTree m n)
    (hvalid : gammaValid fp (operationBudget tree)) :
    forall i j,
      |productDelta fp tree i j| <=
        gamma fp (operationBudget tree) * exactAbsProduct tree i j := by
  intro i j
  calc
    |productDelta fp tree i j|
        <= orderCoefficient fp tree * exactAbsProduct tree i j :=
      productDelta_abs_le_orderCoefficient fp tree hvalid i j
    _ <= gamma fp (operationBudget tree) * exactAbsProduct tree i j :=
      mul_le_mul_of_nonneg_right
        (orderCoefficient_le_gamma_operationBudget fp tree hvalid)
        (exactAbsProduct_nonneg tree i j)

/-- Rectangular contract at the collapsed `gamma_p` coefficient. -/
theorem roundedEval_RectMatProdError_gamma_operationBudget {m n : Nat}
    (fp : FPModel) (tree : Ch14RectProductTree m n)
    (hvalid : gammaValid fp (operationBudget tree)) :
    RectMatProdError (roundedEval fp tree) (exactEval tree)
      (gamma fp (operationBudget tree)) (exactAbsProduct tree) := by
  intro i j
  simpa [productDelta] using
    productDelta_abs_le_gamma_operationBudget fp tree hvalid i j

/-- Literal `c_p u` form with the explicit choice `c_p = 2p`.  The displayed
smallness guard is the standard condition under which `gamma_p <= 2p*u`.
It also discharges `gammaValid fp p`. -/
theorem productDelta_abs_le_two_mul_operationBudget_mul_u {m n : Nat}
    (fp : FPModel) (tree : Ch14RectProductTree m n)
    (hhalf : (operationBudget tree : Real) * fp.u <= 1 / 2) :
    forall i j,
      |productDelta fp tree i j| <=
        (2 * (operationBudget tree : Real)) * fp.u *
          exactAbsProduct tree i j := by
  have hvalid : gammaValid fp (operationBudget tree) := by
    unfold gammaValid
    linarith
  have hgamma :
      gamma fp (operationBudget tree) <=
        2 * ((operationBudget tree : Real) * fp.u) :=
    gamma_le_two_mul_n_u_of_nu_le_half fp (operationBudget tree) hhalf
  intro i j
  calc
    |productDelta fp tree i j|
        <= gamma fp (operationBudget tree) * exactAbsProduct tree i j :=
      productDelta_abs_le_gamma_operationBudget fp tree hvalid i j
    _ <= (2 * ((operationBudget tree : Real) * fp.u)) *
          exactAbsProduct tree i j :=
      mul_le_mul_of_nonneg_right hgamma (exactAbsProduct_nonneg tree i j)
    _ = (2 * (operationBudget tree : Real)) * fp.u *
          exactAbsProduct tree i j := by ring

/-- Rectangular contract in the literal source shape `c_p*u`, with
`c_p = 2p`. -/
theorem roundedEval_RectMatProdError_two_mul_operationBudget_mul_u
    {m n : Nat} (fp : FPModel) (tree : Ch14RectProductTree m n)
    (hhalf : (operationBudget tree : Real) * fp.u <= 1 / 2) :
    RectMatProdError (roundedEval fp tree) (exactEval tree)
      ((2 * (operationBudget tree : Real)) * fp.u) (exactAbsProduct tree) := by
  intro i j
  simpa [productDelta] using
    productDelta_abs_le_two_mul_operationBudget_mul_u fp tree hhalf i j

/-- Adapter back to the chapter's legacy square `MatProdError` interface for
square endpoints of the heterogeneous tree. -/
theorem roundedEval_MatProdError_gamma_operationBudget {n : Nat}
    (fp : FPModel) (tree : Ch14RectProductTree n n)
    (hvalid : gammaValid fp (operationBudget tree)) :
    MatProdError n (roundedEval fp tree) (exactEval tree)
      (gamma fp (operationBudget tree)) (exactAbsProduct tree) := by
  intro i j
  simpa [productDelta] using
    productDelta_abs_le_gamma_operationBudget fp tree hvalid i j

/-- Literal Chapter 14 package at the exact `gamma_p` budget: the concrete
computed product equals the exact compatible product plus a perturbation that
obeys the printed componentwise absolute-product shape. -/
theorem exists_productDelta_gamma_operationBudget {m n : Nat} (fp : FPModel)
    (tree : Ch14RectProductTree m n)
    (hvalid : gammaValid fp (operationBudget tree)) :
    exists Delta : Fin m -> Fin n -> Real,
      roundedEval fp tree = (fun i j => exactEval tree i j + Delta i j) /\
      forall i j,
        |Delta i j| <=
          gamma fp (operationBudget tree) * exactAbsProduct tree i j := by
  refine ⟨productDelta fp tree,
    roundedEval_eq_exactEval_add_productDelta fp tree, ?_⟩
  exact productDelta_abs_le_gamma_operationBudget fp tree hvalid

/-- Literal Chapter 14 `c_p*u` package with the explicit model-derived choice
`c_p = 2p` under `p*u <= 1/2`. -/
theorem exists_productDelta_two_mul_operationBudget_mul_u {m n : Nat}
    (fp : FPModel) (tree : Ch14RectProductTree m n)
    (hhalf : (operationBudget tree : Real) * fp.u <= 1 / 2) :
    exists Delta : Fin m -> Fin n -> Real,
      roundedEval fp tree = (fun i j => exactEval tree i j + Delta i j) /\
      forall i j,
        |Delta i j| <=
          (2 * (operationBudget tree : Real)) * fp.u *
            exactAbsProduct tree i j := by
  refine ⟨productDelta fp tree,
    roundedEval_eq_exactEval_add_productDelta fp tree, ?_⟩
  exact productDelta_abs_le_two_mul_operationBudget_mul_u fp tree hhalf

end Ch14RectProductTree

end NumStability
