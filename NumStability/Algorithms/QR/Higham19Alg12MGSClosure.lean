import NumStability.Algorithms.QR.Higham19Alg12MGSRepair

/-!
# Literal all-orders closure for Higham Algorithm 19.12

This module packages the end-to-end facts already proved for the literal
floating-point modified Gram--Schmidt loop.  It deliberately does not identify
the explicit local/Gram budgets below with the asymptotic dimension-only
coefficients in Higham's Theorem 19.13.  That final compression is a separate
source-strength obligation.
-/

namespace NumStability

noncomputable section

/-- Honest all-orders output certificate for the literal rounded MGS loop.

The certificate is produced directly from the executor.  In particular, none
of the product residual, orthogonality residual, or repaired factorization is a
premise. -/
structure LiteralMGSAllOrdersCertificate (m n : Nat) (fp : FPModel)
    (A : Fin m -> Fin n -> Real) : Prop where
  /-- The returned right factor is exactly upper trapezoidal. -/
  upper : IsUpperTrapezoidal n n (fl_modifiedGramSchmidtR fp A)
  /-- The product perturbation is the actual computed product residual. -/
  product_identity : forall i j,
    A i j + mgsRoundedProductResidual A
        (fl_modifiedGramSchmidtQ fp A)
        (fl_modifiedGramSchmidtR fp A) i j =
      matMulRect m n n (fl_modifiedGramSchmidtQ fp A)
        (fl_modifiedGramSchmidtR fp A) i j
  /-- Every product-residual column is controlled by the telescoped primitive
  update/projection/division budget of the literal loop. -/
  product_column_bound : forall j,
    columnFrob
        (mgsRoundedProductResidual A
          (fl_modifiedGramSchmidtQ fp A)
          (fl_modifiedGramSchmidtR fp A)) j <=
      vecNorm2
        (mgsRoundedProductEntryBudget fp
          (fl_modifiedGramSchmidtQ fp A) (flMGSVectors fp A) j)
  /-- The computed Gram residual has its canonical, independently checkable
  Frobenius-to-operator bound. -/
  orthogonality_all_orders :
    opNorm2Le
      (gramSchmidtOrthogonalityResidual (fl_modifiedGramSchmidtQ fp A))
      (frobNorm
        (gramSchmidtOrthogonalityResidual (fl_modifiedGramSchmidtQ fp A)))
  /-- A nearby matrix with the same computed `Rhat` and an exactly
  orthonormal left factor is constructed by the right-Gram polar repair.  Its
  coefficient is expanded into primitive local accumulation and Gram-defect
  sensitivity data, rather than assumed from the desired conclusion. -/
  repaired_factorization :
    ModifiedGramSchmidtGlobalRepair m n A
      (fl_modifiedGramSchmidtR fp A)
      (mgsRoundedAccumulatedPolarRelativeBudget fp A
        (fl_modifiedGramSchmidtQ fp A)
        (fl_modifiedGramSchmidtR fp A) (flMGSVectors fp A))

/-- End-to-end producer for the literal rounded Algorithm 19.12 all-orders
certificate.

`hpivot` is the explicit nonbreakdown condition required by the divisions in
the printed algorithm.  For the repository's bare `FPModel`, source rank and
gamma validity alone do not imply this computed condition, so it remains
visible rather than being smuggled into the proof. -/
theorem higham19_13_literal_mgs_all_orders_closed {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (hnm : n <= m)
    (hm : gammaValid fp (2 * (m + 1)))
    (hpivot : forall k : Fin n,
      Ne (fl_modifiedGramSchmidtR fp A k k) 0)
    (hsource : forall j : Fin n, 0 < columnFrob A j) :
    LiteralMGSAllOrdersCertificate m n fp A := by
  let hstate : ModifiedGramSchmidtRoundedState fp A
      (fl_modifiedGramSchmidtQ fp A)
      (fl_modifiedGramSchmidtR fp A) (flMGSVectors fp A) :=
    fl_modifiedGramSchmidt_roundedState fp A hm hpivot
  refine
    { upper := fl_modifiedGramSchmidtR_upperTrapezoidal fp A
      product_identity := ?_
      product_column_bound := ?_
      orthogonality_all_orders := ?_
      repaired_factorization := ?_ }
  · intro i j
    simp [mgsRoundedProductResidual]
  · intro j
    exact hstate.product_residual_column_bound hpivot j
  · exact opNorm2Le_of_frobNorm_self _
  · exact hstate.toGlobalRepairWithAccumulatedPolarBudget
      hpivot hnm hsource

end

end NumStability
