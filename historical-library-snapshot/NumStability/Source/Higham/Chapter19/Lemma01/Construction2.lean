import NumStability.Algorithms.LinearSystems.QR.HouseholderConstruction2

/-!
# Higham Chapter 19, Lemma 19.1, Construction 2

Numbered source-facing export for the alternative-sign Householder construction.
-/

namespace NumStability

/-- **Labeled wrapper — Lemma 19.1, Construction 2**
    (Higham, 2nd ed., §19.3, Lemma 19.1 / eq (19.2) (p. 358)).

    Companion to `H19_Lemma19_1_construction1_backward_error` in
    `Higham19Labels.lean`.  Together the two labeled wrappers now cover BOTH sign
    conventions of the printed Lemma 19.1: Construction 1 (eq (19.1), usual sign)
    and Construction 2 (eq (19.2), alternative sign, this theorem).  The printed
    Lemma 19.1 is thereby fully formalized for both constructions.

    Scope: the constants proved here are the honest Construction-2 indices
    `γ_{3n+4}` (first entry) and `γ_{8n+12}` (β), each an instance of Higham's
    generic `γ̃` class (he does not pin the integer constant `c`).  The β clause
    requires the nonzero-tail nondegeneracy hypothesis (see file header, scope
    note 1); the tail and first-entry clauses hold from `x ≠ 0` alone. -/
theorem H19_Lemma19_1_construction2_backward_error (fp : FPModel) {n : ℕ}
    (hn0 : 0 < n) (x : Fin n → ℝ) (hx : x ≠ 0)
    (htail : householderTailSq hn0 x ≠ 0)
    (hval : gammaValid fp (8 * n + 12)) :
    HouseholderConstruction2Error fp hn0 x
      (fl_householderVectorAlt fp hn0 x)
      (fl_householderBetaAlt fp hn0 x) :=
  fl_householderConstruction2Error fp hn0 x hx htail hval

end NumStability
