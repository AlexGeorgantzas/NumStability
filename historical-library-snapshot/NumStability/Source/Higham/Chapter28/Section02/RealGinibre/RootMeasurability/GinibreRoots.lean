import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Sym.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Topology.Instances.Matrix
import NumStability.Algorithms.LinearSystems.QR.HouseholderReflector
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Analysis.Conditioning.LinearSystems.PerronFrobenius
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.TestMatrices.RealGinibre.GinibreRoots
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.ProbabilityLaw.Probability

/-!
# Chapter28 Section02 RealGinibre RootMeasurability GinibreRoots

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28GinibreRoots` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

noncomputable section

namespace NumStability

open MeasureTheory Polynomial

def complexCharpolyAt {n : ℕ} (A : GinibreRawMatrix n) (t : ℂ) : ℂ :=
  (Matrix.scalar (Fin n) t - (Matrix.of A).map Complex.ofReal).det

def complexRootProductAt {n : ℕ} (z : Fin n → ℂ) (t : ℂ) : ℂ :=
  ∏ i : Fin n, (t - z i)

def complexMatrixCharpoly {n : ℕ} (A : GinibreRawMatrix n) : ℂ[X] :=
  (Matrix.charpoly (Matrix.of A)).map Complex.ofRealHom

def complexTuplePolynomial {n : ℕ} (z : Fin n → ℂ) : ℂ[X] :=
  (((Finset.univ : Finset (Fin n)).val.map z).map fun a => X - C a).prod

theorem eval_complexMatrixCharpoly {n : ℕ} (A : GinibreRawMatrix n) (t : ℂ) :
    (complexMatrixCharpoly A).eval t = complexCharpolyAt A t := by
  rw [complexMatrixCharpoly, ← Matrix.charpoly_map, Matrix.eval_charpoly]
  rfl

theorem eval_complexTuplePolynomial {n : ℕ} (z : Fin n → ℂ) (t : ℂ) :
    (complexTuplePolynomial z).eval t = complexRootProductAt z t := by
  rw [complexTuplePolynomial, Polynomial.eval_multiset_prod]
  simp only [Multiset.map_map]
  change (∏ i : Fin n, eval t (X - C (z i))) = _
  simp [complexRootProductAt]

theorem natDegree_complexMatrixCharpoly {n : ℕ} (A : GinibreRawMatrix n) :
    (complexMatrixCharpoly A).natDegree = n := by
  rw [complexMatrixCharpoly, ← Matrix.charpoly_map,
    Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

theorem natDegree_complexTuplePolynomial {n : ℕ} (z : Fin n → ℂ) :
    (complexTuplePolynomial z).natDegree = n := by
  rw [complexTuplePolynomial, natDegree_multiset_prod_X_sub_C_eq_card,
    Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin]

def complexRootTupleRelation {n : ℕ} (A : GinibreRawMatrix n) (z : Fin n → ℂ) : Prop :=
  ∀ k : Fin (n + 1), complexCharpolyAt A (k : ℂ) = complexRootProductAt z (k : ℂ)

theorem complexRootTupleRelation_iff {n : ℕ}
    (A : GinibreRawMatrix n) (z : Fin n → ℂ) :
    complexRootTupleRelation A z ↔
      complexMatrixCharpoly A = complexTuplePolynomial z := by
  constructor
  · intro h
    apply eq_of_natDegree_lt_card_of_eval_eq
        (f := fun k : Fin (n + 1) => (k : ℂ))
    · intro i j hij
      apply Fin.ext
      have hr : (i.val : ℝ) = j.val := by
        simpa using congrArg Complex.re hij
      exact_mod_cast hr
    · intro k
      rw [eval_complexMatrixCharpoly, eval_complexTuplePolynomial]
      exact h k
    · rw [natDegree_complexMatrixCharpoly, natDegree_complexTuplePolynomial,
        max_self, Fintype.card_fin]
      omega
  · intro h k
    rw [← eval_complexMatrixCharpoly, ← eval_complexTuplePolynomial, h]

def complexRootTupleSet (n : ℕ) : Set (GinibreRawMatrix n × (Fin n → ℂ)) :=
  {p | complexRootTupleRelation p.1 p.2}

theorem continuous_complexCharpolyAt {n : ℕ} :
    Continuous (fun p : GinibreRawMatrix n × ℂ => complexCharpolyAt p.1 p.2) := by
  unfold complexCharpolyAt
  apply Continuous.matrix_det
  apply continuous_matrix
  intro i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.scalar_apply]
    fun_prop
  · simp [Matrix.scalar_apply, hij]
    fun_prop

theorem continuous_complexRootProductAt {n : ℕ} :
    Continuous (fun p : (Fin n → ℂ) × ℂ => complexRootProductAt p.1 p.2) := by
  unfold complexRootProductAt
  fun_prop

theorem isClosed_complexRootTupleSet (n : ℕ) :
    IsClosed (complexRootTupleSet n) := by
  simp only [complexRootTupleSet, complexRootTupleRelation, Set.setOf_forall]
  apply isClosed_iInter
  intro k
  apply isClosed_eq
  · exact continuous_complexCharpolyAt.comp
      (continuous_fst.prodMk continuous_const)
  · exact continuous_complexRootProductAt.comp
      (continuous_snd.prodMk continuous_const)

def complexTupleRealCount {n : ℕ} (z : Fin n → ℂ) : ℕ :=
  (Finset.univ.filter fun i => (z i).im = 0).card

def complexRootTupleCountSet (n k : ℕ) : Set (GinibreRawMatrix n × (Fin n → ℂ)) :=
  complexRootTupleSet n ∩ {p | complexTupleRealCount p.2 = k}

def complexRootTupleCountProjection (n k : ℕ) : Set (GinibreRawMatrix n) :=
  Prod.fst '' complexRootTupleCountSet n k

theorem exists_fin_univ_map_eq_of_card {α : Type*} (n : ℕ)
    (s : Multiset α) (hs : s.card = n) :
    ∃ z : Fin n → α, (Finset.univ : Finset (Fin n)).val.map z = s := by
  induction n generalizing s with
  | zero =>
      have hs0 : s = 0 := Multiset.card_eq_zero.mp hs
      subst s
      exact ⟨Fin.elim0, by simp⟩
  | succ n ih =>
      have hspos : 0 < s.card := by omega
      obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp hspos
      obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem ha
      subst s
      have htcard : t.card = n := by simpa using hs
      obtain ⟨z, hz⟩ := ih t htcard
      refine ⟨Fin.cons a z, ?_⟩
      simpa [Fin.univ_val_map, List.ofFn_succ] using congrArg (fun u => a ::ₘ u) hz

theorem exists_complexRootTupleRelation (n : ℕ) (A : GinibreRawMatrix n) :
    ∃ z : Fin n → ℂ, complexRootTupleRelation A z := by
  have hcard : (complexMatrixCharpoly A).roots.card = n := by
    rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_complexMatrixCharpoly]
  obtain ⟨z, hz⟩ := exists_fin_univ_map_eq_of_card n
    (complexMatrixCharpoly A).roots hcard
  refine ⟨z, (complexRootTupleRelation_iff A z).2 ?_⟩
  have hmonic : (complexMatrixCharpoly A).Monic := by
    rw [complexMatrixCharpoly, ← Matrix.charpoly_map]
    exact Matrix.charpoly_monic _
  have hsplit : (complexMatrixCharpoly A).Splits := IsAlgClosed.splits _
  calc
    complexMatrixCharpoly A =
        ((complexMatrixCharpoly A).roots.map fun a => X - C a).prod :=
      hsplit.eq_prod_roots_of_monic hmonic
    _ = complexTuplePolynomial z := by
      simp only [complexTuplePolynomial]
      rw [hz]

theorem mem_range_complexOfReal_iff (z : ℂ) :
    z ∈ Complex.ofRealHom.range ↔ z.im = 0 := by
  constructor
  · rintro ⟨r, rfl⟩
    simp
  · intro hz
    refine ⟨z.re, ?_⟩
    apply Complex.ext
    · simp
    · simpa using hz.symm

theorem roots_complexTuplePolynomial {n : ℕ} (z : Fin n → ℂ) :
    (complexTuplePolynomial z).roots =
      (Finset.univ : Finset (Fin n)).val.map z := by
  unfold complexTuplePolynomial
  exact roots_multiset_prod_X_sub_C _

theorem realEigenvalueCount_eq_complexTupleRealCount_of_relation
    {n : ℕ} (A : GinibreRawMatrix n) (z : Fin n → ℂ)
    (h : complexRootTupleRelation A z) :
    realEigenvalueCount n A = complexTupleRealCount z := by
  classical
  change (Matrix.charpoly (Matrix.of A)).roots.card =
    (Finset.univ.filter fun i => (z i).im = 0).card
  have hroots : (complexMatrixCharpoly A).roots =
      (Finset.univ : Finset (Fin n)).val.map z := by
    rw [(complexRootTupleRelation_iff A z).1 h,
      roots_complexTuplePolynomial]
  have hf := Polynomial.filter_roots_map_range_eq_map_roots
    Complex.ofRealHom.injective (Matrix.charpoly (Matrix.of A))
  have hc := congrArg Multiset.card hf
  rw [show (Matrix.charpoly (Matrix.of A)).map Complex.ofRealHom =
      complexMatrixCharpoly A by rfl, hroots, Multiset.filter_map,
      Multiset.card_map, Multiset.card_map] at hc
  simp only [Function.comp_apply] at hc
  simpa only [mem_range_complexOfReal_iff] using hc.symm

theorem mem_complexRootTupleCountProjection_iff
    (n k : ℕ) (A : GinibreRawMatrix n) :
    A ∈ complexRootTupleCountProjection n k ↔ realEigenvalueCount n A = k := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (realEigenvalueCount_eq_complexTupleRealCount_of_relation
      p.1 p.2 hp.1).trans hp.2
  · intro hcount
    obtain ⟨z, hz⟩ := exists_complexRootTupleRelation n A
    refine ⟨(A, z), ⟨hz, ?_⟩, rfl⟩
    change complexTupleRealCount z = k
    rw [← realEigenvalueCount_eq_complexTupleRealCount_of_relation A z hz]
    exact hcount

theorem compl_complexRootTupleCountProjection (n k : ℕ) :
    (complexRootTupleCountProjection n k)ᶜ =
      ⋃ j : ℕ, if j = k then ∅ else complexRootTupleCountProjection n j := by
  ext A
  constructor
  · intro hA
    have hj : realEigenvalueCount n A ≠ k := by
      intro hj
      exact hA ((mem_complexRootTupleCountProjection_iff n k A).2 hj)
    rw [Set.mem_iUnion]
    refine ⟨realEigenvalueCount n A, ?_⟩
    simp [hj, mem_complexRootTupleCountProjection_iff]
  · rw [Set.mem_iUnion]
    rintro ⟨j, hj⟩ hA
    by_cases heq : j = k
    · simpa [heq] using hj
    · have hjcount : realEigenvalueCount n A = j :=
        (mem_complexRootTupleCountProjection_iff n j A).1 (by simpa [heq] using hj)
      have hkcount : realEigenvalueCount n A = k :=
        (mem_complexRootTupleCountProjection_iff n k A).1 hA
      exact heq (hjcount.symm.trans hkcount)

/-- Number of real characteristic roots strictly below a moving threshold,
counted with algebraic multiplicity.  This is the rank used to split the
regular incidence chart into injective pieces. -/
def realEigenvalueBelowCount {n : ℕ} (p : GinibreRawMatrix n × ℝ) : ℕ :=
  ((Matrix.charpoly (Matrix.of p.1)).roots.filter fun x => x < p.2).card

theorem realEigenvalueBelowCount_le {n : ℕ} (p : GinibreRawMatrix n × ℝ) :
    realEigenvalueBelowCount p ≤ n := by
  unfold realEigenvalueBelowCount
  calc
    ((Matrix.charpoly (Matrix.of p.1)).roots.filter fun x => x < p.2).card ≤
        (Matrix.charpoly (Matrix.of p.1)).roots.card :=
      Multiset.card_le_card (Multiset.filter_le _ _)
    _ ≤ (Matrix.charpoly (Matrix.of p.1)).natDegree :=
      Polynomial.card_roots' _
    _ = n := by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

def complexTupleRealBelowCount {n : ℕ} (p : (Fin n → ℂ) × ℝ) : ℕ :=
  (Finset.univ.filter fun i => (p.1 i).im = 0 ∧ (p.1 i).re < p.2).card

def complexRootTupleBelowCountSet (n k : ℕ) :
    Set ((GinibreRawMatrix n × ℝ) × (Fin n → ℂ)) :=
  {p | complexRootTupleRelation p.1.1 p.2} ∩
    {p | complexTupleRealBelowCount (p.2, p.1.2) = k}

def complexRootTupleBelowCountProjection (n k : ℕ) :
    Set (GinibreRawMatrix n × ℝ) :=
  Prod.fst '' complexRootTupleBelowCountSet n k

theorem realEigenvalueBelowCount_eq_complexTupleRealBelowCount_of_relation
    {n : ℕ} (A : GinibreRawMatrix n) (t : ℝ) (z : Fin n → ℂ)
    (h : complexRootTupleRelation A z) :
    realEigenvalueBelowCount (A, t) = complexTupleRealBelowCount (z, t) := by
  classical
  change (((Matrix.charpoly (Matrix.of A)).roots.filter fun x => x < t).card) =
    (Finset.univ.filter fun i => (z i).im = 0 ∧ (z i).re < t).card
  have hroots : (complexMatrixCharpoly A).roots =
      (Finset.univ : Finset (Fin n)).val.map z := by
    rw [(complexRootTupleRelation_iff A z).1 h,
      roots_complexTuplePolynomial]
  have hf := Polynomial.filter_roots_map_range_eq_map_roots
    Complex.ofRealHom.injective (Matrix.charpoly (Matrix.of A))
  rw [show (Matrix.charpoly (Matrix.of A)).map Complex.ofRealHom =
      complexMatrixCharpoly A by rfl, hroots] at hf
  have hft := congrArg
    (fun s : Multiset ℂ => (s.filter fun w => w.re < t).card) hf
  simp only [Multiset.filter_filter, Multiset.filter_map,
    Multiset.card_map, Function.comp_apply] at hft
  simpa only [mem_range_complexOfReal_iff, Complex.ofRealHom_eq_coe,
    Complex.ofReal_re, and_comm] using hft.symm

theorem mem_complexRootTupleBelowCountProjection_iff
    (n k : ℕ) (p : GinibreRawMatrix n × ℝ) :
    p ∈ complexRootTupleBelowCountProjection n k ↔
      realEigenvalueBelowCount p = k := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (realEigenvalueBelowCount_eq_complexTupleRealBelowCount_of_relation
      q.1.1 q.1.2 q.2 hq.1).trans hq.2
  · intro hcount
    obtain ⟨z, hz⟩ := exists_complexRootTupleRelation n p.1
    refine ⟨(p, z), ⟨hz, ?_⟩, rfl⟩
    change complexTupleRealBelowCount (z, p.2) = k
    rw [← realEigenvalueBelowCount_eq_complexTupleRealBelowCount_of_relation
      p.1 p.2 z hz]
    exact hcount

theorem compl_complexRootTupleBelowCountProjection (n k : ℕ) :
    (complexRootTupleBelowCountProjection n k)ᶜ =
      ⋃ j : ℕ, if j = k then ∅ else complexRootTupleBelowCountProjection n j := by
  ext p
  constructor
  · intro hp
    have hj : realEigenvalueBelowCount p ≠ k := by
      intro hj
      exact hp ((mem_complexRootTupleBelowCountProjection_iff n k p).2 hj)
    rw [Set.mem_iUnion]
    refine ⟨realEigenvalueBelowCount p, ?_⟩
    simp [hj, mem_complexRootTupleBelowCountProjection_iff]
  · rw [Set.mem_iUnion]
    rintro ⟨j, hj⟩ hp
    by_cases heq : j = k
    · simpa [heq] using hj
    · have hjcount : realEigenvalueBelowCount p = j :=
        (mem_complexRootTupleBelowCountProjection_iff n j p).1 (by simpa [heq] using hj)
      have hkcount : realEigenvalueBelowCount p = k :=
        (mem_complexRootTupleBelowCountProjection_iff n k p).1 hp
      exact heq (hjcount.symm.trans hkcount)

end NumStability

end
