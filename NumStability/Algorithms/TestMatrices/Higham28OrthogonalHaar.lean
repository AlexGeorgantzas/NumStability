/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28OrthogonalSphere
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Bases
import Mathlib.Topology.Instances.Matrix

namespace NumStability

open MeasureTheory MeasureTheory.Measure Set

/-! # Normalized Haar probability on the finite real orthogonal group -/

/-- A short name for the real orthogonal group in dimension `n`. -/
abbrev RealOrthogonalGroup (n : ℕ) :=
  Matrix.orthogonalGroup (Fin n) ℝ

noncomputable instance realSquareMatrixSecondCountableTopology (n : ℕ) :
    SecondCountableTopology (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℝ))

noncomputable instance realOrthogonalGroupSecondCountableTopology (n : ℕ) :
    SecondCountableTopology (RealOrthogonalGroup n) :=
  Topology.IsInducing.subtypeVal.secondCountableTopology

noncomputable instance realSquareMatrixMeasurableSpace (n : ℕ) :
    MeasurableSpace (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin n → Fin n → ℝ))

noncomputable instance realSquareMatrixBorelSpace (n : ℕ) :
    BorelSpace (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs (BorelSpace (Fin n → Fin n → ℝ))

/-- We use the Borel measurable structure associated with the inherited
finite-matrix topology. -/
noncomputable instance realOrthogonalGroupMeasurableSpace (n : ℕ) :
    MeasurableSpace (RealOrthogonalGroup n) :=
  inferInstance

noncomputable instance realOrthogonalGroupBorelSpace (n : ℕ) :
    BorelSpace (RealOrthogonalGroup n) := inferInstance

/-- Matrix multiplication and transpose inversion are continuous on the
orthogonal subgroup. -/
noncomputable instance realOrthogonalGroupIsTopologicalGroup (n : ℕ) :
    IsTopologicalGroup (RealOrthogonalGroup n) where
  continuous_mul := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_fst).matrix_mul
      (continuous_subtype_val.comp continuous_snd)
  continuous_inv := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.matrix_transpose

noncomputable instance realOrthogonalGroupMeasurableMul₂ (n : ℕ) :
    MeasurableMul₂ (RealOrthogonalGroup n) where
  measurable_mul := continuous_mul.measurable

/-- The finite real orthogonal group is compact.  The proof is elementary:
the defining equations are closed, while every entry lies in `[-1,1]`. -/
theorem realOrthogonalGroup_isCompact (n : ℕ) :
    IsCompact (Matrix.orthogonalGroup (Fin n) ℝ :
      Set (Matrix (Fin n) (Fin n) ℝ)) := by
  have hclosed : IsClosed (Matrix.orthogonalGroup (Fin n) ℝ :
      Set (Matrix (Fin n) (Fin n) ℝ)) := by
    have heq : (Matrix.orthogonalGroup (Fin n) ℝ :
          Set (Matrix (Fin n) (Fin n) ℝ)) =
          {A | A * A.transpose = 1} := by
      ext A
      exact Matrix.mem_orthogonalGroup_iff (Fin n) ℝ
    rw [heq]
    exact isClosed_eq
      (continuous_id.matrix_mul continuous_id.matrix_transpose)
      continuous_const
  apply (isCompact_Icc.matrix).of_isClosed_subset hclosed
  intro A hA
  rw [Set.mem_matrix]
  intro i j
  have horth : A * A.transpose = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).mp hA
  have hrow : (∑ k : Fin n, A i k * A i k) = 1 := by
    have hij := congrFun (congrFun horth i) i
    simpa [Matrix.mul_apply, Matrix.transpose_apply] using hij
  have hsquare : A i j ^ 2 ≤ 1 := by
    calc
      A i j ^ 2 ≤ ∑ k : Fin n, A i k * A i k := by
        rw [pow_two]
        exact Finset.single_le_sum
          (fun k _ => mul_self_nonneg (A i k)) (Finset.mem_univ j)
      _ = 1 := hrow
  have habs : |A i j| ≤ 1 :=
    (sq_le_one_iff_abs_le_one (A i j)).mp hsquare
  exact ⟨(abs_le.mp habs).1, (abs_le.mp habs).2⟩

noncomputable instance realOrthogonalGroupCompactSpace (n : ℕ) :
    CompactSpace (RealOrthogonalGroup n) :=
  isCompact_iff_compactSpace.mp (realOrthogonalGroup_isCompact n)

/-- Haar measure normalized by the whole compact orthogonal group. -/
noncomputable def normalizedOrthogonalHaar (n : ℕ) :
    Measure (RealOrthogonalGroup n) :=
  haarMeasure
    (⟨⟨Set.univ, isCompact_univ⟩, by simp⟩ :
      TopologicalSpace.PositiveCompacts (RealOrthogonalGroup n))

theorem normalizedOrthogonalHaar_univ (n : ℕ) :
    normalizedOrthogonalHaar n Set.univ = 1 := by
  exact haarMeasure_self

instance normalizedOrthogonalHaar_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (normalizedOrthogonalHaar n) :=
  ⟨normalizedOrthogonalHaar_univ n⟩

instance normalizedOrthogonalHaar_isHaarMeasure (n : ℕ) :
    (normalizedOrthogonalHaar n).IsHaarMeasure := by
  unfold normalizedOrthogonalHaar
  infer_instance

/-- On a compact group the normalized left Haar probability is also right
invariant.  A right translate is another Haar probability, hence agrees by
Haar uniqueness. -/
instance normalizedOrthogonalHaar_isMulRightInvariant (n : ℕ) :
    (normalizedOrthogonalHaar n).IsMulRightInvariant where
  map_mul_right_eq_self g := by
    let μg := Measure.map (fun x : RealOrthogonalGroup n => x * g)
      (normalizedOrthogonalHaar n)
    letI : IsProbabilityMeasure μg :=
      Measure.isProbabilityMeasure_map
        (continuous_id.mul continuous_const).measurable.aemeasurable
    letI : μg.IsHaarMeasure :=
      Measure.isHaarMeasure_map_mul_right (normalizedOrthogonalHaar n) g
    exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure μg
      (normalizedOrthogonalHaar n)

/-- Normalized orthogonal Haar probability is invariant under inversion. -/
theorem normalizedOrthogonalHaar_map_inv (n : ℕ) :
    Measure.map Inv.inv (normalizedOrthogonalHaar n) =
      normalizedOrthogonalHaar n := by
  let μinv := Measure.map Inv.inv (normalizedOrthogonalHaar n)
  letI : IsProbabilityMeasure μinv :=
    Measure.isProbabilityMeasure_map continuous_inv.measurable.aemeasurable
  haveI : μinv.IsMulLeftInvariant := by
    change (normalizedOrthogonalHaar n).inv.IsMulLeftInvariant
    infer_instance
  letI : μinv.IsHaarMeasure := by
    exact Measure.isHaarMeasure_of_isCompact_nonempty_interior μinv
      Set.univ isCompact_univ (by simp) (by simp) (by simp)
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure μinv
    (normalizedOrthogonalHaar n)

end NumStability
