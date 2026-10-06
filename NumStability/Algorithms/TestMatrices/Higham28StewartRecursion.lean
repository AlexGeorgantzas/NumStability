/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28StewartHaar

namespace NumStability

open MeasureTheory ProbabilityTheory

theorem split_succ (d : ℕ) (x : Fin (d + 1) → ℝ) (t : StewartGaussianInputs d)
    (j : Fin d) :
    stewartTailCoordinateCastEquiv d j
        ((stewartInputSplitEquiv d).symm (x, t) j.succ) = t j := by
  let z := (stewartInputSplitEquiv d).symm (x, t)
  have h := (stewartInputSplitEquiv d).apply_symm_apply (x, t)
  have hsnd := congrArg Prod.snd h
  have hj := congrFun hsnd j
  change stewartTailCoordinateCastEquiv d j (z j.succ) = t j
  change stewartTailCoordinateCastEquiv d j (z j.succ) = t j at hj
  exact hj

theorem tail_input_apply (d : ℕ) (x : Fin (d + 1) → ℝ)
    (t : StewartGaussianInputs d)
    (j : Fin d) (k : Fin (d + 1 - (j.val + 1))) :
    (stewartInputSplitEquiv d).symm (x, t) j.succ k =
      t j ((Equiv.cast (congrArg Fin (by omega :
        d + 1 - (j.val + 1) = d - j.val))) k) := by
  let e := Equiv.cast (congrArg Fin (by omega :
    d + 1 - (j.val + 1) = d - j.val))
  have hs := congrFun (stewartInputSplitEquiv_symm_succ d x t j) (e k)
  rw [stewartTailCoordinateCastEquiv,
    MeasurableEquiv.piCongrLeft_apply_apply] at hs
  exact hs.symm

theorem householderVector_cast {m n : ℕ} (h : m = n) (hm : 0 < m) (hn : 0 < n)
    (u : Fin m → ℝ) (k : Fin m) :
    householderVector hm u k =
      householderVector hn
        (fun j => u ((Equiv.cast (congrArg Fin h)).symm j))
        (Equiv.cast (congrArg Fin h) k) := by
  subst n
  simp

theorem stewartHouseholderBeta_cast {m n : ℕ} (h : m = n) (u : Fin m → ℝ) :
    stewartHouseholderBeta u =
      stewartHouseholderBeta
        (fun j => u ((Equiv.cast (congrArg Fin h)).symm j)) := by
  subst n
  simp

theorem householderAlpha_cast {m n : ℕ} (h : m = n)
    (hm : 0 < m) (hn : 0 < n) (u : Fin m → ℝ) :
    householderAlpha hm u =
      householderAlpha hn
        (fun j => u ((Equiv.cast (congrArg Fin h)).symm j)) := by
  subst n
  simp

@[simp] theorem finCastEquiv_val {m n : ℕ} (h : m = n) (i : Fin m) :
    (Equiv.cast (congrArg Fin h) i).val = i.val := by
  subst n
  rfl

theorem tail_input_reindex (d : ℕ) (x : Fin (d + 1) → ℝ)
    (t : StewartGaussianInputs d)
    (j : Fin d) :
    (fun q => (stewartInputSplitEquiv d).symm (x, t) j.succ
        ((Equiv.cast (congrArg Fin (by omega :
          d + 1 - (j.val + 1) = d - j.val))).symm q)) = t j := by
  funext q
  have hq := congrFun (stewartInputSplitEquiv_symm_succ d x t j) q
  rw [stewartTailCoordinateCastEquiv,
    MeasurableEquiv.coe_piCongrLeft] at hq
  rw [Equiv.piCongrLeft_apply] at hq
  simpa using hq

theorem tail_householderVector (d : ℕ) (x : Fin (d + 1) → ℝ)
    (t : StewartGaussianInputs d)
    (j : Fin d) (k : Fin (d + 1 - (j.val + 1))) :
    householderVector (by omega : 0 < d + 1 - (j.val + 1))
        ((stewartInputSplitEquiv d).symm (x, t) j.succ) k =
      householderVector (by omega : 0 < d - j.val) (t j)
        (Equiv.cast (congrArg Fin (by omega :
          d + 1 - (j.val + 1) = d - j.val)) k) := by
  let u := (stewartInputSplitEquiv d).symm (x, t) j.succ
  let e := Equiv.cast (congrArg Fin (by omega :
    d + 1 - (j.val + 1) = d - j.val))
  have hs : (fun q => u (e.symm q)) = t j := by
    funext q
    have hq := congrFun (stewartInputSplitEquiv_symm_succ d x t j) q
    rw [stewartTailCoordinateCastEquiv,
      MeasurableEquiv.coe_piCongrLeft] at hq
    rw [Equiv.piCongrLeft_apply] at hq
    simpa [u, e] using hq
  have hcast := householderVector_cast
    (by omega : d + 1 - (j.val + 1) = d - j.val)
    (by omega) (by omega) u k
  simpa [u, e, hs] using hcast

theorem embeddedVector_succ (d : ℕ)
    (x : Fin (d + 1) → ℝ) (t : StewartGaussianInputs d)
    (j a : Fin d) :
    stewartEmbeddedHouseholderVector j.succ
        ((stewartInputSplitEquiv d).symm (x, t) j.succ) a.succ =
      stewartEmbeddedHouseholderVector j (t j) a := by
  unfold stewartEmbeddedHouseholderVector
  by_cases hja : j.val ≤ a.val
  · have hsucc : j.succ.val ≤ a.succ.val := by simpa using hja
    simp only [hsucc, hja, dite_true]
    let k : Fin (d + 1 - (j.val + 1)) :=
      ⟨a.val - j.val, by omega⟩
    have hv := tail_householderVector d x t j k
    rw [show (⟨a.succ.val - j.succ.val, by omega⟩ :
        Fin (d + 1 - j.succ.val)) = k by
      apply Fin.ext
      simp [k]]
    calc
      _ = householderVector (by omega : 0 < d - j.val) (t j)
          (Equiv.cast (congrArg Fin (by omega :
            d + 1 - (j.val + 1) = d - j.val)) k) := hv
      _ = householderVector (by omega : 0 < d - j.val) (t j)
          ⟨a.val - j.val, by omega⟩ := by
        congr 1
        apply Fin.ext
        simpa [k] using finCastEquiv_val
          (by omega : d + 1 - (j.val + 1) = d - j.val) k
  · simp [hja]

theorem embeddedVector_zero (d : ℕ)
    (x : Fin (d + 1) → ℝ) (t : StewartGaussianInputs d)
    (j : Fin d) :
    stewartEmbeddedHouseholderVector j.succ
        ((stewartInputSplitEquiv d).symm (x, t) j.succ) 0 = 0 := by
  exact stewartEmbeddedHouseholderVector_of_lt _ _ _ (by simp)

theorem embeddedBeta_succ (d : ℕ)
    (x : Fin (d + 1) → ℝ) (t : StewartGaussianInputs d)
    (j : Fin d) :
    stewartHouseholderBeta
        (stewartEmbeddedHouseholderVector j.succ
          ((stewartInputSplitEquiv d).symm (x, t) j.succ)) =
      stewartHouseholderBeta (stewartEmbeddedHouseholderVector j (t j)) := by
  unfold stewartHouseholderBeta
  rw [Fin.sum_univ_succ]
  simp only [embeddedVector_zero, zero_mul, zero_add]
  simp_rw [embeddedVector_succ]

theorem embeddedHouseholder_succ (d : ℕ)
    (x : Fin (d + 1) → ℝ) (t : StewartGaussianInputs d)
    (j : Fin d) :
    stewartEmbeddedHouseholder j.succ
        ((stewartInputSplitEquiv d).symm (x, t) j.succ) =
      orthogonalTailBlockMatrix d (stewartEmbeddedHouseholder j (t j)) := by
  ext a b
  refine Fin.cases ?_ (fun aa => ?_) a <;>
    refine Fin.cases ?_ (fun bb => ?_) b
  · simp [stewartEmbeddedHouseholder, householder,
      orthogonalTailBlockMatrix, idMatrix]
  · have h0 : (0 : Fin (d + 1)) ≠ bb.succ := by
      intro h
      simpa using congrArg Fin.val h
    simp [stewartEmbeddedHouseholder, householder,
      orthogonalTailBlockMatrix, idMatrix, h0]
  · have h0 : aa.succ ≠ (0 : Fin (d + 1)) := by
      intro h
      simpa using congrArg Fin.val h
    simp [stewartEmbeddedHouseholder, householder,
      orthogonalTailBlockMatrix, idMatrix, h0]
  · simp [stewartEmbeddedHouseholder, householder,
      orthogonalTailBlockMatrix, idMatrix, embeddedVector_succ,
      embeddedBeta_succ]

theorem householderList_split (d : ℕ) (hd : 0 < d)
    (x : Fin (d + 1) → ℝ) (t : StewartGaussianInputs d) :
    stewartHouseholderList ((stewartInputSplitEquiv d).symm (x, t)) =
      stewartEmbeddedHouseholder (0 : Fin (d + 1)) x ::
        (stewartHouseholderList t).map
          (orthogonalTailBlockMatrix d) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  unfold stewartHouseholderList
  simp only [Nat.add_sub_cancel, List.map_ofFn]
  rw [List.ofFn_succ]
  congr 1
  apply List.ofFn_inj.mpr
  funext k
  simpa [Function.comp_def] using
    embeddedHouseholder_succ (r + 1) x t k.castSucc

theorem matrixListProduct_tailBlock (d : ℕ)
    (Ps : List (RSqMat d)) :
    matrixListProduct (Ps.map (orthogonalTailBlockMatrix d)) =
      orthogonalTailBlockMatrix d (matrixListProduct Ps) := by
  induction Ps with
  | nil =>
      simpa [matrixListProduct] using (orthogonalTailBlockMatrix_one d).symm
  | cons P Ps ih =>
      simp only [List.map_cons, matrixListProduct]
      rw [ih]
      exact (orthogonalTailBlockMatrix_mul d P (matrixListProduct Ps)).symm

theorem stewartRDiagonal_succ (d : ℕ)
    (x : Fin (d + 1) → ℝ) (t : StewartGaussianInputs d)
    (j : Fin d) :
    stewartRDiagonal ((stewartInputSplitEquiv d).symm (x, t)) j.succ =
      stewartRDiagonal t j := by
  let u := (stewartInputSplitEquiv d).symm (x, t) j.succ
  let e := Equiv.cast (congrArg Fin (by omega :
    d + 1 - (j.val + 1) = d - j.val))
  have hs : (fun q => u (e.symm q)) = t j :=
    tail_input_reindex d x t j
  unfold stewartRDiagonal
  by_cases hj : j.val + 1 < d
  · have hfull : j.succ.val + 1 < d + 1 := by simpa using hj
    simp only [hj, hfull, dite_true]
    have ha := householderAlpha_cast
      (by omega : d + 1 - (j.val + 1) = d - j.val)
      (by omega) (by omega) u
    simpa [u, e, hs] using ha
  · have hfull : ¬ j.succ.val + 1 < d + 1 := by simpa using hj
    simp only [hj, hfull, dite_false]
    congr 1
    have hq := congrFun hs (⟨0, by omega⟩ : Fin (d - j.val))
    rw [← hq]
    change u (⟨0, by omega⟩ : Fin (d + 1 - (j.val + 1))) =
      u (e.symm (⟨0, by omega⟩ : Fin (d - j.val)))
    congr 1
    apply Fin.ext
    symm
    simpa [e] using finCastEquiv_val
      (by omega : d - j.val = d + 1 - (j.val + 1))
      (⟨0, by omega⟩ : Fin (d - j.val))

theorem signDiagonal_split (d : ℕ) (hd : 0 < d)
    (x : Fin (d + 1) → ℝ) (t : StewartGaussianInputs d) :
    stewartSignDiagonal ((stewartInputSplitEquiv d).symm (x, t)) =
      matMul (d + 1) (stewartFirstSignMatrix d x)
        (orthogonalTailBlockMatrix d (stewartSignDiagonal t)) := by
  ext a b
  refine Fin.cases ?_ (fun aa => ?_) a <;>
    refine Fin.cases ?_ (fun bb => ?_) b
  · simp [stewartSignDiagonal, stewartRDiagonal,
      stewartFirstSignMatrix, matMul, diagMatrix, hd]
  · have h0 : (0 : Fin (d + 1)) ≠ bb.succ := by
      intro h
      simpa using congrArg Fin.val h
    simp [stewartSignDiagonal, stewartFirstSignMatrix, matMul,
      diagMatrix, h0]
  · have h0 : aa.succ ≠ (0 : Fin (d + 1)) := by
      intro h
      simpa using congrArg Fin.val h
    simp [stewartSignDiagonal, stewartFirstSignMatrix, matMul,
      diagMatrix, h0]
  · simp [stewartSignDiagonal, stewartFirstSignMatrix, matMul,
      diagMatrix, stewartRDiagonal_succ]

theorem firstEmbeddedHouseholder (d : ℕ)
    (x : Fin (d + 1) → ℝ) :
    stewartEmbeddedHouseholder (0 : Fin (d + 1)) x =
      householder (d + 1)
        (householderVector (by omega : 0 < d + 1) x)
        (stewartHouseholderBeta
          (householderVector (by omega : 0 < d + 1) x)) := by
  congr 1

theorem householderProduct_split (d : ℕ) (hd : 0 < d)
    (x : Fin (d + 1) → ℝ) (t : StewartGaussianInputs d) :
    matrixListProduct
        (stewartHouseholderList ((stewartInputSplitEquiv d).symm (x, t))) =
      matMul (d + 1)
        (stewartEmbeddedHouseholder (0 : Fin (d + 1)) x)
        (orthogonalTailBlockMatrix d
          (matrixListProduct (stewartHouseholderList t))) := by
  rw [householderList_split d hd x t]
  simp only [matrixListProduct]
  congr 1
  exact matrixListProduct_tailBlock d (stewartHouseholderList t)

theorem householder_mul_orthogonal {n : ℕ}
    (R : RSqMat n) (hR : IsOrthogonal n R)
    (v : Fin n → ℝ) (beta : ℝ) :
    matMul n (householder n (matMulVec n R v) beta) R =
      matMul n R (householder n v beta) := by
  have hRtR : R.transpose * R = (1 : RSqMat n) := by
    ext i j
    simpa [Matrix.mul_apply, Matrix.transpose_apply, matTranspose,
      Matrix.one_apply, idMatrix] using hR.left_inv i j
  have hrecover : Matrix.mulVec R.transpose (Matrix.mulVec R v) = v := by
    rw [Matrix.mulVec_mulVec, hRtR, Matrix.one_mulVec]
  ext i j
  have hdot : (∑ k : Fin n, matMulVec n R v k * R k j) = v j := by
    have hj := congrFun hrecover j
    simpa [Matrix.mulVec, matMulVec, Matrix.transpose_apply, mul_comm] using hj
  have hleftFactor :
      (∑ k : Fin n,
        beta * matMulVec n R v i * matMulVec n R v k * R k j) =
        beta * matMulVec n R v i *
          (∑ k : Fin n, matMulVec n R v k * R k j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hrightFactor :
      (∑ k : Fin n, R i k * (beta * v k * v j)) =
        beta * matMulVec n R v i * v j := by
    unfold matMulVec
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  calc
    matMul n (householder n (matMulVec n R v) beta) R i j =
        R i j - beta * matMulVec n R v i *
          (∑ k : Fin n, matMulVec n R v k * R k j) := by
      unfold matMul householder
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib]
      rw [show (∑ k : Fin n, idMatrix n i k * R k j) = R i j by
        simp [idMatrix]]
      exact congrArg (R i j - ·) hleftFactor
    _ = R i j - beta * matMulVec n R v i * v j := by rw [hdot]
    _ = matMul n R (householder n v beta) i j := by
      unfold matMul householder
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
      rw [show (∑ k : Fin n, R i k * idMatrix n k j) = R i j by
        simp [idMatrix]]
      rw [hrightFactor]

theorem stewartHouseholderBeta_orthogonal {n : ℕ}
    (R : RSqMat n) (hR : IsOrthogonal n R) (v : Fin n → ℝ) :
    stewartHouseholderBeta (matMulVec n R v) =
      stewartHouseholderBeta v := by
  have hnorm := vecNorm2Sq_orthogonal R v hR
  unfold stewartHouseholderBeta
  simpa [vecNorm2Sq, pow_two] using congrArg
    (fun s : ℝ => if s = 0 then 0 else 2 / s) hnorm

theorem tailBlock_orthogonal {d : ℕ} (E : RSqMat d)
    (hE : IsOrthogonal d E) :
    IsOrthogonal (d + 1) (orthogonalTailBlockMatrix d E) := by
  have hleft : E.transpose * E = (1 : RSqMat d) := by
    ext i j
    simpa [Matrix.mul_apply, Matrix.transpose_apply, matTranspose,
      Matrix.one_apply, idMatrix] using hE.left_inv i j
  have hright : E * E.transpose = (1 : RSqMat d) := by
    ext i j
    simpa [Matrix.mul_apply, Matrix.transpose_apply, matTranspose,
      Matrix.one_apply, idMatrix] using hE.right_inv i j
  constructor
  · intro i j
    have hmatrix :
        (orthogonalTailBlockMatrix d E).transpose *
            orthogonalTailBlockMatrix d E = (1 : RSqMat (d + 1)) := by
      rw [orthogonalTailBlockMatrix_transpose,
        ← orthogonalTailBlockMatrix_mul, hleft,
        orthogonalTailBlockMatrix_one]
    have hij := congrFun (congrFun hmatrix i) j
    simpa [Matrix.mul_apply, Matrix.transpose_apply, matTranspose,
      Matrix.one_apply, idMatrix] using hij
  · intro i j
    have hmatrix :
        orthogonalTailBlockMatrix d E *
            (orthogonalTailBlockMatrix d E).transpose =
          (1 : RSqMat (d + 1)) := by
      rw [orthogonalTailBlockMatrix_transpose,
        ← orthogonalTailBlockMatrix_mul, hright,
        orthogonalTailBlockMatrix_one]
    have hij := congrFun (congrFun hmatrix i) j
    simpa [Matrix.mul_apply, Matrix.transpose_apply, matTranspose,
      Matrix.one_apply, idMatrix] using hij

theorem tailBlock_transpose_mulVec_zero (d : ℕ)
    (E : RSqMat d) (x : Fin (d + 1) → ℝ) :
    matMulVec (d + 1) (matTranspose (orthogonalTailBlockMatrix d E)) x 0 =
      x 0 := by
  simp [matMulVec, matTranspose, orthogonalTailBlockMatrix,
    Fin.sum_univ_succ]

theorem householderScale_tailBlock_transpose (d : ℕ)
    (E : RSqMat d) (hE : IsOrthogonal d E)
    (x : Fin (d + 1) → ℝ) :
    householderScale (by omega : 0 < d + 1)
        (matMulVec (d + 1)
          (matTranspose (orthogonalTailBlockMatrix d E)) x) =
      householderScale (by omega : 0 < d + 1) x := by
  let R : RSqMat (d + 1) := orthogonalTailBlockMatrix d E
  have hR : IsOrthogonal (d + 1) R := tailBlock_orthogonal E hE
  have hnorm := vecNorm2Sq_orthogonal (matTranspose R) x hR.transpose
  unfold householderScale
  let p : Fin (d + 1) := ⟨0, by omega⟩
  change householderSign
      (matMulVec (d + 1)
        (matTranspose (orthogonalTailBlockMatrix d E)) x p) *
        Real.sqrt (∑ i, matMulVec (d + 1)
          (matTranspose (orthogonalTailBlockMatrix d E)) x i *
          matMulVec (d + 1)
            (matTranspose (orthogonalTailBlockMatrix d E)) x i) =
    householderSign (x p) * Real.sqrt (∑ i, x i * x i)
  have hp : matMulVec (d + 1)
      (matTranspose (orthogonalTailBlockMatrix d E)) x p = x p := by
    simp [p, matMulVec, matTranspose, orthogonalTailBlockMatrix,
      Fin.sum_univ_succ]
  rw [hp]
  congr 2
  simpa [R, vecNorm2Sq, pow_two] using hnorm

theorem householderVector_tailBlock_transpose (d : ℕ)
    (E : RSqMat d) (hE : IsOrthogonal d E)
    (x : Fin (d + 1) → ℝ) :
    matMulVec (d + 1) (orthogonalTailBlockMatrix d E)
        (householderVector (by omega : 0 < d + 1)
          (matMulVec (d + 1)
            (matTranspose (orthogonalTailBlockMatrix d E)) x)) =
      householderVector (by omega : 0 < d + 1) x := by
  let R := orthogonalTailBlockMatrix d E
  let y := matMulVec (d + 1) (matTranspose R) x
  have hR : IsOrthogonal (d + 1) R := tailBlock_orthogonal E hE
  have hRRt : R * R.transpose = (1 : RSqMat (d + 1)) := by
    ext i j
    simpa [Matrix.mul_apply, Matrix.transpose_apply, matTranspose,
      Matrix.one_apply, idMatrix] using hR.right_inv i j
  have hrecover : matMulVec (d + 1) R y = x := by
    change Matrix.mulVec R (Matrix.mulVec R.transpose x) = x
    rw [Matrix.mulVec_mulVec, hRRt, Matrix.one_mulVec]
  have hscale : householderScale (by omega : 0 < d + 1) y =
      householderScale (by omega : 0 < d + 1) x := by
    simpa [R, y] using householderScale_tailBlock_transpose d E hE x
  funext a
  refine Fin.cases ?_ (fun aa => ?_) a
  · simp [matMulVec, matTranspose, R, y, orthogonalTailBlockMatrix,
      Fin.sum_univ_succ, householderVector, hscale]
  · have ha := congrFun hrecover aa.succ
    simpa [matMulVec, R, y, orthogonalTailBlockMatrix,
      Fin.sum_univ_succ, householderVector] using ha

theorem householderBeta_tailBlock_transpose (d : ℕ)
    (E : RSqMat d) (hE : IsOrthogonal d E)
    (x : Fin (d + 1) → ℝ) :
    stewartHouseholderBeta
        (householderVector (by omega : 0 < d + 1) x) =
      stewartHouseholderBeta
        (householderVector (by omega : 0 < d + 1)
          (matMulVec (d + 1)
            (matTranspose (orthogonalTailBlockMatrix d E)) x)) := by
  let R := orthogonalTailBlockMatrix d E
  let y := matMulVec (d + 1) (matTranspose R) x
  let vy := householderVector (by omega : 0 < d + 1) y
  have hR : IsOrthogonal (d + 1) R := tailBlock_orthogonal E hE
  have hv : matMulVec (d + 1) R vy =
      householderVector (by omega : 0 < d + 1) x := by
    simpa [R, y, vy] using
      householderVector_tailBlock_transpose d E hE x
  calc
    stewartHouseholderBeta
        (householderVector (by omega : 0 < d + 1) x) =
      stewartHouseholderBeta (matMulVec (d + 1) R vy) :=
        congrArg stewartHouseholderBeta hv.symm
    _ = stewartHouseholderBeta vy :=
      stewartHouseholderBeta_orthogonal R hR vy
    _ = stewartHouseholderBeta
        (householderVector (by omega : 0 < d + 1)
          (matMulVec (d + 1)
            (matTranspose (orthogonalTailBlockMatrix d E)) x)) := by
      rfl

theorem firstSignMatrix_tailBlock_transpose (d : ℕ)
    (E : RSqMat d) (hE : IsOrthogonal d E)
    (x : Fin (d + 1) → ℝ) :
    stewartFirstSignMatrix d x =
      stewartFirstSignMatrix d
        (matMulVec (d + 1)
          (matTranspose (orthogonalTailBlockMatrix d E)) x) := by
  have hscale := householderScale_tailBlock_transpose d E hE x
  have halpha : householderAlpha (by omega : 0 < d + 1) x =
      householderAlpha (by omega : 0 < d + 1)
        (matMulVec (d + 1)
          (matTranspose (orthogonalTailBlockMatrix d E)) x) := by
    unfold householderAlpha
    rw [hscale]
  ext i j
  refine Fin.cases ?_ (fun ii => ?_) i <;>
    refine Fin.cases ?_ (fun jj => ?_) j <;>
    simp [stewartFirstSignMatrix, diagMatrix, halpha]

theorem firstSignMatrix_commutes_tailBlock (d : ℕ)
    (E : RSqMat d) (x : Fin (d + 1) → ℝ) :
    matMul (d + 1) (stewartFirstSignMatrix d x)
        (orthogonalTailBlockMatrix d E) =
      matMul (d + 1) (orthogonalTailBlockMatrix d E)
        (stewartFirstSignMatrix d x) := by
  ext i j
  refine Fin.cases ?_ (fun ii => ?_) i <;>
    refine Fin.cases ?_ (fun jj => ?_) j <;>
    simp [stewartFirstSignMatrix, matMul, diagMatrix,
      orthogonalTailBlockMatrix]

theorem firstHouseholder_tailBlock_equivariant (d : ℕ)
    (E : RSqMat d) (hE : IsOrthogonal d E)
    (x : Fin (d + 1) → ℝ) :
    matMul (d + 1)
        (householder (d + 1)
          (householderVector (by omega : 0 < d + 1) x)
          (stewartHouseholderBeta
            (householderVector (by omega : 0 < d + 1) x)))
        (orthogonalTailBlockMatrix d E) =
      matMul (d + 1) (orthogonalTailBlockMatrix d E)
        (householder (d + 1)
          (householderVector (by omega : 0 < d + 1)
            (matMulVec (d + 1)
              (matTranspose (orthogonalTailBlockMatrix d E)) x))
          (stewartHouseholderBeta
            (householderVector (by omega : 0 < d + 1)
              (matMulVec (d + 1)
                (matTranspose (orthogonalTailBlockMatrix d E)) x)))) := by
  let R := orthogonalTailBlockMatrix d E
  let y := matMulVec (d + 1) (matTranspose R) x
  let vy := householderVector (by omega : 0 < d + 1) y
  have hR : IsOrthogonal (d + 1) R := tailBlock_orthogonal E hE
  have hv : matMulVec (d + 1) R vy =
      householderVector (by omega : 0 < d + 1) x := by
    simpa [R, y, vy] using
      householderVector_tailBlock_transpose d E hE x
  have hb : stewartHouseholderBeta
      (householderVector (by omega : 0 < d + 1) x) =
        stewartHouseholderBeta vy := by
    simpa [R, y, vy] using
      householderBeta_tailBlock_transpose d E hE x
  have hbase := householder_mul_orthogonal R hR vy
    (stewartHouseholderBeta vy)
  simpa [R, y, vy, hv, hb] using hbase

theorem stewartFirstSection_tailBlock_equivariant (d : ℕ)
    (E : RSqMat d) (hE : IsOrthogonal d E)
    (x : Fin (d + 1) → ℝ) :
    matMul (d + 1) (stewartFirstSectionMatrix d x)
        (orthogonalTailBlockMatrix d E) =
      matMul (d + 1) (orthogonalTailBlockMatrix d E)
        (stewartFirstSectionMatrix d
          (matMulVec (d + 1)
            (matTranspose (orthogonalTailBlockMatrix d E)) x)) := by
  let R : RSqMat (d + 1) := orthogonalTailBlockMatrix d E
  let y := matMulVec (d + 1) (matTranspose R) x
  let Sx : RSqMat (d + 1) := stewartFirstSignMatrix d x
  let Sy : RSqMat (d + 1) := stewartFirstSignMatrix d y
  let Hx : RSqMat (d + 1) := householder (d + 1)
    (householderVector (by omega : 0 < d + 1) x)
    (stewartHouseholderBeta
      (householderVector (by omega : 0 < d + 1) x))
  let Hy : RSqMat (d + 1) := householder (d + 1)
    (householderVector (by omega : 0 < d + 1) y)
    (stewartHouseholderBeta
      (householderVector (by omega : 0 < d + 1) y))
  have hH : Hx * R = R * Hy := by
    simpa [R, y, Hx, Hy, matMul] using
      firstHouseholder_tailBlock_equivariant d E hE x
  have hS : Sx = Sy := by
    simpa [R, y, Sx, Sy] using
      firstSignMatrix_tailBlock_transpose d E hE x
  have hcomm : Sx * R = R * Sx := by
    simpa [R, Sx, matMul] using
      firstSignMatrix_commutes_tailBlock d E x
  change (Sx * Hx) * R = R * (Sy * Hy)
  calc
    (Sx * Hx) * R = Sx * (Hx * R) := Matrix.mul_assoc _ _ _
    _ = Sx * (R * Hy) := by rw [hH]
    _ = (Sx * R) * Hy := (Matrix.mul_assoc _ _ _).symm
    _ = (R * Sx) * Hy := by rw [hcomm]
    _ = R * (Sx * Hy) := Matrix.mul_assoc _ _ _
    _ = R * (Sy * Hy) := by rw [hS]

theorem stewartOrthogonalMatrix_split (d : ℕ) (hd : 0 < d)
    (x : Fin (d + 1) → ℝ) (t : StewartGaussianInputs d) :
    stewartOrthogonalMatrix ((stewartInputSplitEquiv d).symm (x, t)) =
      matMul (d + 1)
        (orthogonalTailBlockMatrix d (stewartOrthogonalMatrix t))
        (stewartFirstSectionMatrix d
          (matMulVec (d + 1)
            (matTranspose (orthogonalTailBlockMatrix d
              (matrixListProduct (stewartHouseholderList t)))) x)) := by
  let E : RSqMat d := matrixListProduct (stewartHouseholderList t)
  let Dt : RSqMat d := stewartSignDiagonal t
  let BDt : RSqMat (d + 1) := orthogonalTailBlockMatrix d Dt
  let R : RSqMat (d + 1) := orthogonalTailBlockMatrix d E
  let y := matMulVec (d + 1) (matTranspose R) x
  let Sx : RSqMat (d + 1) := stewartFirstSignMatrix d x
  let Sy : RSqMat (d + 1) := stewartFirstSectionMatrix d y
  let Hx : RSqMat (d + 1) := stewartEmbeddedHouseholder 0 x
  have hE : IsOrthogonal d E := by
    exact matrixListProduct_isOrthogonal (stewartHouseholderList t)
      (stewartHouseholderList_orthogonal t)
  have hD : stewartSignDiagonal
      ((stewartInputSplitEquiv d).symm (x, t)) = Sx * BDt := by
    simpa [Sx, BDt, Dt, matMul] using signDiagonal_split d hd x t
  have hP : matrixListProduct
      (stewartHouseholderList ((stewartInputSplitEquiv d).symm (x, t))) =
        Hx * R := by
    simpa [Hx, R, E, matMul] using householderProduct_split d hd x t
  have hcomm : Sx * BDt = BDt * Sx := by
    simpa [Sx, BDt, Dt, matMul] using
      firstSignMatrix_commutes_tailBlock d Dt x
  have hsection : (Sx * Hx) * R = R * Sy := by
    simpa [Sx, Hx, Sy, R, E, y, stewartFirstSectionMatrix,
      firstEmbeddedHouseholder, matMul] using
      stewartFirstSection_tailBlock_equivariant d E hE x
  have hblock : BDt * R =
      orthogonalTailBlockMatrix d (Dt * E) := by
    simpa [BDt, R] using
      (orthogonalTailBlockMatrix_mul d Dt E).symm
  change matMul (d + 1)
      (stewartSignDiagonal ((stewartInputSplitEquiv d).symm (x, t)))
      (matrixListProduct
        (stewartHouseholderList ((stewartInputSplitEquiv d).symm (x, t)))) =
    matMul (d + 1) (orthogonalTailBlockMatrix d (Dt * E)) Sy
  rw [hD, hP]
  change (Sx * BDt) * (Hx * R) =
    orthogonalTailBlockMatrix d (Dt * E) * Sy
  calc
    (Sx * BDt) * (Hx * R) = (BDt * Sx) * (Hx * R) := by rw [hcomm]
    _ = BDt * ((Sx * Hx) * R) := by noncomm_ring
    _ = BDt * (R * Sy) := by rw [hsection]
    _ = (BDt * R) * Sy := (Matrix.mul_assoc _ _ _).symm
    _ = orthogonalTailBlockMatrix d (Dt * E) * Sy := by rw [hblock]

theorem stewartFirstSectionMatrix_zero (x : Fin 1 → ℝ) :
    stewartFirstSectionMatrix 0 x 0 0 = householderSign (x 0) := by
  simp [stewartFirstSectionMatrix, stewartFirstSignMatrix,
    householderVector, householderScale, householderAlpha,
    stewartHouseholderBeta, householder, matMul, diagMatrix, idMatrix]
  rw [show Real.sqrt (x 0 * x 0) = |x 0| by
    rw [show x 0 * x 0 = (x 0) ^ 2 by ring, Real.sqrt_sq_eq_abs]]
  by_cases hx : x 0 < 0
  · have hxne : x 0 ≠ 0 := ne_of_lt hx
    have hnotpos : ¬ 0 < x 0 := by linarith
    simp [householderSign, hx, abs_of_neg hx, hxne]
    field_simp
    ring_nf
    simp [hnotpos]
  · by_cases hx0 : x 0 = 0
    · simp [householderSign, hx0]
    · have hxpos : 0 < x 0 := lt_of_le_of_ne (le_of_not_gt hx) (Ne.symm hx0)
      simp [householderSign, hx, abs_of_pos hxpos, hx0]
      field_simp
      ring_nf
      simp [hxpos]
      exact Nat.cast_one

@[simp] theorem householderSign_idempotent (a : ℝ) :
    householderSign (householderSign a) = householderSign a := by
  by_cases ha : a < 0 <;>
    simp [householderSign, ha]

theorem stewartOrthogonalMatrix_split_all (d : ℕ)
    (x : Fin (d + 1) → ℝ) (t : StewartGaussianInputs d) :
    stewartOrthogonalMatrix ((stewartInputSplitEquiv d).symm (x, t)) =
      matMul (d + 1)
        (orthogonalTailBlockMatrix d (stewartOrthogonalMatrix t))
        (stewartFirstSectionMatrix d
          (matMulVec (d + 1)
            (matTranspose (orthogonalTailBlockMatrix d
              (matrixListProduct (stewartHouseholderList t)))) x)) := by
  by_cases hd : 0 < d
  · exact stewartOrthogonalMatrix_split d hd x t
  · have hd0 : d = 0 := by omega
    subst d
    ext i j
    fin_cases i
    fin_cases j
    simp [stewartOrthogonalMatrix, stewartOrthogonalProduct,
      stewartSignDiagonal, stewartRDiagonal, stewartHouseholderList,
      matrixListProduct, orthogonalTailBlockMatrix, matMul, matMulVec,
      matTranspose, diagMatrix, idMatrix,
      stewartFirstSectionMatrix_zero,
      householderSign_idempotent]

noncomputable def stewartHouseholderGroupOutput (d : ℕ)
    (t : StewartGaussianInputs d) : RealOrthogonalGroup d :=
  ⟨matrixListProduct (stewartHouseholderList t), by
    rw [Matrix.mem_orthogonalGroup_iff]
    ext i j
    simpa [Matrix.mul_apply, Matrix.transpose_apply, matTranspose,
      Matrix.one_apply, idMatrix] using
      (matrixListProduct_isOrthogonal (stewartHouseholderList t)
        (stewartHouseholderList_orthogonal t)).right_inv i j⟩

theorem measurable_stewartHouseholderGroupOutput (d : ℕ) :
    Measurable (stewartHouseholderGroupOutput d) := by
  exact measurable_stewartHouseholderListProduct.subtype_mk

noncomputable def stewartTailRotation (d : ℕ)
    (t : StewartGaussianInputs d) : RealOrthogonalGroup (d + 1) :=
  orthogonalTailEmbedding d (stewartHouseholderGroupOutput d t)

theorem measurable_stewartTailRotation (d : ℕ) :
    Measurable (stewartTailRotation d) := by
  exact (continuous_orthogonalTailEmbedding d).measurable.comp
    (measurable_stewartHouseholderGroupOutput d)

noncomputable def stewartTailRotateVector (d : ℕ)
    (p : StewartGaussianInputs d × (Fin (d + 1) → ℝ)) :
    Fin (d + 1) → ℝ :=
  Matrix.mulVec
    (((stewartTailRotation d p.1)⁻¹ : RealOrthogonalGroup (d + 1)) :
      Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) p.2

theorem measurable_stewartTailRotateVector (d : ℕ) :
    Measurable (stewartTailRotateVector d) := by
  unfold stewartTailRotateVector
  have hQ : Measurable fun p : StewartGaussianInputs d ×
      (Fin (d + 1) → ℝ) => (stewartTailRotation d p.1)⁻¹ :=
    (measurable_stewartTailRotation d).comp measurable_fst |>.inv
  have hM : Measurable fun p : StewartGaussianInputs d ×
      (Fin (d + 1) → ℝ) =>
      (((stewartTailRotation d p.1)⁻¹ : RealOrthogonalGroup (d + 1)) :
        Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :=
    continuous_subtype_val.measurable.comp hQ
  refine measurable_pi_lambda _ fun i => ?_
  exact Finset.measurable_fun_sum Finset.univ fun j _ =>
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hM)).mul
      ((measurable_pi_apply j).comp measurable_snd)

theorem stewartTailRotateVector_eq_transpose (d : ℕ)
    (t : StewartGaussianInputs d) (x : Fin (d + 1) → ℝ) :
    stewartTailRotateVector d (t, x) =
      matMulVec (d + 1)
        (matTranspose (orthogonalTailBlockMatrix d
          (matrixListProduct (stewartHouseholderList t)))) x := by
  funext i
  simp [stewartTailRotateVector, stewartTailRotation,
    stewartHouseholderGroupOutput, orthogonalTailEmbedding,
    Matrix.mulVec, matMulVec, matTranspose,
    dotProduct, mul_comm]

theorem stewartOrthogonalGroupOutput_split (d : ℕ)
    (x : Fin (d + 1) → ℝ) (t : StewartGaussianInputs d) :
    stewartOrthogonalGroupOutput
        ((stewartInputSplitEquiv d).symm (x, t)) =
      orthogonalTailEmbedding d (stewartOrthogonalGroupOutput t) *
        stewartFirstSection d (stewartTailRotateVector d (t, x)) := by
  apply Subtype.ext
  rw [stewartTailRotateVector_eq_transpose]
  simpa [stewartOrthogonalGroupOutput, orthogonalTailEmbedding,
    stewartFirstSection, matMul] using
    stewartOrthogonalMatrix_split_all d x t

theorem stewartTailRotate_measurePreserving (d : ℕ) :
    MeasurePreserving
      (fun p : StewartGaussianInputs d × (Fin (d + 1) → ℝ) =>
        (p.1, stewartTailRotateVector d p))
      ((stewartGaussianInputMeasure d).prod
        (standardGaussianVectorMeasure (d + 1)))
      ((stewartGaussianInputMeasure d).prod
        (standardGaussianVectorMeasure (d + 1))) := by
  letI : IsProbabilityMeasure (standardGaussianVectorMeasure (d + 1)) :=
    standardGaussianVectorMeasure_isProbabilityMeasure (d + 1)
  letI : SFinite (standardGaussianVectorMeasure (d + 1)) := inferInstance
  letI : SFinite (stewartGaussianInputMeasure d) := inferInstance
  refine (MeasurePreserving.id (stewartGaussianInputMeasure d)).skew_product
    (g := fun t x => stewartTailRotateVector d (t, x)) ?_ ?_
  · simpa [Function.uncurry] using measurable_stewartTailRotateVector d
  filter_upwards [] with t
  simpa [stewartTailRotateVector] using
    standardGaussianVectorMeasure_map_orthogonalGroup (d + 1)
      ((stewartTailRotation d t)⁻¹)

/-! ## Measure-level induction scaffold -/

noncomputable def stewartGaussianFiberProducer (d : ℕ)
    (p : RealOrthogonalGroup d × (Fin (d + 1) → ℝ)) :
    RealOrthogonalGroup (d + 1) :=
  orthogonalTailEmbedding d p.1 * stewartFirstSection d p.2

theorem measurable_stewartGaussianFiberProducer (d : ℕ) :
    Measurable (stewartGaussianFiberProducer d) := by
  exact ((continuous_orthogonalTailEmbedding d).measurable.comp measurable_fst).mul
    ((measurable_stewartFirstSection d).comp measurable_snd)

instance stewartOrthogonalGroupLaw_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (stewartOrthogonalGroupLaw n) := by
  unfold stewartOrthogonalGroupLaw
  exact Measure.isProbabilityMeasure_map
    measurable_stewartOrthogonalGroupOutput.aemeasurable

theorem measure_eq_of_subsingleton_probability
    {α : Type*} [MeasurableSpace α] [Subsingleton α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    μ = ν := by
  ext s hs
  by_cases h : s.Nonempty
  · rcases h with ⟨y, hy⟩
    have hsuniv : s = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      simpa only [Subsingleton.elim x y] using hy
    rw [hsuniv]
    simp
  · have hsempty : s = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    simp [hsempty]

theorem stewartOrthogonalGroupLaw_zero :
    stewartOrthogonalGroupLaw 0 = normalizedOrthogonalHaar 0 := by
  letI : Subsingleton (RealOrthogonalGroup 0) := by
    constructor
    intro Q R
    apply Subtype.ext
    ext i
    exact Fin.elim0 i
  exact measure_eq_of_subsingleton_probability _ _

noncomputable def stewartSplitTailFirst (d : ℕ)
    (z : StewartGaussianInputs (d + 1)) :
    StewartGaussianInputs d × (Fin (d + 1) → ℝ) :=
  ((stewartInputSplitEquiv d z).2, (stewartInputSplitEquiv d z).1)

noncomputable def stewartTailRotateMap (d : ℕ)
    (p : StewartGaussianInputs d × (Fin (d + 1) → ℝ)) :
    StewartGaussianInputs d × (Fin (d + 1) → ℝ) :=
  (p.1, stewartTailRotateVector d p)

noncomputable def stewartTailOutputMap (d : ℕ)
    (p : StewartGaussianInputs d × (Fin (d + 1) → ℝ)) :
    RealOrthogonalGroup d × (Fin (d + 1) → ℝ) :=
  (stewartOrthogonalGroupOutput p.1, p.2)

noncomputable def stewartSuccessorComposite (d : ℕ)
    (z : StewartGaussianInputs (d + 1)) :
    RealOrthogonalGroup (d + 1) :=
  stewartGaussianFiberProducer d
    (stewartTailOutputMap d
      (stewartTailRotateMap d (stewartSplitTailFirst d z)))

theorem stewartSuccessorComposite_eq (d : ℕ) :
    stewartSuccessorComposite d =
      stewartOrthogonalGroupOutput (n := d + 1) := by
  funext z
  calc
    stewartSuccessorComposite d z =
        orthogonalTailEmbedding d
            (stewartOrthogonalGroupOutput (stewartInputSplitEquiv d z).2) *
          stewartFirstSection d
            (stewartTailRotateVector d
              ((stewartInputSplitEquiv d z).2,
                (stewartInputSplitEquiv d z).1)) := rfl
    _ = stewartOrthogonalGroupOutput
          ((stewartInputSplitEquiv d).symm
            ((stewartInputSplitEquiv d z).1,
              (stewartInputSplitEquiv d z).2)) :=
      (stewartOrthogonalGroupOutput_split d
        (stewartInputSplitEquiv d z).1
        (stewartInputSplitEquiv d z).2).symm
    _ = stewartOrthogonalGroupOutput z := by
      rw [(stewartInputSplitEquiv d).symm_apply_apply]

theorem stewartOrthogonalGroupLaw_succ
    (d : ℕ)
    (hd : stewartOrthogonalGroupLaw d = normalizedOrthogonalHaar d)
    (hraw : Measure.map (stewartGaussianFiberProducer d)
        ((normalizedOrthogonalHaar d).prod
          (standardGaussianVectorMeasure (d + 1))) =
        normalizedOrthogonalHaar (d + 1)) :
    stewartOrthogonalGroupLaw (d + 1) =
      normalizedOrthogonalHaar (d + 1) := by
  let γ := standardGaussianVectorMeasure (d + 1)
  let μ := stewartGaussianInputMeasure d
  letI : IsProbabilityMeasure γ :=
    standardGaussianVectorMeasure_isProbabilityMeasure (d + 1)
  letI : SFinite γ := inferInstance
  letI : SFinite μ := inferInstance
  have hsplit0 := (Measure.measurePreserving_swap (μ := γ) (ν := μ)).comp
    (stewartInputSplitEquiv_measurePreserving d)
  have hsplit : MeasurePreserving (stewartSplitTailFirst d)
      (stewartGaussianInputMeasure (d + 1)) (μ.prod γ) := by
    simpa [stewartSplitTailFirst, Function.comp_def, γ, μ] using hsplit0
  have hrotate : MeasurePreserving (stewartTailRotateMap d)
      (μ.prod γ) (μ.prod γ) := by
    simpa [stewartTailRotateMap, γ, μ] using
      stewartTailRotate_measurePreserving d
  have hout0 :=
    (measurable_stewartOrthogonalGroupOutput.measurePreserving μ).prod
      (MeasurePreserving.id γ)
  have hmap : Measure.map (stewartOrthogonalGroupOutput (n := d)) μ =
      normalizedOrthogonalHaar d := by
    simpa [stewartOrthogonalGroupLaw, μ] using hd
  rw [hmap] at hout0
  have hout : MeasurePreserving (stewartTailOutputMap d)
      (μ.prod γ) ((normalizedOrthogonalHaar d).prod γ) := by
    simpa [stewartTailOutputMap, γ, μ, Prod.map] using hout0
  have hproducer : MeasurePreserving (stewartGaussianFiberProducer d)
      ((normalizedOrthogonalHaar d).prod γ)
      (normalizedOrthogonalHaar (d + 1)) :=
    ⟨measurable_stewartGaussianFiberProducer d, by simpa [γ] using hraw⟩
  have hcomp := hproducer.comp (hout.comp (hrotate.comp hsplit))
  have hcomp' : MeasurePreserving (stewartSuccessorComposite d)
      (stewartGaussianInputMeasure (d + 1))
      (normalizedOrthogonalHaar (d + 1)) := by
    simpa [stewartSuccessorComposite, Function.comp_def] using hcomp
  rw [stewartSuccessorComposite_eq] at hcomp'
  simpa [stewartOrthogonalGroupLaw] using hcomp'.map_eq

end NumStability
