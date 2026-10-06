import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Matrix.Normed

namespace HighamBench

open scoped BigOperators Matrix.Norms.Frobenius

structure StandardFPModel where
  u : ℝ
  u_nonneg : 0 ≤ u
  fl_add : ℝ → ℝ → ℝ
  fl_sub : ℝ → ℝ → ℝ
  fl_mul : ℝ → ℝ → ℝ
  fl_div : ℝ → ℝ → ℝ
  fl_sqrt : ℝ → ℝ
  fl_add_zero : ∀ x : ℝ, fl_add 0 x = x
  model_add : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_add x y = (x + y) * (1 + δ)
  model_sub : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_sub x y = (x - y) * (1 + δ)
  model_mul : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_mul x y = (x * y) * (1 + δ)
  model_div : ∀ x y : ℝ, y ≠ 0 → ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_div x y = (x / y) * (1 + δ)
  model_sqrt : ∀ x : ℝ, 0 ≤ x → ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_sqrt x = Real.sqrt x * (1 + δ)

noncomputable def gamma (u : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * u) / (1 - (n : ℝ) * u)

def GammaValid (u : ℝ) (n : ℕ) : Prop :=
  (n : ℝ) * u < 1

noncomputable def roundedDotProduct (fp : StandardFPModel) (n : ℕ)
    (x y : Fin n → ℝ) : ℝ :=
  match n with
  | 0 => 0
  | n + 1 =>
      Fin.foldl n
        (fun acc i ↦ fp.fl_add acc (fp.fl_mul (x i.succ) (y i.succ)))
        (fp.fl_mul (x 0) (y 0))

noncomputable def roundedMatVec (fp : StandardFPModel) (m n : ℕ)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i ↦ roundedDotProduct fp n (A i) x

noncomputable def roundedForwardSubSteps (fp : StandardFPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (b : Fin n → ℝ) :
    ∀ k : ℕ, k ≤ n → (Fin n → ℝ) → Fin n → ℝ
  | 0, _, x => x
  | k + 1, hk, x =>
      have hlt : n - k - 1 < n := by omega
      let ik : Fin n := ⟨n - k - 1, hlt⟩
      let s := Fin.foldl (n - k - 1)
        (fun acc (t : Fin (n - k - 1)) ↦
          fp.fl_sub acc
            (fp.fl_mul (L ik ⟨t.val, by omega⟩) (x ⟨t.val, by omega⟩)))
        (b ik)
      let x' := Function.update x ik (fp.fl_div s (L ik ik))
      roundedForwardSubSteps fp n L b k (Nat.le_of_succ_le hk) x'

noncomputable def roundedForwardSub (fp : StandardFPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (b : Fin n → ℝ) : Fin n → ℝ :=
  roundedForwardSubSteps fp n L b n (le_refl n) (fun _ ↦ 0)

abbrev P15Matrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

abbrev P15RectMatrix (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

abbrev P15Vector (n : ℕ) := Fin n → ℝ

noncomputable def p15RectMatMul {m n p : ℕ}
    (A : P15RectMatrix m n) (B : P15RectMatrix n p) :
    P15RectMatrix m p :=
  fun i j ↦ ∑ k : Fin n, A i k * B k j

noncomputable def p15MatMul {n : ℕ} (A B : P15Matrix n) : P15Matrix n :=
  fun i j ↦ ∑ k : Fin n, A i k * B k j

noncomputable def p15MatVec {n : ℕ} (A : P15Matrix n)
    (x : P15Vector n) : P15Vector n :=
  fun i ↦ ∑ j : Fin n, A i j * x j

noncomputable def p15RectFrobNorm {m n : ℕ}
    (A : P15RectMatrix m n) : ℝ :=
  Real.sqrt (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2)

noncomputable def p15FrobNorm {n : ℕ} (A : P15Matrix n) : ℝ :=
  p15RectFrobNorm A

def p15RectTranspose {m n : ℕ} (A : P15RectMatrix m n) :
    P15RectMatrix n m :=
  fun j i ↦ A i j

def p15RectAdd {m n : ℕ}
    (A B : P15RectMatrix m n) : P15RectMatrix m n :=
  fun i j ↦ A i j + B i j

noncomputable def p15RectMatVec {m n : ℕ}
    (A : P15RectMatrix m n) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i ↦ ∑ j : Fin n, A i j * x j

noncomputable def p15RoundedRectMatVec (fp : StandardFPModel) {m n : ℕ}
    (A : P15RectMatrix m n) (x : Fin n → ℝ) : Fin m → ℝ :=
  roundedMatVec fp m n A x

noncomputable def p15RoundedLowRankMatVec (fp : StandardFPModel) {b r : ℕ}
    (X Y : P15RectMatrix b r) (v : P15Vector b) : P15Vector b :=
  p15RoundedRectMatVec fp X
    (p15RoundedRectMatVec fp (p15RectTranspose Y) v)

def p15LowerTriangular {n : ℕ} (L : P15Matrix n) : Prop :=
  ∀ i j, i.val < j.val → L i j = 0

noncomputable def p15LowRankMatrix {b r : ℕ}
    (X Y : P15RectMatrix b r) : P15Matrix b :=
  p15RectMatMul X (p15RectTranspose Y)

def p15OrthonormalColumns {b r : ℕ} (X : P15RectMatrix b r) : Prop :=
  ∀ j k, (∑ i : Fin b, X i j * X i k) = if j = k then 1 else 0

noncomputable def p15GammaReal (k u : ℝ) : ℝ :=
  k * u / (1 - k * u)

noncomputable def p15LowRankMatMulCost (b r : ℕ) : ℝ :=
  (b : ℝ) + 2 * (r : ℝ) * Real.sqrt (r : ℝ)

structure P15RoundedMatMulStage (m n p : ℕ) (u : ℝ)
    (A : P15RectMatrix m n) (B : P15RectMatrix n p) where
  error : P15RectMatrix m p
  error_le : p15RectFrobNorm error ≤
    p15GammaReal (n : ℝ) u * p15RectFrobNorm A * p15RectFrobNorm B

noncomputable def P15RoundedMatMulStage.result {m n p : ℕ} {u : ℝ}
    {A : P15RectMatrix m n} {B : P15RectMatrix n p}
    (stage : P15RoundedMatMulStage m n p u A B) : P15RectMatrix m p :=
  p15RectMatMul A B + stage.error

inductive P15LowRankMatMulTrace {b r : ℕ} (u : ℝ)
    (XA YA XB YB : P15RectMatrix b r) where
  | leftAssociated
      (middleStage : P15RoundedMatMulStage r b r u
        (p15RectTranspose YA) YB)
      (leftStage : P15RoundedMatMulStage b r r u XA middleStage.result)
      (finalStage : P15RoundedMatMulStage b r b u leftStage.result
        (p15RectTranspose XB))
  | rightAssociated
      (middleStage : P15RoundedMatMulStage r b r u
        (p15RectTranspose YA) YB)
      (rightStage : P15RoundedMatMulStage r r b u middleStage.result
        (p15RectTranspose XB))
      (finalStage : P15RoundedMatMulStage b r b u XA rightStage.result)

noncomputable def P15LowRankMatMulTrace.result {b r : ℕ} {u : ℝ}
    {XA YA XB YB : P15RectMatrix b r}
    (trace : P15LowRankMatMulTrace u XA YA XB YB) : P15Matrix b :=
  match trace with
  | .leftAssociated _ _ finalStage => finalStage.result
  | .rightAssociated _ _ finalStage => finalStage.result

structure P15LowRankMatMulExecution (b r : ℕ) where
  A : P15Matrix b
  B : P15Matrix b
  XA : P15RectMatrix b r
  YA : P15RectMatrix b r
  XB : P15RectMatrix b r
  YB : P15RectMatrix b r
  epsilon : ℝ
  betaA : ℝ
  betaB : ℝ
  unitRoundoff : ℝ
  unitRoundoff_nonneg : 0 ≤ unitRoundoff
  gamma_valid :
    p15LowRankMatMulCost b r * unitRoundoff < 1
  xA_orthonormal : p15OrthonormalColumns XA
  xB_orthonormal : p15OrthonormalColumns XB
  approximationErrorA : P15Matrix b
  approximationErrorB : P15Matrix b
  approximationA_eq :
    p15LowRankMatrix XA YA = A + approximationErrorA
  approximationB_eq :
    p15LowRankMatrix YB XB = B + approximationErrorB
  approximationErrorA_le :
    p15FrobNorm approximationErrorA ≤ epsilon * betaA
  approximationErrorB_le :
    p15FrobNorm approximationErrorB ≤ epsilon * betaB
  trace : P15LowRankMatMulTrace unitRoundoff XA YA XB YB

end HighamBench
