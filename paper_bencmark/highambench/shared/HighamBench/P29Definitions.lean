import Mathlib

namespace HighamBench

open scoped BigOperators

/-! Paper-local definitions for the first-step Schur-complement analysis and
the `LDLᵀ` solution phase in Appendix B. -/

structure P29FPModel where
  u : ℝ
  u_nonneg : 0 ≤ u
  fl_add : ℝ → ℝ → ℝ
  fl_sub : ℝ → ℝ → ℝ
  fl_mul : ℝ → ℝ → ℝ
  fl_div : ℝ → ℝ → ℝ
  fl_add_zero : ∀ x : ℝ, fl_add 0 x = x
  model_add : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_add x y = (x + y) * (1 + δ)
  model_sub : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_sub x y = (x - y) * (1 + δ)
  model_mul : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_mul x y = (x * y) * (1 + δ)
  model_div : ∀ x y : ℝ, y ≠ 0 → ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_div x y = (x / y) * (1 + δ)

abbrev P29Matrix (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

noncomputable def p29Gamma (u : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * u) / (1 - (n : ℝ) * u)

def P29GammaValid (u : ℝ) (n : ℕ) : Prop :=
  (n : ℝ) * u < 1

noncomputable def p29Transpose {m n : ℕ}
    (A : P29Matrix m n) : P29Matrix n m :=
  fun i j => A j i

noncomputable def p29MatMul {m n p : ℕ}
    (A : P29Matrix m n) (B : P29Matrix n p) : P29Matrix m p :=
  fun i j => ∑ k : Fin n, A i k * B k j

/-- The entrywise-sum matrix norm used to make the paper's suppressed
dimension-dependent constants explicit. -/
noncomputable def p29EntryNorm {m n : ℕ} (A : P29Matrix m n) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin n, |A i j|

noncomputable def p29RoundedDotProduct (fp : P29FPModel) (n : ℕ)
    (x y : Fin n → ℝ) : ℝ :=
  match n with
  | 0 => 0
  | n' + 1 =>
      Fin.foldl n'
        (fun acc i => fp.fl_add acc (fp.fl_mul (x i.succ) (y i.succ)))
        (fp.fl_mul (x 0) (y 0))

noncomputable def p29RoundedMatMul (fp : P29FPModel) {m n p : ℕ}
    (A : P29Matrix m n) (B : P29Matrix n p) : P29Matrix m p :=
  fun i j => p29RoundedDotProduct fp n (A i) (fun k => B k j)

/-- The rounded first-step update `A₂₂ - L₁₁ A₁₂` in Appendix B. -/
noncomputable def p29RoundedSchur (fp : P29FPModel) {m r : ℕ}
    (A22 : P29Matrix m m) (L11 : P29Matrix m r)
    (A12 : P29Matrix r m) : P29Matrix m m :=
  fun i j => fp.fl_sub (A22 i j) (p29RoundedMatMul fp L11 A12 i j)

noncomputable def p29ExactSchur {m r : ℕ}
    (A22 : P29Matrix m m) (L11 : P29Matrix m r)
    (A12 : P29Matrix r m) : P29Matrix m m :=
  fun i j => A22 i j - p29MatMul L11 A12 i j

/-- The explicit componentwise version of the first-step `cᵣ ε` bound in
Appendix B. -/
noncomputable def p29SchurErrorMajorant (fp : P29FPModel) {m r : ℕ}
    (A22 : P29Matrix m m) (L11 : P29Matrix m r)
    (A12 : P29Matrix r m) (i j : Fin m) : ℝ :=
  fp.u * |A22 i j - p29RoundedMatMul fp L11 A12 i j| +
    p29Gamma fp.u r * ∑ k : Fin r, |L11 i k| * |A12 k j|

/-! Rounded triangular solves used in the `LDLᵀ` solution phase. -/

noncomputable def p29ForwardSubSteps (fp : P29FPModel) (n : ℕ)
    (L : P29Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ), k ≤ n → (Fin n → ℝ) → Fin n → ℝ
  | 0, _, x => x
  | k + 1, hk, x =>
      have hlt : n - k - 1 < n := by omega
      let ik : Fin n := ⟨n - k - 1, hlt⟩
      let count := n - k - 1
      let s := Fin.foldl count
        (fun acc (t : Fin count) =>
          fp.fl_sub acc
            (fp.fl_mul (L ik ⟨t.val, by omega⟩)
              (x ⟨t.val, by omega⟩)))
        (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (L ik ik))
      p29ForwardSubSteps fp n L b k (Nat.le_of_succ_le hk) x'

noncomputable def p29ForwardSub (fp : P29FPModel) (n : ℕ)
    (L : P29Matrix n n) (b : Fin n → ℝ) : Fin n → ℝ :=
  p29ForwardSubSteps fp n L b n (le_refl n) (fun _ => 0)

noncomputable def p29BackSubSteps (fp : P29FPModel) (n : ℕ)
    (U : P29Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ), k ≤ n → (Fin n → ℝ) → Fin n → ℝ
  | 0, _, x => x
  | k + 1, hk, x =>
      have hlt : k < n := hk
      let ik : Fin n := ⟨k, hlt⟩
      let count := n - k - 1
      let s := Fin.foldl count
        (fun acc (t : Fin count) =>
          fp.fl_sub acc
            (fp.fl_mul (U ik ⟨k + 1 + t.val, by omega⟩)
              (x ⟨k + 1 + t.val, by omega⟩)))
        (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (U ik ik))
      p29BackSubSteps fp n U b k (Nat.le_of_succ_le hk) x'

noncomputable def p29BackSub (fp : P29FPModel) (n : ℕ)
    (U : P29Matrix n n) (b : Fin n → ℝ) : Fin n → ℝ :=
  p29BackSubSteps fp n U b n (le_refl n) (fun _ => 0)

noncomputable def p29LDLT {n : ℕ}
    (L D : P29Matrix n n) : P29Matrix n n :=
  p29MatMul (p29MatMul L D) (p29Transpose L)

noncomputable def p29PerturbedLDLT {n : ℕ}
    (L D ΔL ΔD ΔU : P29Matrix n n) : P29Matrix n n :=
  p29MatMul (p29MatMul (L + ΔL) (D + ΔD)) (p29Transpose L + ΔU)

noncomputable def p29CombinedBackwardError {n : ℕ}
    (L D ΔL ΔD ΔU : P29Matrix n n) : P29Matrix n n :=
  p29PerturbedLDLT L D ΔL ΔD ΔU - p29LDLT L D

/-- The factorization perturbation plus the three solution-phase
perturbations in Appendix B. -/
noncomputable def p29TotalBackwardError {n : ℕ}
    (E0 : P29Matrix n n) (L D ΔL ΔD ΔU : P29Matrix n n) :
    P29Matrix n n :=
  E0 + p29CombinedBackwardError L D ΔL ΔD ΔU

/-- A normwise backward-stable solve with the one-by-one and two-by-two blocks
of `D`, matching the shared hypothesis in Appendix B. -/
def P29BlockSolveStable (n : ℕ)
    (D : P29Matrix n n) (y z : Fin n → ℝ) (eta : ℝ) : Prop :=
  ∃ ΔD : P29Matrix n n,
    p29EntryNorm ΔD ≤ eta * p29EntryNorm D ∧
    ∀ i, ∑ j : Fin n, (D i j + ΔD i j) * z j = y i

/-- An explicit `d'(n) ε` factor for the three perturbations in the Appendix-B
solution argument, using the entrywise-sum matrix norm. -/
noncomputable def p29SolveBackwardFactor (fp : P29FPModel) (n : ℕ)
    (eta : ℝ) (L D : P29Matrix n n) : ℝ :=
  (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
    p29EntryNorm (p29Transpose L) *
    (p29Gamma fp.u n * (1 + eta) * (1 + p29Gamma fp.u n) +
      eta * (1 + p29Gamma fp.u n) + p29Gamma fp.u n)

noncomputable def p29TotalBackwardBound (fp : P29FPModel) (n : ℕ)
    (eta factorEta : ℝ) (A L D : P29Matrix n n) : ℝ :=
  factorEta * p29EntryNorm A + p29SolveBackwardFactor fp n eta L D

end HighamBench
