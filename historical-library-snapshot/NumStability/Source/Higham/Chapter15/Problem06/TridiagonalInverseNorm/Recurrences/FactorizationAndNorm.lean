import NumStability.Source.Higham.Chapter15.Problem06.TridiagonalInverseNorm.Recurrences.EntryFormulas
import NumStability.Source.Higham.Chapter15.Problem06.TridiagonalInverseNorm.TridiagonalInverseCompletion

/-!
# FactorizationAndNorm

Canonical destination for the frozen declaration block of
`NumStability.Algorithms.LU.Higham15Problem15_6Closure`, routed by wave R02 of the August 2026 repository reorganization
completion phase. Declaration names, kinds, visibilities, signatures and
proofs are unchanged; only the module they live in has changed. Private
declarations keep their logical names and are re-mangled against this module,
exactly as recorded in the reviewed private normalization.
-/

/-!
# Higham15Problem15_6Closure (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.LU.Higham15Problem15_6Closure`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and
their users. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

namespace NumStability

namespace Higham15Problem15_6

open scoped BigOperators

open NumStability

theorem forward_column_scaled {n : ℕ} (hn : 0 < n)
    (T : TridiagData n) (A_inv : Fin n → Fin n → ℝ)
    (hIrred : IsIrreducibleTridiag T)
    (hRight : IsRightInverse n (tridiag_to_matrix T) A_inv) :
    ∀ i : Fin n,
      problem15_6_x T i * A_inv ⟨0, hn⟩ ⟨n - 1, by omega⟩ =
        A_inv i ⟨n - 1, by omega⟩ := by
  let first : Fin n := ⟨0, hn⟩
  let last : Fin n := ⟨n - 1, by omega⟩
  have hbyVal : ∀ t : ℕ, ∀ ht : t < n,
      forwardColumnNat T t * A_inv first last = A_inv ⟨t, ht⟩ last := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
        intro ht
        match t with
        | 0 => simp [forwardColumnNat, first]
        | 1 =>
            have hn2 : 1 < n := by omega
            let r : Fin n := ⟨0, hn⟩
            let one : Fin n := ⟨1, hn2⟩
            have hrlast : r ≠ last := by
              intro h
              have hv := congrArg Fin.val h
              simp [r, last] at hv
              omega
            have hact := tridiag_mulVec_entry T (fun k => A_inv k last) r
            rw [hRight r last] at hact
            simp [hrlast, r, one, hn2] at hact
            have hc : T.c r ≠ 0 := hIrred.2 r hn2
            have hfirst : r = first := by rfl
            have hone : (⟨r.val + 1, by simpa [r] using hn2⟩ : Fin n) = one := by
              apply Fin.ext
              rfl
            rw [hone] at hact
            have hfirst' : r = first := by rfl
            have hone' : (⟨1, ht⟩ : Fin n) = one := Fin.ext rfl
            have hd0 : diagAt T 0 = T.d r := by simp [diagAt, r, hn]
            have hc0 : superAt T 0 = T.c r := by simp [superAt, r, hn]
            simp only [forwardColumnNat]
            rw [hd0, hc0, hfirst', hone']
            rw [div_mul_eq_mul_div]
            apply (div_eq_iff hc).2
            ring_nf at hact ⊢
            linarith
        | k + 2 =>
            have hk : k < n := by omega
            have hk1 : k + 1 < n := by omega
            have hk2 : k + 2 < n := ht
            let prev : Fin n := ⟨k, hk⟩
            let r : Fin n := ⟨k + 1, hk1⟩
            let next : Fin n := ⟨k + 2, hk2⟩
            have hrlast : r ≠ last := by
              intro h
              have hv := congrArg Fin.val h
              simp [r, last] at hv
              omega
            have hact := tridiag_mulVec_entry T (fun q => A_inv q last) r
            rw [hRight r last] at hact
            simp [hrlast, r, hk1, hk2] at hact
            have hc : T.c r ≠ 0 := hIrred.2 r (by simp [r]; omega)
            change 0 = T.d r * A_inv r last + T.a r * A_inv prev last +
              T.c r * A_inv next last at hact
            have ih0 := ih k (by omega) hk
            have ih1 := ih (k + 1) (by omega) hk1
            have hd : diagAt T (k + 1) = T.d r := by
              simp [diagAt, r, hk1]
            have ha : subAt T (k + 1) = T.a r := by
              simp [subAt, r, hk1]
            have hcAt : superAt T (k + 1) = T.c r := by
              simp [superAt, r, hk1]
            have htarget : (⟨k + 2, ht⟩ : Fin n) = next := Fin.ext rfl
            have hnum :
                (T.a r * forwardColumnNat T k +
                    T.d r * forwardColumnNat T (k + 1)) * A_inv first last =
                  T.a r * A_inv prev last + T.d r * A_inv r last := by
              calc
                _ = T.a r * (forwardColumnNat T k * A_inv first last) +
                    T.d r * (forwardColumnNat T (k + 1) * A_inv first last) := by ring
                _ = _ := by
                  rw [ih0, ih1]
            simp only [forwardColumnNat]
            rw [ha, hd, hcAt, htarget, div_mul_eq_mul_div]
            apply (div_eq_iff hc).2
            rw [neg_mul, hnum]
            ring_nf at hact ⊢
            linarith
  intro i
  simpa [problem15_6_x, first, last] using hbyVal i.val i.isLt

theorem backward_row_scaled {n : ℕ} (hn : 0 < n)
    (T : TridiagData n) (A_inv : Fin n → Fin n → ℝ)
    (hIrred : IsIrreducibleTridiag T)
    (hRight : IsRightInverse n (tridiag_to_matrix T) A_inv) :
    ∀ i : Fin n,
      problem15_6_yBar T i * A_inv ⟨0, hn⟩ ⟨n - 1, by omega⟩ =
        A_inv ⟨0, hn⟩ i := by
  let first : Fin n := ⟨0, hn⟩
  let last : Fin n := ⟨n - 1, by omega⟩
  have hLeft : IsLeftInverse n (tridiag_to_matrix T) A_inv :=
    isLeftInverse_of_isRightInverse _ _ hRight
  have hbyDist : ∀ t : ℕ, ∀ ht : t < n,
      backwardRowNat T t * A_inv first last =
        A_inv first ⟨n - 1 - t, by omega⟩ := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
        intro ht
        match t with
        | 0 => simp [backwardRowNat, last]
        | 1 =>
            have hn2 : 1 < n := by omega
            let prev : Fin n := ⟨n - 2, by omega⟩
            have hfirstlast : first ≠ last := by
              intro h
              have hv := congrArg Fin.val h
              simp [first, last] at hv
              omega
            have hact := tridiag_vecMul_entry T (fun q => A_inv first q) last
            rw [hLeft first last] at hact
            have hlastnext : ¬ last.val + 1 < n := by simp [last]; omega
            simp [hfirstlast, hlastnext, last, hn2] at hact
            have hprev :
                (⟨n - 1 - 1, by omega⟩ : Fin n) = prev := by
              apply Fin.ext
              simp [prev]
              omega
            rw [hprev] at hact
            change 0 = T.d last * A_inv first last +
              T.c prev * A_inv first prev at hact
            have hd : diagAt T (n - 1) = T.d last := by
              simp [diagAt, last, hn]
            have hcAt : superAt T (n - 2) = T.c prev := by
              simp [superAt, prev, hn]
            have hc : T.c prev ≠ 0 := hIrred.2 prev (by simp [prev]; omega)
            have htarget : (⟨n - 1 - 1, by omega⟩ : Fin n) = prev := by
              apply Fin.ext
              simp [prev]
              omega
            simp only [backwardRowNat]
            rw [hd, hcAt, htarget, div_mul_eq_mul_div]
            apply (div_eq_iff hc).2
            ring_nf at hact ⊢
            linarith
        | k + 2 =>
            have hk : k < n := by omega
            have hk1 : k + 1 < n := by omega
            let target : Fin n := ⟨n - 1 - (k + 2), by omega⟩
            let col : Fin n := ⟨n - (k + 2), by omega⟩
            let next : Fin n := ⟨n - 1 - k, by omega⟩
            have hcolpos : 0 < col.val := by simp [col]; omega
            have hcolnext : col.val + 1 < n := by simp [col]; omega
            have hfirstcol : first ≠ col := by
              intro h
              have hv := congrArg Fin.val h
              simp [first, col] at hv
              omega
            have hact := tridiag_vecMul_entry T (fun q => A_inv first q) col
            rw [hLeft first col] at hact
            simp [hfirstcol, hcolpos, hcolnext] at hact
            have hprev :
                (⟨col.val - 1, by omega⟩ : Fin n) = target := by
              apply Fin.ext
              simp [col, target]
              omega
            have hnext :
                (⟨col.val + 1, by omega⟩ : Fin n) = next := by
              apply Fin.ext
              simp [col, next]
              omega
            rw [hprev, hnext] at hact
            change 0 = T.d col * A_inv first col +
                T.c target * A_inv first target +
                T.a next * A_inv first next at hact
            have ih0 := ih k (by omega) hk
            have ih1 := ih (k + 1) (by omega) hk1
            have hd : diagAt T (n - (k + 2)) = T.d col := by
              simp [diagAt, col, hn]
            have ha : subAt T (n - (k + 2) + 1) = T.a next := by
              unfold subAt
              rw [dif_pos (by omega)]
              congr 1
            have hcAt : superAt T (n - (k + 2) - 1) = T.c target := by
              unfold superAt
              rw [dif_pos (by omega)]
              congr 1
            have hc : T.c target ≠ 0 := hIrred.2 target (by simp [target]; omega)
            have htarget : (⟨n - 1 - (k + 2), by omega⟩ : Fin n) = target := rfl
            have hnum :
                (T.d col * backwardRowNat T (k + 1) +
                    T.a next * backwardRowNat T k) * A_inv first last =
                  T.d col * A_inv first col + T.a next * A_inv first next := by
              calc
                _ = T.d col * (backwardRowNat T (k + 1) * A_inv first last) +
                    T.a next * (backwardRowNat T k * A_inv first last) := by ring
                _ = _ := by
                  rw [ih1, ih0]
                  congr 2 <;> congr 1 <;> apply Fin.ext <;> simp [col, next] <;> omega
            simp only [backwardRowNat]
            rw [hd, ha, hcAt, htarget, div_mul_eq_mul_div]
            apply (div_eq_iff hc).2
            rw [neg_mul, hnum]
            ring_nf at hact ⊢
            linarith
  intro i
  have hres := hbyDist (n - 1 - i.val)
    (by omega : n - 1 - i.val < n)
  have hidx :
      (⟨n - 1 - (n - 1 - i.val), by omega⟩ : Fin n) = i := by
    apply Fin.ext
    simp only [Fin.val_mk]
    omega
  rw [hidx] at hres
  simpa [problem15_6_yBar, first, last] using hres

theorem yResidual_scaled {n : ℕ} (hn : 0 < n)
    (T : TridiagData n) (A_inv : Fin n → Fin n → ℝ)
    (hIrred : IsIrreducibleTridiag T)
    (hRight : IsRightInverse n (tridiag_to_matrix T) A_inv) :
    problem15_6_yResidual T * A_inv ⟨0, hn⟩ ⟨n - 1, by omega⟩ = 1 := by
  let first : Fin n := ⟨0, hn⟩
  let last : Fin n := ⟨n - 1, by omega⟩
  have hLeft : IsLeftInverse n (tridiag_to_matrix T) A_inv :=
    isLeftInverse_of_isRightInverse _ _ hRight
  by_cases hn1 : n = 1
  · subst n
    have hact := tridiag_vecMul_entry T (fun q => A_inv first q) first
    rw [hLeft first first] at hact
    simp [first] at hact
    simpa [problem15_6_yResidual, diagAt, subAt, backwardRowNat,
      first, last] using hact.symm
  · have hn2 : 1 < n := by omega
    let one : Fin n := ⟨1, hn2⟩
    have hact := tridiag_vecMul_entry T (fun q => A_inv first q) first
    rw [hLeft first first] at hact
    simp [first, hn2] at hact
    change 1 = T.d first * A_inv first first + T.a one * A_inv first one at hact
    have hs := backward_row_scaled hn T A_inv hIrred hRight
    have h0 := hs first
    have h1 := hs one
    change backwardRowNat T (n - 1) * A_inv first last =
      A_inv first first at h0
    change backwardRowNat T (n - 2) * A_inv first last =
      A_inv first one at h1
    have hd : diagAt T 0 = T.d first := by simp [diagAt, first, hn]
    have ha : subAt T 1 = T.a one := by simp [subAt, one, hn2]
    simp only [problem15_6_yResidual, dif_neg (by omega : n ≠ 0),
      dif_neg hn1]
    rw [hd, ha]
    calc
      (T.d first * backwardRowNat T (n - 1) +
          T.a one * backwardRowNat T (n - 2)) * A_inv first last =
          T.d first * (backwardRowNat T (n - 1) * A_inv first last) +
            T.a one * (backwardRowNat T (n - 2) * A_inv first last) := by ring
      _ = T.d first * A_inv first first + T.a one * A_inv first one := by
        rw [h0, h1]
      _ = 1 := hact.symm

theorem yResidual_ne {n : ℕ} (hn : 0 < n)
    (T : TridiagData n) (A_inv : Fin n → Fin n → ℝ)
    (hIrred : IsIrreducibleTridiag T)
    (hRight : IsRightInverse n (tridiag_to_matrix T) A_inv) :
    problem15_6_yResidual T ≠ 0 := by
  intro hz
  have hs := yResidual_scaled hn T A_inv hIrred hRight
  rw [hz, zero_mul] at hs
  norm_num at hs

theorem y_correct {n : ℕ} (hn : 0 < n)
    (T : TridiagData n) (A_inv : Fin n → Fin n → ℝ)
    (hIrred : IsIrreducibleTridiag T)
    (hRight : IsRightInverse n (tridiag_to_matrix T) A_inv) :
    ∀ i : Fin n, problem15_6_y T i = A_inv ⟨0, hn⟩ i := by
  let first : Fin n := ⟨0, hn⟩
  let last : Fin n := ⟨n - 1, by omega⟩
  have hs := backward_row_scaled hn T A_inv hIrred hRight
  have hr := yResidual_scaled hn T A_inv hIrred hRight
  have hrne := yResidual_ne hn T A_inv hIrred hRight
  intro i
  have hi := hs i
  apply (div_eq_iff hrne).2
  change problem15_6_yBar T i = A_inv first i * problem15_6_yResidual T
  calc
    problem15_6_yBar T i = problem15_6_yBar T i * 1 := by ring
    _ = problem15_6_yBar T i *
        (problem15_6_yResidual T * A_inv first last) := by rw [hr]
    _ = problem15_6_yResidual T *
        (problem15_6_yBar T i * A_inv first last) := by ring
    _ = problem15_6_yResidual T * A_inv first i := by rw [hi]
    _ = A_inv first i * problem15_6_yResidual T := by ring

theorem x_correct {n : ℕ} (hn : 0 < n)
    (T : TridiagData n) (A_inv : Fin n → Fin n → ℝ)
    (hIrred : IsIrreducibleTridiag T)
    (hRight : IsRightInverse n (tridiag_to_matrix T) A_inv) :
    ∀ i : Fin n,
      problem15_6_x T i =
        A_inv i ⟨n - 1, by omega⟩ / A_inv ⟨0, hn⟩ ⟨n - 1, by omega⟩ := by
  have hr := yResidual_scaled hn T A_inv hIrred hRight
  have hc : A_inv ⟨0, hn⟩ ⟨n - 1, by omega⟩ ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hr
    norm_num at hr
  have hs := forward_column_scaled hn T A_inv hIrred hRight
  intro i
  exact (eq_div_iff hc).2 (hs i)

theorem upper_factorization {n : ℕ} (hn : 0 < n)
    (T : TridiagData n) (A_inv : Fin n → Fin n → ℝ)
    (hIrred : IsIrreducibleTridiag T)
    (hRight : IsRightInverse n (tridiag_to_matrix T) A_inv) :
    ∀ i j : Fin n, i.val ≤ j.val →
      A_inv i j = problem15_6_x T i * problem15_6_y T j := by
  let first : Fin n := ⟨0, hn⟩
  let last : Fin n := ⟨n - 1, by omega⟩
  have hr := yResidual_scaled hn T A_inv hIrred hRight
  have hc : A_inv first last ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hr
    norm_num at hr
  have hxs := forward_column_scaled hn T A_inv hIrred hRight
  have hy := y_correct hn T A_inv hIrred hRight
  obtain ⟨xu, yu, pl, ql, hu, hl⟩ :=
    NumStability.Ch15IkebeClosure.H15_Theorem15_9_of_irreducible_rightInverse
      hn T A_inv hIrred hRight
  intro i j hij
  have hcross :
      A_inv i j * A_inv first last = A_inv i last * A_inv first j := by
    rw [hu i j hij, hu i last (by simp [last]; omega),
      hu first j (by simp [first]), hu first last (by simp [first])]
    ring
  apply mul_right_cancel₀ hc
  calc
    A_inv i j * A_inv first last = A_inv i last * A_inv first j := hcross
    _ = (problem15_6_x T i * A_inv first last) *
        problem15_6_y T j := by rw [hxs i, hy j]
    _ = (problem15_6_x T i * problem15_6_y T j) *
        A_inv first last := by ring

theorem backward_column_scaled {n : ℕ} (hn : 0 < n)
    (T : TridiagData n) (A_inv : Fin n → Fin n → ℝ)
    (hIrred : IsIrreducibleTridiag T)
    (hRight : IsRightInverse n (tridiag_to_matrix T) A_inv) :
    ∀ i : Fin n,
      problem15_6_p T i * A_inv ⟨n - 1, by omega⟩ ⟨0, hn⟩ =
        A_inv i ⟨0, hn⟩ := by
  let first : Fin n := ⟨0, hn⟩
  let last : Fin n := ⟨n - 1, by omega⟩
  have hbyDist : ∀ t : ℕ, ∀ ht : t < n,
      backwardColumnNat T t * A_inv last first =
        A_inv ⟨n - 1 - t, by omega⟩ first := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
        intro ht
        match t with
        | 0 => simp [backwardColumnNat, last]
        | 1 =>
            have hn2 : 1 < n := by omega
            let prev : Fin n := ⟨n - 2, by omega⟩
            have hlastfirst : last ≠ first := by
              intro h
              have hv := congrArg Fin.val h
              simp [first, last] at hv
              omega
            have hact := tridiag_mulVec_entry T (fun q => A_inv q first) last
            rw [hRight last first] at hact
            have hlastnext : ¬ last.val + 1 < n := by simp [last]; omega
            simp [hlastfirst, hlastnext, last, hn2] at hact
            have hprev :
                (⟨n - 1 - 1, by omega⟩ : Fin n) = prev := by
              apply Fin.ext
              simp [prev]
              omega
            rw [hprev] at hact
            change 0 = T.d last * A_inv last first +
              T.a last * A_inv prev first at hact
            have hd : diagAt T (n - 1) = T.d last := by
              simp [diagAt, last, hn]
            have haAt : subAt T (n - 1) = T.a last := by
              simp [subAt, last, hn]
            have ha : T.a last ≠ 0 := by
              have hs := hIrred.1 prev (by simp [prev]; omega)
              have he :
                  (⟨prev.val + 1, by simp [prev]; omega⟩ : Fin n) = last := by
                apply Fin.ext
                simp [prev, last]
                omega
              rwa [he] at hs
            have htarget : (⟨n - 1 - 1, by omega⟩ : Fin n) = prev := hprev
            simp only [backwardColumnNat]
            rw [hd, haAt, htarget, div_mul_eq_mul_div]
            apply (div_eq_iff ha).2
            ring_nf at hact ⊢
            linarith
        | k + 2 =>
            have hk : k < n := by omega
            have hk1 : k + 1 < n := by omega
            let target : Fin n := ⟨n - 1 - (k + 2), by omega⟩
            let col : Fin n := ⟨n - (k + 2), by omega⟩
            let next : Fin n := ⟨n - 1 - k, by omega⟩
            have hcolpos : 0 < col.val := by simp [col]; omega
            have hcolnext : col.val + 1 < n := by simp [col]; omega
            have hcolfirst : col ≠ first := by
              intro h
              have hv := congrArg Fin.val h
              simp [first, col] at hv
              omega
            have hact := tridiag_mulVec_entry T (fun q => A_inv q first) col
            rw [hRight col first] at hact
            simp [hcolfirst, hcolpos, hcolnext] at hact
            have hprev :
                (⟨col.val - 1, by omega⟩ : Fin n) = target := by
              apply Fin.ext
              simp [col, target]
              omega
            have hnext :
                (⟨col.val + 1, by omega⟩ : Fin n) = next := by
              apply Fin.ext
              simp [col, next]
              omega
            rw [hprev, hnext] at hact
            change 0 = T.d col * A_inv col first +
                T.a col * A_inv target first +
                T.c col * A_inv next first at hact
            have ih0 := ih k (by omega) hk
            have ih1 := ih (k + 1) (by omega) hk1
            have hd : diagAt T (n - (k + 2)) = T.d col := by
              simp [diagAt, col, hn]
            have hcAt : superAt T (n - (k + 2)) = T.c col := by
              simp [superAt, col, hn]
            have haAt : subAt T (n - (k + 2)) = T.a col := by
              simp [subAt, col, hn]
            have ha : T.a col ≠ 0 := by
              have hs := hIrred.1 target (by simp [target]; omega)
              have he :
                  (⟨target.val + 1, by simp [target]; omega⟩ : Fin n) = col := by
                apply Fin.ext
                simp [target, col]
                omega
              rwa [he] at hs
            have htarget : (⟨n - 1 - (k + 2), by omega⟩ : Fin n) = target := rfl
            have hnum :
                (T.d col * backwardColumnNat T (k + 1) +
                    T.c col * backwardColumnNat T k) * A_inv last first =
                  T.d col * A_inv col first + T.c col * A_inv next first := by
              calc
                _ = T.d col * (backwardColumnNat T (k + 1) * A_inv last first) +
                    T.c col * (backwardColumnNat T k * A_inv last first) := by ring
                _ = _ := by
                  rw [ih1, ih0]
                  congr 2 <;> congr 1 <;> apply Fin.ext <;> simp [col] <;> omega
            simp only [backwardColumnNat]
            rw [hd, hcAt, haAt, htarget, div_mul_eq_mul_div]
            apply (div_eq_iff ha).2
            rw [neg_mul, hnum]
            ring_nf at hact ⊢
            linarith
  intro i
  have hres := hbyDist (n - 1 - i.val)
    (by omega : n - 1 - i.val < n)
  have hidx :
      (⟨n - 1 - (n - 1 - i.val), by omega⟩ : Fin n) = i := by
    apply Fin.ext
    simp only [Fin.val_mk]
    omega
  rw [hidx] at hres
  simpa [problem15_6_p, first, last] using hres

theorem forward_row_scaled {n : ℕ} (hn : 0 < n)
    (T : TridiagData n) (A_inv : Fin n → Fin n → ℝ)
    (hIrred : IsIrreducibleTridiag T)
    (hRight : IsRightInverse n (tridiag_to_matrix T) A_inv) :
    ∀ j : Fin n,
      problem15_6_qBar T j * A_inv ⟨n - 1, by omega⟩ ⟨0, hn⟩ =
        A_inv ⟨n - 1, by omega⟩ j := by
  let first : Fin n := ⟨0, hn⟩
  let last : Fin n := ⟨n - 1, by omega⟩
  have hLeft : IsLeftInverse n (tridiag_to_matrix T) A_inv :=
    isLeftInverse_of_isRightInverse _ _ hRight
  have hbyVal : ∀ t : ℕ, ∀ ht : t < n,
      forwardRowNat T t * A_inv last first = A_inv last ⟨t, ht⟩ := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
        intro ht
        match t with
        | 0 => simp [forwardRowNat, first]
        | 1 =>
            have hn2 : 1 < n := by omega
            let one : Fin n := ⟨1, hn2⟩
            have hlastfirst : last ≠ first := by
              intro h
              have hv := congrArg Fin.val h
              simp [last, first] at hv
              omega
            have hact := tridiag_vecMul_entry T (fun q => A_inv last q) first
            rw [hLeft last first] at hact
            simp [hlastfirst, first, one, hn2] at hact
            change 0 = T.d first * A_inv last first +
              T.a one * A_inv last one at hact
            have hd : diagAt T 0 = T.d first := by simp [diagAt, first, hn]
            have haAt : subAt T 1 = T.a one := by simp [subAt, one, hn2]
            have ha : T.a one ≠ 0 := by
              have hs := hIrred.1 first hn2
              have he :
                  (⟨first.val + 1, hn2⟩ : Fin n) = one := Fin.ext rfl
              rwa [he] at hs
            have hone : (⟨1, ht⟩ : Fin n) = one := Fin.ext rfl
            simp only [forwardRowNat]
            rw [hd, haAt, hone, div_mul_eq_mul_div]
            apply (div_eq_iff ha).2
            ring_nf at hact ⊢
            linarith
        | k + 2 =>
            have hk : k < n := by omega
            have hk1 : k + 1 < n := by omega
            let prev : Fin n := ⟨k, hk⟩
            let col : Fin n := ⟨k + 1, hk1⟩
            let next : Fin n := ⟨k + 2, ht⟩
            have hcollast : col ≠ last := by
              intro h
              have hv := congrArg Fin.val h
              simp [col, last] at hv
              omega
            have hcolpos : 0 < col.val := by simp [col]
            have hcolnext : col.val + 1 < n := by simp [col]; omega
            have hact := tridiag_vecMul_entry T (fun q => A_inv last q) col
            rw [hLeft last col] at hact
            simp [Ne.symm hcollast, hcolpos, hcolnext] at hact
            have hprev :
                (⟨col.val - 1, by omega⟩ : Fin n) = prev := by
              apply Fin.ext
              simp [col, prev]
            have hnext :
                (⟨col.val + 1, by omega⟩ : Fin n) = next := by
              apply Fin.ext
              simp [col, next]
            rw [hprev, hnext] at hact
            change 0 = T.d col * A_inv last col +
                T.c prev * A_inv last prev +
                T.a next * A_inv last next at hact
            have ih0 := ih k (by omega) hk
            have ih1 := ih (k + 1) (by omega) hk1
            have hcAt : superAt T k = T.c prev := by
              simp [superAt, prev, hk]
            have hd : diagAt T (k + 1) = T.d col := by
              simp [diagAt, col, hk1]
            have haAt : subAt T (k + 2) = T.a next := by
              simp [subAt, next, ht]
            have ha : T.a next ≠ 0 := by
              have hs := hIrred.1 col hcolnext
              have he :
                  (⟨col.val + 1, hcolnext⟩ : Fin n) = next := hnext
              rwa [he] at hs
            have htarget : (⟨k + 2, ht⟩ : Fin n) = next := rfl
            have hnum :
                (T.c prev * forwardRowNat T k +
                    T.d col * forwardRowNat T (k + 1)) * A_inv last first =
                  T.c prev * A_inv last prev + T.d col * A_inv last col := by
              calc
                _ = T.c prev * (forwardRowNat T k * A_inv last first) +
                    T.d col * (forwardRowNat T (k + 1) * A_inv last first) := by ring
                _ = _ := by rw [ih0, ih1]
            simp only [forwardRowNat]
            rw [hcAt, hd, haAt, htarget, div_mul_eq_mul_div]
            apply (div_eq_iff ha).2
            rw [neg_mul, hnum]
            ring_nf at hact ⊢
            linarith
  intro j
  simpa [problem15_6_qBar, first, last] using hbyVal j.val j.isLt

theorem qResidual_scaled {n : ℕ} (hn : 0 < n)
    (T : TridiagData n) (A_inv : Fin n → Fin n → ℝ)
    (hIrred : IsIrreducibleTridiag T)
    (hRight : IsRightInverse n (tridiag_to_matrix T) A_inv) :
    problem15_6_qResidual T * A_inv ⟨n - 1, by omega⟩ ⟨0, hn⟩ = 1 := by
  let first : Fin n := ⟨0, hn⟩
  let last : Fin n := ⟨n - 1, by omega⟩
  have hLeft : IsLeftInverse n (tridiag_to_matrix T) A_inv :=
    isLeftInverse_of_isRightInverse _ _ hRight
  by_cases hn1 : n = 1
  · subst n
    have hact := tridiag_vecMul_entry T (fun q => A_inv last q) last
    rw [hLeft last last] at hact
    simp [last] at hact
    simpa [problem15_6_qResidual, superAt, diagAt, forwardRowNat,
      first, last] using hact.symm
  · have hn2 : 1 < n := by omega
    let prev : Fin n := ⟨n - 2, by omega⟩
    have hact := tridiag_vecMul_entry T (fun q => A_inv last q) last
    rw [hLeft last last] at hact
    have hlastnext : ¬ last.val + 1 < n := by simp [last]; omega
    simp [last, hlastnext, hn2] at hact
    have hprev :
        (⟨n - 1 - 1, by omega⟩ : Fin n) = prev := by
      apply Fin.ext
      simp [prev]
      omega
    rw [hprev] at hact
    change 1 = T.d last * A_inv last last + T.c prev * A_inv last prev at hact
    have hs := forward_row_scaled hn T A_inv hIrred hRight
    have hp := hs prev
    have hl := hs last
    change forwardRowNat T (n - 2) * A_inv last first =
      A_inv last prev at hp
    change forwardRowNat T (n - 1) * A_inv last first =
      A_inv last last at hl
    have hc : superAt T (n - 2) = T.c prev := by
      simp [superAt, prev, hn]
    have hd : diagAt T (n - 1) = T.d last := by
      simp [diagAt, last, hn]
    simp only [problem15_6_qResidual, dif_neg (by omega : n ≠ 0),
      dif_neg hn1]
    rw [hc, hd]
    calc
      (T.c prev * forwardRowNat T (n - 2) +
          T.d last * forwardRowNat T (n - 1)) * A_inv last first =
          T.c prev * (forwardRowNat T (n - 2) * A_inv last first) +
            T.d last * (forwardRowNat T (n - 1) * A_inv last first) := by ring
      _ = T.c prev * A_inv last prev + T.d last * A_inv last last := by
        rw [hp, hl]
      _ = 1 := by linarith

theorem qResidual_ne {n : ℕ} (hn : 0 < n)
    (T : TridiagData n) (A_inv : Fin n → Fin n → ℝ)
    (hIrred : IsIrreducibleTridiag T)
    (hRight : IsRightInverse n (tridiag_to_matrix T) A_inv) :
    problem15_6_qResidual T ≠ 0 := by
  intro hz
  have hs := qResidual_scaled hn T A_inv hIrred hRight
  rw [hz, zero_mul] at hs
  norm_num at hs

theorem q_correct {n : ℕ} (hn : 0 < n)
    (T : TridiagData n) (A_inv : Fin n → Fin n → ℝ)
    (hIrred : IsIrreducibleTridiag T)
    (hRight : IsRightInverse n (tridiag_to_matrix T) A_inv) :
    ∀ j : Fin n, problem15_6_q T j = A_inv ⟨n - 1, by omega⟩ j := by
  let first : Fin n := ⟨0, hn⟩
  let last : Fin n := ⟨n - 1, by omega⟩
  have hs := forward_row_scaled hn T A_inv hIrred hRight
  have hr := qResidual_scaled hn T A_inv hIrred hRight
  have hrne := qResidual_ne hn T A_inv hIrred hRight
  intro j
  have hj := hs j
  apply (div_eq_iff hrne).2
  change problem15_6_qBar T j = A_inv last j * problem15_6_qResidual T
  calc
    problem15_6_qBar T j = problem15_6_qBar T j * 1 := by ring
    _ = problem15_6_qBar T j *
        (problem15_6_qResidual T * A_inv last first) := by rw [hr]
    _ = problem15_6_qResidual T *
        (problem15_6_qBar T j * A_inv last first) := by ring
    _ = problem15_6_qResidual T * A_inv last j := by rw [hj]
    _ = A_inv last j * problem15_6_qResidual T := by ring

theorem p_correct {n : ℕ} (hn : 0 < n)
    (T : TridiagData n) (A_inv : Fin n → Fin n → ℝ)
    (hIrred : IsIrreducibleTridiag T)
    (hRight : IsRightInverse n (tridiag_to_matrix T) A_inv) :
    ∀ i : Fin n,
      problem15_6_p T i =
        A_inv i ⟨0, hn⟩ / A_inv ⟨n - 1, by omega⟩ ⟨0, hn⟩ := by
  have hr := qResidual_scaled hn T A_inv hIrred hRight
  have hc : A_inv ⟨n - 1, by omega⟩ ⟨0, hn⟩ ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hr
    norm_num at hr
  have hs := backward_column_scaled hn T A_inv hIrred hRight
  intro i
  exact (eq_div_iff hc).2 (hs i)

theorem lower_factorization {n : ℕ} (hn : 0 < n)
    (T : TridiagData n) (A_inv : Fin n → Fin n → ℝ)
    (hIrred : IsIrreducibleTridiag T)
    (hRight : IsRightInverse n (tridiag_to_matrix T) A_inv) :
    ∀ i j : Fin n, j.val ≤ i.val →
      A_inv i j = problem15_6_p T i * problem15_6_q T j := by
  let first : Fin n := ⟨0, hn⟩
  let last : Fin n := ⟨n - 1, by omega⟩
  have hr := qResidual_scaled hn T A_inv hIrred hRight
  have hc : A_inv last first ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hr
    norm_num at hr
  have hps := backward_column_scaled hn T A_inv hIrred hRight
  have hq := q_correct hn T A_inv hIrred hRight
  obtain ⟨xu, yu, pl, ql, hu, hl⟩ :=
    NumStability.Ch15IkebeClosure.H15_Theorem15_9_of_irreducible_rightInverse
      hn T A_inv hIrred hRight
  intro i j hji
  have hcross :
      A_inv i j * A_inv last first = A_inv i first * A_inv last j := by
    rw [hl i j hji, hl i first (by simp [first]),
      hl last j (by simp [last]; omega), hl last first (by simp [first])]
    ring
  apply mul_right_cancel₀ hc
  calc
    A_inv i j * A_inv last first = A_inv i first * A_inv last j := hcross
    _ = (problem15_6_p T i * A_inv last first) *
        problem15_6_q T j := by rw [hps i, hq j]
    _ = (problem15_6_p T i * problem15_6_q T j) *
        A_inv last first := by ring

theorem absInvMul_correct {n : ℕ} (hn : 0 < n)
    (T : TridiagData n) (A_inv : Fin n → Fin n → ℝ)
    (hIrred : IsIrreducibleTridiag T)
    (hRight : IsRightInverse n (tridiag_to_matrix T) A_inv)
    (d : Fin n → ℝ) :
    ∀ i : Fin n, problem15_6_absInvMul T d i =
      ∑ j : Fin n, |A_inv i j| * d j := by
  have hu := upper_factorization hn T A_inv hIrred hRight
  have hl := lower_factorization hn T A_inv hIrred hRight
  intro i
  let lw : ℕ → ℝ := problem15_6_lowerWeight T d
  let uw : ℕ → ℝ := problem15_6_upperWeight T d
  have hsplit := prefix_suffix_scan_split
    (fun k => |problem15_6_p T i| * lw k)
    (fun k => |problem15_6_x T i| * uw k)
    (n := n) (i := i.val) (Nat.le_of_lt i.isLt)
  have hpre := prefixScanNat_const_mul
    |problem15_6_p T i| lw i.val
  have hsuf := reverseSuffixScanNat_const_mul
    |problem15_6_x T i| uw n (n - i.val)
  have hentries :
      (∑ k ∈ Finset.range n,
        if k < i.val then |problem15_6_p T i| * lw k
        else |problem15_6_x T i| * uw k) =
      ∑ k ∈ Finset.range n,
        |finVectorAt (A_inv i) k| * finVectorAt d k := by
    apply Finset.sum_congr rfl
    intro k hkmem
    have hk : k < n := Finset.mem_range.mp hkmem
    let j : Fin n := ⟨k, hk⟩
    by_cases hki : k < i.val
    · rw [if_pos hki]
      have hfac := hl i j (by simp [j]; omega)
      simp only [lw, problem15_6_lowerWeight]
      simp [finVectorAt, hk, j]
      rw [hfac, abs_mul]
      ring
    · rw [if_neg hki]
      have hfac := hu i j (by simp [j]; omega)
      simp only [uw, problem15_6_upperWeight]
      simp [finVectorAt, hk, j]
      rw [hfac, abs_mul]
      ring
  have hfin := Fin.sum_univ_eq_sum_range
    (fun k : ℕ => |finVectorAt (A_inv i) k| * finVectorAt d k) n
  calc
    problem15_6_absInvMul T d i =
        prefixScanNat (fun k => |problem15_6_p T i| * lw k) i.val +
          reverseSuffixScanNat (fun k => |problem15_6_x T i| * uw k)
            n (n - i.val) := by
              simp only [problem15_6_absInvMul, lw, uw]
              rw [hpre, hsuf]
    _ = ∑ k ∈ Finset.range n,
          if k < i.val then |problem15_6_p T i| * lw k
          else |problem15_6_x T i| * uw k := hsplit
    _ = ∑ k ∈ Finset.range n,
          |finVectorAt (A_inv i) k| * finVectorAt d k := hentries
    _ = ∑ j : Fin n, |A_inv i j| * d j := by
      simpa [finVectorAt] using hfin.symm

theorem infNorm_correct {n : ℕ} (hn : 0 < n)
    (T : TridiagData n) (A_inv : Fin n → Fin n → ℝ)
    (hIrred : IsIrreducibleTridiag T)
    (hRight : IsRightInverse n (tridiag_to_matrix T) A_inv)
    (d : Fin n → ℝ) :
    problem15_6_infNorm T d =
      infNormVec (fun i => ∑ j : Fin n, |A_inv i j| * d j) := by
  unfold problem15_6_infNorm
  apply congrArg infNormVec
  funext i
  exact absInvMul_correct hn T A_inv hIrred hRight d i

/-- **Higham Problem 15.6, source-hypothesis closure.**

For the actual inverse of a nonempty nonsingular irreducible tridiagonal
matrix, the literal forward/backward scalar recurrences produce Higham's
upper-triangle factors `x` and `y`.  The two scan recurrences then compute
`|A⁻¹|d` and its infinity norm exactly for every `d ≥ 0`.  The same endpoint
records both the exact nontrivial-dimension scalar-operation count and its
uniform linear bound.

No inverse-entry formula, recurrence correctness, rank-one conclusion, or
complexity conclusion is supplied as a premise. -/
theorem H15_Problem15_6_of_irreducible_rightInverse {n : ℕ} (hn : 0 < n)
    (T : TridiagData n) (A_inv : Fin n → Fin n → ℝ)
    (hIrred : IsIrreducibleTridiag T)
    (hRight : IsRightInverse n (tridiag_to_matrix T) A_inv)
    (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) :
    (∀ i : Fin n,
      problem15_6_x T i =
        A_inv i ⟨n - 1, by omega⟩ /
          A_inv ⟨0, hn⟩ ⟨n - 1, by omega⟩) ∧
    (∀ j : Fin n, problem15_6_y T j = A_inv ⟨0, hn⟩ j) ∧
    (∀ i : Fin n, problem15_6_absInvMul T d i =
      ∑ j : Fin n, |A_inv i j| * d j) ∧
    (∀ i : Fin n, 0 ≤ problem15_6_absInvMul T d i) ∧
    problem15_6_infNorm T d =
      infNormVec (fun i => ∑ j : Fin n, |A_inv i j| * d j) ∧
    (2 ≤ n → problem15_6_scalarOps n = 29 * n - 26) ∧
    problem15_6_scalarOps n ≤ 29 * n := by
  have hx := x_correct hn T A_inv hIrred hRight
  have hy := y_correct hn T A_inv hIrred hRight
  have hz := absInvMul_correct hn T A_inv hIrred hRight d
  have hznn : ∀ i : Fin n, 0 ≤ problem15_6_absInvMul T d i := by
    intro i
    rw [hz i]
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (hd j))
  exact ⟨hx, hy, hz, hznn,
    infNorm_correct hn T A_inv hIrred hRight d,
    fun hn2 => problem15_6_scalarOps_exact hn2,
    problem15_6_scalarOps_linear n⟩

end Higham15Problem15_6
end NumStability
