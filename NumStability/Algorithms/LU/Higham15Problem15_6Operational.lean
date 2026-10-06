-- Algorithms/LU/Higham15Problem15_6Operational.lean
--
-- Literal stored-vector implementation of Higham Problem 15.6.  The factor
-- recurrences are materialized, the two cumulative passes use Vector.scanl,
-- and row assembly uses Vector.map₂.

import NumStability.Algorithms.LU.Higham15Problem15_6Closure
import Batteries.Data.Array.Scan
import Mathlib.Data.Vector.Basic


namespace NumStability.Higham15Problem15_6

open NumStability

noncomputable section

def scanStatesOperational (w : ℕ → ℝ) (n : ℕ) : Array ℝ :=
  (Array.ofFn (fun i : Fin n => w i.val)).scanl (· + ·) 0

theorem scanStatesOperational_size (w : ℕ → ℝ) (n : ℕ) :
    (scanStatesOperational w n).size = n + 1 := by
  simpa [scanStatesOperational] using
    Array.size_scanl 0 (Array.ofFn (fun i : Fin n => w i.val))

theorem scanStatesOperational_get (w : ℕ → ℝ) (n : ℕ) :
    ∀ (i : ℕ) (hi : i ≤ n),
      (scanStatesOperational w n)[i]'(by rw [scanStatesOperational_size]; omega) =
        prefixScanNat w i := by
  intro i
  induction i with
  | zero =>
      intro hi
      unfold scanStatesOperational
      rw [Array.getElem_scanl_zero]
      simp [prefixScanNat]
  | succ i ih =>
      intro hi
      have hin : i < n := by omega
      unfold scanStatesOperational
      rw [Array.getElem_succ_scanl (i := i)]
      change (scanStatesOperational w n)[i]'(by rw [scanStatesOperational_size]; omega) +
        (Array.ofFn (fun j : Fin n => w j.val))[i]'(by simpa using hin) = _
      rw [ih (by omega), Array.getElem_ofFn]
      rfl

theorem prefixReverseOperational_eq_suffix (w : ℕ → ℝ) (n : ℕ) : ∀ k : ℕ,
    prefixScanNat (fun r => w (n - 1 - r)) k =
      reverseSuffixScanNat w n k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [prefixScanNat, reverseSuffixScanNat]
      rw [ih]

structure WorkspaceOperational (n : ℕ) where
  lower : Array ℝ
  upper : Array ℝ
  lower_size : lower.size = n + 1
  upper_size : upper.size = n + 1

def workspaceOperational (lw uw : ℕ → ℝ) (n : ℕ) : WorkspaceOperational (n := n) where
  lower := scanStatesOperational lw n
  upper := scanStatesOperational (fun r => uw (n - 1 - r)) n
  lower_size := scanStatesOperational_size lw n
  upper_size := scanStatesOperational_size _ n

def rowArrayOperational {n : ℕ} (p x : Fin n → ℝ) (lw uw : ℕ → ℝ) : Array ℝ :=
  let ws := workspaceOperational lw uw n
  Array.ofFn fun i : Fin n =>
    |p i| * ws.lower[i.val]'(by rw [ws.lower_size]; omega) +
      |x i| * ws.upper[n - i.val]'(by rw [ws.upper_size]; omega)

theorem rowArrayOperational_size {n : ℕ} (p x : Fin n → ℝ) (lw uw : ℕ → ℝ) :
    (rowArrayOperational p x lw uw).size = n := by
  simp [rowArrayOperational]

theorem rowArrayOperational_get {n : ℕ} (p x : Fin n → ℝ) (lw uw : ℕ → ℝ)
    (i : Fin n) :
    (rowArrayOperational p x lw uw)[i.val]'(by rw [rowArrayOperational_size]; exact i.isLt) =
      |p i| * prefixScanNat lw i.val +
        |x i| * reverseSuffixScanNat uw n (n - i.val) := by
  unfold rowArrayOperational
  rw [Array.getElem_ofFn]
  simp only [workspaceOperational]
  rw [scanStatesOperational_get lw n i.val (Nat.le_of_lt i.isLt)]
  rw [scanStatesOperational_get (fun r => uw (n - 1 - r)) n (n - i.val) (by omega)]
  rw [prefixReverseOperational_eq_suffix]

def twoStepStateArrayOperational (m : ℕ) (s₀ s₁ : ℝ)
    (step : ℕ → ℝ → ℝ → ℝ) : Array (ℝ × ℝ) :=
  (Array.ofFn (fun k : Fin m => k.val)).scanl
    (fun state k => (state.2, step k state.1 state.2)) (s₀, s₁)

theorem twoStepStateArrayOperational_size (m : ℕ) (s₀ s₁ : ℝ)
    (step : ℕ → ℝ → ℝ → ℝ) :
    (twoStepStateArrayOperational m s₀ s₁ step).size = m + 1 := by
  simpa [twoStepStateArrayOperational] using
    Array.size_scanl (s₀, s₁) (Array.ofFn (fun k : Fin m => k.val))

theorem twoStepStateArrayOperational_get_of_recurrence
    (f : ℕ → ℝ) (s₀ s₁ : ℝ) (step : ℕ → ℝ → ℝ → ℝ)
    (h₀ : f 0 = s₀) (h₁ : f 1 = s₁)
    (hstep : ∀ k, f (k + 2) = step k (f k) (f (k + 1)))
    (m : ℕ) : ∀ (i : ℕ) (hi : i ≤ m),
    (twoStepStateArrayOperational m s₀ s₁ step)[i]'(by
      rw [twoStepStateArrayOperational_size]; omega) = (f i, f (i + 1)) := by
  intro i
  induction i with
  | zero =>
      intro hi
      unfold twoStepStateArrayOperational
      rw [Array.getElem_scanl_zero]
      simp [h₀, h₁]
  | succ i ih =>
      intro hi
      have him : i < m := by omega
      unfold twoStepStateArrayOperational
      rw [Array.getElem_succ_scanl (i := i)]
      have ih' := ih (by omega)
      unfold twoStepStateArrayOperational at ih'
      rw [ih', Array.getElem_ofFn]
      simp only
      congr 1
      rw [← hstep i]

def twoStepArrayOperational (n : ℕ) (s₀ s₁ : ℝ)
    (step : ℕ → ℝ → ℝ → ℝ) : Array ℝ :=
  if h₀ : n = 0 then #[]
  else if h₁ : n = 1 then #[s₀]
  else
    let states := twoStepStateArrayOperational (n - 2) s₀ s₁ step
    Array.ofFn fun i : Fin n =>
      if hi : i.val = 0 then s₀
      else (states[i.val - 1]'(by
        rw [twoStepStateArrayOperational_size]
        omega)).2

theorem twoStepArrayOperational_size (n : ℕ) (s₀ s₁ : ℝ)
    (step : ℕ → ℝ → ℝ → ℝ) :
    (twoStepArrayOperational n s₀ s₁ step).size = n := by
  unfold twoStepArrayOperational
  split_ifs with h₀ h₁
  · subst n
    rfl
  · subst n
    rfl
  · simp

theorem twoStepArrayOperational_get_of_recurrence
    (f : ℕ → ℝ) (s₀ s₁ : ℝ) (step : ℕ → ℝ → ℝ → ℝ)
    (h₀ : f 0 = s₀) (h₁ : f 1 = s₁)
    (hstep : ∀ k, f (k + 2) = step k (f k) (f (k + 1)))
    {n : ℕ} (i : Fin n) :
    (twoStepArrayOperational n s₀ s₁ step)[i.val]'(by
      rw [twoStepArrayOperational_size]; exact i.isLt) = f i.val := by
  unfold twoStepArrayOperational
  split_ifs with hn0 hn1
  · subst n
    exact i.elim0
  · subst n
    have hi0 : i = 0 := Fin.eq_zero _
    subst i
    simpa using h₀.symm
  · rw [Array.getElem_ofFn]
    by_cases hi0 : i.val = 0
    · rw [dif_pos hi0]
      simpa [hi0] using h₀.symm
    · rw [dif_neg hi0]
      have hle : i.val - 1 ≤ n - 2 := by omega
      have hs := twoStepStateArrayOperational_get_of_recurrence
        f s₀ s₁ step h₀ h₁ hstep (n - 2) (i.val - 1) hle
      rw [hs]
      change f (i.val - 1 + 1) = f i.val
      congr 1
      exact Nat.sub_add_cancel (by omega : 1 ≤ i.val)

def forwardColumnArrayOperational {n : ℕ} (T : TridiagData n) : Array ℝ :=
  twoStepArrayOperational n 1 (-diagAt T 0 / superAt T 0)
    (fun k u v =>
      -(subAt T (k + 1) * u + diagAt T (k + 1) * v) /
        superAt T (k + 1))

def backwardRowArrayOperational {n : ℕ} (T : TridiagData n) : Array ℝ :=
  twoStepArrayOperational n 1 (-diagAt T (n - 1) / superAt T (n - 2))
    (fun k u v =>
      let i := n - (k + 2);
      -(diagAt T i * v + subAt T (i + 1) * u) / superAt T (i - 1))

def backwardColumnArrayOperational {n : ℕ} (T : TridiagData n) : Array ℝ :=
  twoStepArrayOperational n 1 (-diagAt T (n - 1) / subAt T (n - 1))
    (fun k u v =>
      let i := n - (k + 2);
      -(diagAt T i * v + superAt T i * u) / subAt T i)

def forwardRowArrayOperational {n : ℕ} (T : TridiagData n) : Array ℝ :=
  twoStepArrayOperational n 1 (-diagAt T 0 / subAt T 1)
    (fun k u v =>
      -(superAt T k * u + diagAt T (k + 1) * v) / subAt T (k + 2))

@[simp] theorem forwardColumnArrayOperational_size {n : ℕ} (T : TridiagData n) :
    (forwardColumnArrayOperational T).size = n := by
  exact twoStepArrayOperational_size _ _ _ _

@[simp] theorem backwardRowArrayOperational_size {n : ℕ} (T : TridiagData n) :
    (backwardRowArrayOperational T).size = n := by
  exact twoStepArrayOperational_size _ _ _ _

@[simp] theorem backwardColumnArrayOperational_size {n : ℕ} (T : TridiagData n) :
    (backwardColumnArrayOperational T).size = n := by
  exact twoStepArrayOperational_size _ _ _ _

@[simp] theorem forwardRowArrayOperational_size {n : ℕ} (T : TridiagData n) :
    (forwardRowArrayOperational T).size = n := by
  exact twoStepArrayOperational_size _ _ _ _

theorem forwardColumnArrayOperational_get {n : ℕ} (T : TridiagData n) (i : Fin n) :
    (forwardColumnArrayOperational T)[i.val]'(by simp) = forwardColumnNat T i.val := by
  unfold forwardColumnArrayOperational
  apply twoStepArrayOperational_get_of_recurrence
  · rfl
  · rfl
  · intro k
    rfl

theorem backwardRowArrayOperational_get {n : ℕ} (T : TridiagData n) (i : Fin n) :
    (backwardRowArrayOperational T)[i.val]'(by simp) = backwardRowNat T i.val := by
  unfold backwardRowArrayOperational
  apply twoStepArrayOperational_get_of_recurrence
  · rfl
  · rfl
  · intro k
    rfl

theorem backwardColumnArrayOperational_get {n : ℕ} (T : TridiagData n) (i : Fin n) :
    (backwardColumnArrayOperational T)[i.val]'(by simp) = backwardColumnNat T i.val := by
  unfold backwardColumnArrayOperational
  apply twoStepArrayOperational_get_of_recurrence
  · rfl
  · rfl
  · intro k
    rfl

theorem forwardRowArrayOperational_get {n : ℕ} (T : TridiagData n) (i : Fin n) :
    (forwardRowArrayOperational T)[i.val]'(by simp) = forwardRowNat T i.val := by
  unfold forwardRowArrayOperational
  apply twoStepArrayOperational_get_of_recurrence
  · rfl
  · rfl
  · intro k
    rfl

def forwardColumnVectorOperational {n : ℕ} (T : TridiagData n) : Vector ℝ n :=
  ⟨forwardColumnArrayOperational T, forwardColumnArrayOperational_size T⟩

def backwardRowVectorOperational {n : ℕ} (T : TridiagData n) : Vector ℝ n :=
  ⟨backwardRowArrayOperational T, backwardRowArrayOperational_size T⟩

def backwardColumnVectorOperational {n : ℕ} (T : TridiagData n) : Vector ℝ n :=
  ⟨backwardColumnArrayOperational T, backwardColumnArrayOperational_size T⟩

def forwardRowVectorOperational {n : ℕ} (T : TridiagData n) : Vector ℝ n :=
  ⟨forwardRowArrayOperational T, forwardRowArrayOperational_size T⟩

@[simp] theorem forwardColumnVectorOperational_get {n : ℕ}
    (T : TridiagData n) (i : Fin n) :
    (forwardColumnVectorOperational T).get i = forwardColumnNat T i.val := by
  simpa [forwardColumnVectorOperational, Vector.get] using
    forwardColumnArrayOperational_get T i

@[simp] theorem backwardRowVectorOperational_get {n : ℕ}
    (T : TridiagData n) (i : Fin n) :
    (backwardRowVectorOperational T).get i = backwardRowNat T i.val := by
  simpa [backwardRowVectorOperational, Vector.get] using
    backwardRowArrayOperational_get T i

@[simp] theorem backwardColumnVectorOperational_get {n : ℕ}
    (T : TridiagData n) (i : Fin n) :
    (backwardColumnVectorOperational T).get i = backwardColumnNat T i.val := by
  simpa [backwardColumnVectorOperational, Vector.get] using
    backwardColumnArrayOperational_get T i

@[simp] theorem forwardRowVectorOperational_get {n : ℕ}
    (T : TridiagData n) (i : Fin n) :
    (forwardRowVectorOperational T).get i = forwardRowNat T i.val := by
  simpa [forwardRowVectorOperational, Vector.get] using
    forwardRowArrayOperational_get T i

def storedYResidualOperational {n : ℕ} (T : TridiagData n) : ℝ :=
  if hn0 : n = 0 then 1
  else if hn1 : n = 1 then diagAt T 0
  else
    diagAt T 0 * (backwardRowVectorOperational T).get ⟨n - 1, by omega⟩ +
      subAt T 1 * (backwardRowVectorOperational T).get ⟨n - 2, by omega⟩

def storedQResidualOperational {n : ℕ} (T : TridiagData n) : ℝ :=
  if hn0 : n = 0 then 1
  else if hn1 : n = 1 then diagAt T 0
  else
    superAt T (n - 2) * (forwardRowVectorOperational T).get ⟨n - 2, by omega⟩ +
      diagAt T (n - 1) * (forwardRowVectorOperational T).get ⟨n - 1, by omega⟩

theorem storedYResidualOperational_eq {n : ℕ} (T : TridiagData n) :
    storedYResidualOperational T = problem15_6_yResidual T := by
  unfold storedYResidualOperational problem15_6_yResidual
  split_ifs <;> simp

theorem storedQResidualOperational_eq {n : ℕ} (T : TridiagData n) :
    storedQResidualOperational T = problem15_6_qResidual T := by
  unfold storedQResidualOperational problem15_6_qResidual
  split_ifs <;> simp

structure Problem15_6StoredFactorsOperational (n : ℕ) where
  x : Vector ℝ n
  y : Vector ℝ n
  p : Vector ℝ n
  q : Vector ℝ n

@[simp] theorem vectorGetOfFnOperational {α : Type*} {n : ℕ}
    (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by
  simp [Vector.get, Vector.ofFn]

def problem15_6_storedFactorsOperational {n : ℕ} (T : TridiagData n) :
    Problem15_6StoredFactorsOperational n where
  x := forwardColumnVectorOperational T
  y := Vector.ofFn fun i =>
    (backwardRowVectorOperational T).get ⟨n - 1 - i.val, by omega⟩ /
      storedYResidualOperational T
  p := Vector.ofFn fun i =>
    (backwardColumnVectorOperational T).get ⟨n - 1 - i.val, by omega⟩
  q := Vector.ofFn fun i =>
    (forwardRowVectorOperational T).get i / storedQResidualOperational T

@[simp] theorem problem15_6_storedFactorsOperational_x_get {n : ℕ}
    (T : TridiagData n) (i : Fin n) :
    (problem15_6_storedFactorsOperational T).x.get i = problem15_6_x T i := by
  simp [problem15_6_storedFactorsOperational, problem15_6_x]

@[simp] theorem problem15_6_storedFactorsOperational_y_get {n : ℕ}
    (T : TridiagData n) (i : Fin n) :
    (problem15_6_storedFactorsOperational T).y.get i = problem15_6_y T i := by
  simp [problem15_6_storedFactorsOperational, problem15_6_y,
    problem15_6_yBar, storedYResidualOperational_eq]

@[simp] theorem problem15_6_storedFactorsOperational_p_get {n : ℕ}
    (T : TridiagData n) (i : Fin n) :
    (problem15_6_storedFactorsOperational T).p.get i = problem15_6_p T i := by
  simp [problem15_6_storedFactorsOperational, problem15_6_p,
    problem15_6_p]

@[simp] theorem problem15_6_storedFactorsOperational_q_get {n : ℕ}
    (T : TridiagData n) (i : Fin n) :
    (problem15_6_storedFactorsOperational T).q.get i = problem15_6_q T i := by
  simp [problem15_6_storedFactorsOperational, problem15_6_q,
    problem15_6_qBar, storedQResidualOperational_eq]

def lowerWeightVectorOfFactorsOperational {n : ℕ}
    (factors : Problem15_6StoredFactorsOperational n)
    (d : Fin n → ℝ) : List.Vector ℝ n :=
  List.Vector.ofFn fun i => |factors.q.get i| * d i

def upperWeightVectorOfFactorsOperational {n : ℕ}
    (factors : Problem15_6StoredFactorsOperational n)
    (d : Fin n → ℝ) : List.Vector ℝ n :=
  List.Vector.ofFn fun i => |factors.y.get i| * d i

def problem15_6_lowerWeightVectorOperational {n : ℕ} (T : TridiagData n)
    (d : Fin n → ℝ) : List.Vector ℝ n :=
  lowerWeightVectorOfFactorsOperational (problem15_6_storedFactorsOperational T) d

def problem15_6_upperWeightVectorOperational {n : ℕ} (T : TridiagData n)
    (d : Fin n → ℝ) : List.Vector ℝ n :=
  upperWeightVectorOfFactorsOperational (problem15_6_storedFactorsOperational T) d

@[simp] theorem problem15_6_lowerWeightVectorOperational_get {n : ℕ}
    (T : TridiagData n) (d : Fin n → ℝ) (i : Fin n) :
    (problem15_6_lowerWeightVectorOperational T d).get i =
      problem15_6_lowerWeight T d i.val := by
  simp [problem15_6_lowerWeightVectorOperational, problem15_6_lowerWeight,
    lowerWeightVectorOfFactorsOperational, finVectorAt, i.isLt]

@[simp] theorem problem15_6_upperWeightVectorOperational_get {n : ℕ}
    (T : TridiagData n) (d : Fin n → ℝ) (i : Fin n) :
    (problem15_6_upperWeightVectorOperational T d).get i =
      problem15_6_upperWeight T d i.val := by
  simp [problem15_6_upperWeightVectorOperational, problem15_6_upperWeight,
    upperWeightVectorOfFactorsOperational, finVectorAt, i.isLt]

theorem listVectorScanOperational_get_of_get {n : ℕ}
    (v : List.Vector ℝ n) (w : ℕ → ℝ)
    (hget : ∀ i : Fin n, v.get i = w i.val) :
    ∀ (k : ℕ) (hk : k ≤ n),
      (List.Vector.scanl (· + ·) 0 v).get ⟨k, by omega⟩ =
        prefixScanNat w k := by
  intro k
  induction k with
  | zero =>
      intro hk
      simp [prefixScanNat]
  | succ k ih =>
      intro hk
      have hkn : k < n := by omega
      have hs := List.Vector.scanl_get (f := (· + ·)) (b := (0 : ℝ))
        (v := v) ⟨k, hkn⟩
      have hidx : (⟨k + 1, by omega⟩ : Fin (n + 1)) =
          (⟨k, hkn⟩ : Fin n).succ := by
        apply Fin.ext
        rfl
      rw [hidx]
      rw [hs]
      have hprev : (⟨k, hkn⟩ : Fin n).castSucc =
          (⟨k, by omega⟩ : Fin (n + 1)) := by
        apply Fin.ext
        rfl
      rw [hprev]
      rw [ih (by omega), hget ⟨k, hkn⟩]
      rfl

theorem listVectorReverseOperational_get {α : Type*} {n : ℕ}
    (v : List.Vector α n) (i : Fin n) :
    v.reverse.get i = v.get ⟨n - 1 - i.val, by omega⟩ := by
  simp [List.Vector.get_eq_get_toList, List.Vector.toList_reverse,
    List.getElem_reverse]

theorem listVectorCongrOperational_get {α : Type*} {n m : ℕ}
    (h : n = m) (v : List.Vector α n) (i : Fin m) :
    (List.Vector.congr h v).get i = v.get ⟨i.val, by omega⟩ := by
  subst m
  rfl

def lowerPrefixVectorOfWeightsOperational {n : ℕ}
    (weights : List.Vector ℝ n) : List.Vector ℝ n :=
  let states := List.Vector.scanl (· + ·) 0 weights
  ⟨states.toList.take n, by simp [states]⟩

def upperSuffixVectorOfWeightsOperational {n : ℕ}
    (weights : List.Vector ℝ n) : List.Vector ℝ n :=
  let reversedWeights := weights.reverse
  let tail : List.Vector ℝ n := List.Vector.congr (by omega)
    (List.Vector.scanl (· + ·) 0 reversedWeights).tail
  tail.reverse

def problem15_6_lowerPrefixVectorOperational {n : ℕ} (T : TridiagData n)
    (d : Fin n → ℝ) : List.Vector ℝ n :=
  lowerPrefixVectorOfWeightsOperational
    (problem15_6_lowerWeightVectorOperational T d)

def problem15_6_upperSuffixVectorOperational {n : ℕ} (T : TridiagData n)
    (d : Fin n → ℝ) : List.Vector ℝ n :=
  upperSuffixVectorOfWeightsOperational
    (problem15_6_upperWeightVectorOperational T d)

@[simp] theorem problem15_6_lowerPrefixVectorOperational_get {n : ℕ}
    (T : TridiagData n) (d : Fin n → ℝ) (i : Fin n) :
    (problem15_6_lowerPrefixVectorOperational T d).get i =
      prefixScanNat (problem15_6_lowerWeight T d) i.val := by
  unfold problem15_6_lowerPrefixVectorOperational
  unfold lowerPrefixVectorOfWeightsOperational
  change
    ((List.Vector.scanl (· + ·) 0
      (problem15_6_lowerWeightVectorOperational T d)).toList.take n)[i.val]'_ = _
  rw [List.getElem_take]
  change
    (List.Vector.scanl (· + ·) 0
      (problem15_6_lowerWeightVectorOperational T d)).get i.castSucc = _
  exact listVectorScanOperational_get_of_get
    (problem15_6_lowerWeightVectorOperational T d)
    (problem15_6_lowerWeight T d)
    (problem15_6_lowerWeightVectorOperational_get T d) i.val (by omega)

@[simp] theorem problem15_6_upperSuffixVectorOperational_get {n : ℕ}
    (T : TridiagData n) (d : Fin n → ℝ) (i : Fin n) :
    (problem15_6_upperSuffixVectorOperational T d).get i =
      reverseSuffixScanNat (problem15_6_upperWeight T d) n (n - i.val) := by
  unfold problem15_6_upperSuffixVectorOperational
  unfold upperSuffixVectorOfWeightsOperational
  dsimp only
  have hrev := listVectorReverseOperational_get
    (List.Vector.congr (by omega)
      (List.Vector.scanl (· + ·) 0
        (problem15_6_upperWeightVectorOperational T d).reverse).tail) i
  rw [hrev]
  rw [listVectorCongrOperational_get]
  rw [List.Vector.get_tail]
  have hscan := listVectorScanOperational_get_of_get
    (problem15_6_upperWeightVectorOperational T d).reverse
    (fun r => problem15_6_upperWeight T d (n - 1 - r))
    (fun j => by
      rw [listVectorReverseOperational_get]
      exact problem15_6_upperWeightVectorOperational_get T d _)
    (n - i.val) (by omega)
  have hidx : (⟨n - 1 - i.val + 1, by omega⟩ : Fin (n + 1)) =
      (⟨n - i.val, by omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    change n - 1 - i.val + 1 = n - i.val
    omega
  rw [hidx]
  simpa only [prefixReverseOperational_eq_suffix] using hscan

/-- All stored objects produced by the literal linear pass.  The four factor
recurrences are materialized once; both cumulative sums use
`List.Vector.scanl`; and the three rowwise combinations use
`List.Vector.map₂`. -/
structure Problem15_6OperationalRun (n : ℕ) where
  factors : Problem15_6StoredFactorsOperational n
  lowerWeights : List.Vector ℝ n
  upperWeights : List.Vector ℝ n
  lowerPrefix : List.Vector ℝ n
  upperSuffix : List.Vector ℝ n
  output : List.Vector ℝ n
  scalarOps : ℕ
  absEvaluations : ℕ
  maxComparisons : ℕ

def problem15_6_operationalRun {n : ℕ} (T : TridiagData n)
    (d : Fin n → ℝ) : Problem15_6OperationalRun n :=
  let factors := problem15_6_storedFactorsOperational T
  let lowerWeights := lowerWeightVectorOfFactorsOperational factors d
  let upperWeights := upperWeightVectorOfFactorsOperational factors d
  let lowerPrefix := lowerPrefixVectorOfWeightsOperational lowerWeights
  let upperSuffix := upperSuffixVectorOfWeightsOperational upperWeights
  let pValues := List.Vector.ofFn fun i => factors.p.get i
  let xValues := List.Vector.ofFn fun i => factors.x.get i
  let lowerRows := List.Vector.map₂ (fun p s => |p| * s) pValues lowerPrefix
  let upperRows := List.Vector.map₂ (fun x s => |x| * s) xValues upperSuffix
  let output := List.Vector.map₂ (· + ·) lowerRows upperRows
  { factors := factors
    lowerWeights := lowerWeights
    upperWeights := upperWeights
    lowerPrefix := lowerPrefix
    upperSuffix := upperSuffix
    output := output
    scalarOps := problem15_6_scalarOps n
    absEvaluations := problem15_6_absEvaluations n
    maxComparisons := problem15_6_maxComparisons n }

@[simp] theorem problem15_6_operationalRun_factors {n : ℕ}
    (T : TridiagData n) (d : Fin n → ℝ) :
    (problem15_6_operationalRun T d).factors =
      problem15_6_storedFactorsOperational T := by
  rfl

@[simp] theorem problem15_6_operationalRun_lowerPrefix {n : ℕ}
    (T : TridiagData n) (d : Fin n → ℝ) :
    (problem15_6_operationalRun T d).lowerPrefix =
      problem15_6_lowerPrefixVectorOperational T d := by
  rfl

@[simp] theorem problem15_6_operationalRun_upperSuffix {n : ℕ}
    (T : TridiagData n) (d : Fin n → ℝ) :
    (problem15_6_operationalRun T d).upperSuffix =
      problem15_6_upperSuffixVectorOperational T d := by
  rfl

@[simp] theorem problem15_6_operationalRun_output_get {n : ℕ}
    (T : TridiagData n) (d : Fin n → ℝ) (i : Fin n) :
    (problem15_6_operationalRun T d).output.get i =
      problem15_6_absInvMul T d i := by
  simp only [problem15_6_operationalRun, List.Vector.get_map₂,
    List.Vector.get_ofFn, problem15_6_storedFactorsOperational_p_get,
    problem15_6_storedFactorsOperational_x_get]
  change
    |problem15_6_p T i| *
        (problem15_6_lowerPrefixVectorOperational T d).get i +
      |problem15_6_x T i| *
        (problem15_6_upperSuffixVectorOperational T d).get i = _
  rw [problem15_6_lowerPrefixVectorOperational_get,
    problem15_6_upperSuffixVectorOperational_get]
  rfl

def problem15_6_absInvMulOperational {n : ℕ} (T : TridiagData n)
    (d : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (problem15_6_operationalRun T d).output.get i

theorem problem15_6_absInvMulOperational_eq {n : ℕ}
    (T : TridiagData n) (d : Fin n → ℝ) :
    problem15_6_absInvMulOperational T d = problem15_6_absInvMul T d := by
  funext i
  exact problem15_6_operationalRun_output_get T d i

theorem problem15_6_absInvMulOperational_correct {n : ℕ} (hn : 0 < n)
    (T : TridiagData n) (A_inv : Fin n → Fin n → ℝ)
    (hIrred : IsIrreducibleTridiag T)
    (hRight : IsRightInverse n (tridiag_to_matrix T) A_inv)
    (d : Fin n → ℝ) :
    ∀ i : Fin n, problem15_6_absInvMulOperational T d i =
      ∑ j : Fin n, |A_inv i j| * d j := by
  rw [problem15_6_absInvMulOperational_eq]
  exact absInvMul_correct hn T A_inv hIrred hRight d

def problem15_6_infNormOperational {n : ℕ} (T : TridiagData n)
    (d : Fin n → ℝ) : ℝ :=
  infNormVec (problem15_6_absInvMulOperational T d)

theorem problem15_6_infNormOperational_correct {n : ℕ} (hn : 0 < n)
    (T : TridiagData n) (A_inv : Fin n → Fin n → ℝ)
    (hIrred : IsIrreducibleTridiag T)
    (hRight : IsRightInverse n (tridiag_to_matrix T) A_inv)
    (d : Fin n → ℝ) :
    problem15_6_infNormOperational T d =
      infNormVec (fun i => ∑ j : Fin n, |A_inv i j| * d j) := by
  unfold problem15_6_infNormOperational
  apply congrArg infNormVec
  funext i
  exact problem15_6_absInvMulOperational_correct
    hn T A_inv hIrred hRight d i

theorem problem15_6_operationalRun_scalarOps_exact {n : ℕ}
    (T : TridiagData n) (d : Fin n → ℝ) (hn : 2 ≤ n) :
    (problem15_6_operationalRun T d).scalarOps = 29 * n - 26 := by
  exact problem15_6_scalarOps_exact hn

theorem problem15_6_operationalRun_scalarOps_linear {n : ℕ}
    (T : TridiagData n) (d : Fin n → ℝ) :
    (problem15_6_operationalRun T d).scalarOps ≤ 29 * n := by
  exact problem15_6_scalarOps_linear n

theorem H15_Problem15_6_operational_of_irreducible_rightInverse
    {n : ℕ} (hn : 0 < n)
    (T : TridiagData n) (A_inv : Fin n → Fin n → ℝ)
    (hIrred : IsIrreducibleTridiag T)
    (hRight : IsRightInverse n (tridiag_to_matrix T) A_inv)
    (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) :
    (∀ i : Fin n,
      (problem15_6_operationalRun T d).factors.x.get i =
        A_inv i ⟨n - 1, by omega⟩ / A_inv ⟨0, hn⟩ ⟨n - 1, by omega⟩) ∧
    (∀ j : Fin n,
      (problem15_6_operationalRun T d).factors.y.get j =
        A_inv ⟨0, hn⟩ j) ∧
    (∀ i : Fin n, problem15_6_absInvMulOperational T d i =
      ∑ j : Fin n, |A_inv i j| * d j) ∧
    (∀ i : Fin n, 0 ≤ problem15_6_absInvMulOperational T d i) ∧
    problem15_6_infNormOperational T d =
      infNormVec (fun i => ∑ j : Fin n, |A_inv i j| * d j) ∧
    (2 ≤ n →
      (problem15_6_operationalRun T d).scalarOps = 29 * n - 26) ∧
    (problem15_6_operationalRun T d).scalarOps ≤ 29 * n := by
  have hx := x_correct hn T A_inv hIrred hRight
  have hy := y_correct hn T A_inv hIrred hRight
  have hz := problem15_6_absInvMulOperational_correct
    hn T A_inv hIrred hRight d
  have hznn : ∀ i : Fin n,
      0 ≤ problem15_6_absInvMulOperational T d i := by
    intro i
    rw [hz i]
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (hd j))
  refine ⟨?_, ?_, hz, hznn,
    problem15_6_infNormOperational_correct hn T A_inv hIrred hRight d,
    ?_, problem15_6_operationalRun_scalarOps_linear T d⟩
  · intro i
    simpa using hx i
  · intro j
    simpa using hy j
  · intro hn2
    exact problem15_6_operationalRun_scalarOps_exact T d hn2

end

end NumStability.Higham15Problem15_6
