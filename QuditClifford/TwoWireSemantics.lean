import QuditClifford.CircuitSemantics
import QuditClifford.DerivedGates

/-! Exact placement of arbitrary two-qudit operators on distinct named wires. -/
noncomputable section
namespace QuditClifford.Circuit
open Matrix
open scoped Kronecker
variable {d n : ℕ} [NeZero d]

/-- Place a two-qudit matrix on an ordered pair of distinct register wires. -/
def onTwoWires (i j : Fin n) (A : TwoQuditMatrix d) : QuditOperator d n :=
  fun row col => if ∀ k, k ≠ i → k ≠ j → row k = col k then
    A (row i, row j) (col i, col j) else 0

/-- Replace two distinct coordinates of a computational-basis vector. -/
def updateTwo (i j : Fin n) (col : Fin n → ZMod d) (t : ZMod d × ZMod d) :=
  Function.update (Function.update col i t.1) j t.2

omit [NeZero d] in
@[simp] theorem updateTwo_first (i j : Fin n) (h : i ≠ j)
    (col : Fin n → ZMod d) (t : ZMod d × ZMod d) : updateTwo i j col t i = t.1 := by
  simp [updateTwo, Function.update_of_ne h]

omit [NeZero d] in
@[simp] theorem updateTwo_second (i j : Fin n)
    (col : Fin n → ZMod d) (t : ZMod d × ZMod d) : updateTwo i j col t j = t.2 := by
  simp [updateTwo]

omit [NeZero d] in
@[simp] theorem updateTwo_other (i j k : Fin n) (hi : k ≠ i) (hj : k ≠ j)
    (col : Fin n → ZMod d) (t : ZMod d × ZMod d) : updateTwo i j col t k = col k := by
  simp [updateTwo, Function.update_of_ne hi, Function.update_of_ne hj]

omit [NeZero d] in
private theorem updateTwo_injective (i j : Fin n) (h : i ≠ j) (col : Fin n → ZMod d) :
    Function.Injective (updateTwo i j col) := by
  intro a b hab
  apply Prod.ext
  · simpa [h] using congrFun hab i
  · simpa using congrFun hab j

/-- Multiplication by a placed two-wire operator sums only over those two wires. -/
theorem mul_onTwoWires_apply (i j : Fin n) (h : i ≠ j)
    (M : QuditOperator d n) (A : TwoQuditMatrix d) (row col : Fin n → ZMod d) :
    (M * onTwoWires i j A) row col =
      ∑ t : ZMod d × ZMod d, M row (updateTwo i j col t) * A t (col i, col j) := by
  classical
  rw [Matrix.mul_apply]
  let f := fun mid => M row mid * onTwoWires i j A mid col
  have hsum : ∑ mid, f mid = ∑ t, f (updateTwo i j col t) := by
    rw [← Finset.sum_image (updateTwo_injective i j h col).injOn]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro mid _ hnot
    have hoff : ¬ ∀ k, k ≠ i → k ≠ j → mid k = col k := by
      intro hm
      apply hnot
      apply Finset.mem_image.mpr
      refine ⟨(mid i, mid j), Finset.mem_univ _, ?_⟩
      funext k
      by_cases hi : k = i
      · subst k; simp [h]
      by_cases hj : k = j
      · subst k; simp
      simp [updateTwo_other i j k hi hj, hm k hi hj]
    simp [f, onTwoWires, hoff]
  change ∑ mid, f mid = _
  rw [hsum]
  apply Finset.sum_congr rfl
  intro t _
  have hoff : ∀ k, k ≠ i → k ≠ j → updateTwo i j col t k = col k := by
    intro k hi hj; exact updateTwo_other i j k hi hj col t
  dsimp only [f]
  rw [onTwoWires, if_pos hoff]
  simp [h]

/-- Placement is multiplicative, including its idle-wire identities. -/
theorem onTwoWires_mul (i j : Fin n) (h : i ≠ j) (A B : TwoQuditMatrix d) :
    onTwoWires i j (A * B) = onTwoWires i j A * onTwoWires i j B := by
  classical
  ext row col
  rw [mul_onTwoWires_apply i j h]
  have hoff (t : ZMod d × ZMod d) :
      (∀ k, k ≠ i → k ≠ j → row k = updateTwo i j col t k) ↔
      (∀ k, k ≠ i → k ≠ j → row k = col k) := by
    constructor <;> intro hh k hi hj <;>
      simpa [updateTwo_other i j k hi hj] using hh k hi hj
  by_cases hh : ∀ k, k ≠ i → k ≠ j → row k = col k
  · simp [onTwoWires, hoff, hh, h, Matrix.mul_apply]
  · simp [onTwoWires, hoff, hh]

omit [NeZero d] in
@[simp] theorem onTwoWires_one (i j : Fin n) :
    onTwoWires i j (1 : TwoQuditMatrix d) = (1 : QuditOperator d n) := by
  classical
  ext row col
  by_cases heq : row = col
  · subst row; simp [onTwoWires, Matrix.one_apply]
  · have hnot : ¬ ((∀ k, k ≠ i → k ≠ j → row k = col k) ∧
        (row i, row j) = (col i, col j)) := by
      rintro ⟨hoff, hp⟩
      apply heq
      funext k
      by_cases hi : k = i
      · simpa [hi] using congrArg Prod.fst hp
      by_cases hj : k = j
      · simpa [hj] using congrArg Prod.snd hp
      exact hoff k hi hj
    simp only [onTwoWires, Matrix.one_apply, if_neg heq]
    split_ifs with hoff hp
    · exact False.elim (hnot ⟨hoff, hp⟩)
    all_goals rfl

omit [NeZero d] in
@[simp] theorem onTwoWires_smul (i j : Fin n) (c : ℂ) (A : TwoQuditMatrix d) :
    onTwoWires i j (c • A) = c • onTwoWires i j A := by
  classical
  ext row col
  simp only [onTwoWires, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

theorem onTwoWires_pow (i j : Fin n) (h : i ≠ j) (A : TwoQuditMatrix d) (k : ℕ) :
    onTwoWires i j (A ^ k) = onTwoWires i j A ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, onTwoWires_mul i j h, ih, pow_succ]

omit [NeZero d] in
/-- Placement of a first-wire operator agrees with one-wire placement. -/
@[simp] theorem onTwoWires_firstWire (i j : Fin n) (h : i ≠ j) (A : QuditMatrix d) :
    onTwoWires i j (firstWire d A) = onWire i A := by
  classical
  ext row col
  have hoff : (∀ k, k ≠ i → row k = col k) ↔
      (∀ k, k ≠ i → k ≠ j → row k = col k) ∧ row j = col j := by
    constructor
    · intro hh; exact ⟨fun k hi _ => hh k hi, hh j h.symm⟩
    · rintro ⟨hh, hj⟩ k hi
      by_cases hk : k = j
      · simpa [hk] using hj
      · exact hh k hi hk
  simp only [onTwoWires, firstWire, Matrix.kronecker_apply, Matrix.one_apply, onWire, hoff]
  split_ifs <;> simp_all

omit [NeZero d] in
@[simp] theorem onTwoWires_secondWire (i j : Fin n) (h : i ≠ j) (A : QuditMatrix d) :
    onTwoWires i j (secondWire d A) = onWire j A := by
  classical
  ext row col
  have hoff : (∀ k, k ≠ j → row k = col k) ↔
      (∀ k, k ≠ i → k ≠ j → row k = col k) ∧ row i = col i := by
    constructor
    · intro hh; exact ⟨fun k _ hj => hh k hj, hh i h⟩
    · rintro ⟨hh, hi⟩ k hj
      by_cases hk : k = i
      · simpa [hk] using hi
      · exact hh k hk hj
  simp only [onTwoWires, secondWire, Matrix.kronecker_apply, Matrix.one_apply, onWire, hoff]
  split_ifs <;> simp_all

omit [NeZero d] in
@[simp] theorem onTwoWires_diagonal (i j : Fin n) (f : ZMod d × ZMod d → ℂ) :
    onTwoWires i j (Matrix.diagonal f) =
      Matrix.diagonal (fun row : Fin n → ZMod d => f (row i, row j)) := by
  classical
  ext row col
  by_cases heq : row = col
  · subst row; simp [onTwoWires, Matrix.diagonal_apply]
  · have hnot : ¬ ((∀ k, k ≠ i → k ≠ j → row k = col k) ∧
        (row i, row j) = (col i, col j)) := by
      rintro ⟨hoff, hp⟩
      apply heq
      funext k
      by_cases hi : k = i
      · simpa [hi] using congrArg Prod.fst hp
      by_cases hj : k = j
      · simpa [hj] using congrArg Prod.snd hp
      exact hoff k hi hj
    simp only [onTwoWires, Matrix.diagonal_apply, if_neg heq]
    split_ifs with hoff hp
    · exact False.elim (hnot ⟨hoff, hp⟩)
    all_goals rfl

omit [NeZero d] in
/-- A two-wire basis map acts by replacing the chosen pair of coordinates. -/
theorem onTwoWires_basisMap (i j : Fin n) (h : i ≠ j)
    (f : (ZMod d × ZMod d) → (ZMod d × ZMod d)) :
    onTwoWires i j (basisMap f) =
      basisMap (fun col => updateTwo i j col (f (col i, col j))) := by
  classical
  ext row col
  have hh : row = updateTwo i j col (f (col i, col j)) ↔
      (∀ k, k ≠ i → k ≠ j → row k = col k) ∧
        (row i, row j) = f (col i, col j) := by
    constructor
    · intro heq; subst row
      exact ⟨fun k hi hj => updateTwo_other i j k hi hj _ _, by simp [h]⟩
    · rintro ⟨hoff, hp⟩
      funext k
      by_cases hi : k = i
      · subst k; simpa [h] using congrArg Prod.fst hp
      by_cases hj : k = j
      · subst k; simpa using congrArg Prod.snd hp
      simp [updateTwo_other i j k hi hj, hoff k hi hj]
  simp only [onTwoWires, basisMap, hh]
  split_ifs <;> simp_all

end QuditClifford.Circuit
