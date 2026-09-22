import QuditClifford.AdjacentOneWireRewrites
import QuditClifford.AdjacentNormalCircuit

/-!
# Canonical orientation and reflection of two-wire words

On two wires there is only one physical CZ location. This module removes
the reverse spelling of that location and defines reflection while retaining
the canonical CZ letter. Preservation of rewrite proofs is a separate theorem.
-/
namespace QuditClifford.Circuit

/-- Choose the canonical spelling of the only two-wire controlled phase. -/
def orientTwoGate : Gate 2 → Gate 2
  | .scalar => .scalar
  | .H i => .H i
  | .S i => .S i
  | .CZ _ _ _ => .CZ 0 1 (by decide)

/-- Orient CZ letters; every other primitive letter is unchanged. -/
def orientTwoWord (w : Word 2) : Word 2 := w.map orientTwoGate

/-- Reflection of the two physical wire positions. -/
def flipTwo : Fin 2 ↪ Fin 2 := (Equiv.swap 0 1).toEmbedding

/-- Wire reflection followed by canonical orientation of CZ. -/
def reflectTwoWord (w : Word 2) : Word 2 := orientTwoWord (relabel flipTwo w)

@[simp] theorem flipTwo_zero : flipTwo 0 = 1 := by simp [flipTwo]
@[simp] theorem flipTwo_one : flipTwo 1 = 0 := by simp [flipTwo]
@[simp] theorem flipTwo_flip (i : Fin 2) : flipTwo (flipTwo i) = i := by
  fin_cases i <;> simp

@[simp] theorem orientTwoWord_nil : orientTwoWord [] = [] := rfl
@[simp] theorem orientTwoWord_cons (a : Gate 2) (w : Word 2) :
    orientTwoWord (a::w) = orientTwoGate a :: orientTwoWord w := rfl
@[simp] theorem orientTwoWord_append (u v : Word 2) :
    orientTwoWord (u++v) = orientTwoWord u ++ orientTwoWord v := List.map_append
@[simp] theorem orientTwoWord_replicate (k : ℕ) (a : Gate 2) :
    orientTwoWord (List.replicate k a) = List.replicate k (orientTwoGate a) :=
  List.map_replicate
@[simp] theorem orientTwoWord_power (w : Word 2) (k : ℕ) :
    orientTwoWord (power w k) = power (orientTwoWord w) k := by
  simp [orientTwoWord, power, List.map_flatten]

@[simp] theorem reflectTwoWord_nil : reflectTwoWord [] = [] := rfl
@[simp] theorem reflectTwoWord_cons (a : Gate 2) (w : Word 2) :
    reflectTwoWord (a::w) = orientTwoGate (a.relabel flipTwo) :: reflectTwoWord w := rfl
@[simp] theorem reflectTwoWord_append (u v : Word 2) :
    reflectTwoWord (u++v) = reflectTwoWord u ++ reflectTwoWord v := by
  simp [reflectTwoWord]
@[simp] theorem reflectTwoWord_replicate (k : ℕ) (a : Gate 2) :
    reflectTwoWord (List.replicate k a) =
      List.replicate k (orientTwoGate (a.relabel flipTwo)) := by simp [reflectTwoWord]
@[simp] theorem reflectTwoWord_power (w : Word 2) (k : ℕ) :
    reflectTwoWord (power w k) = power (reflectTwoWord w) k := by simp [reflectTwoWord]

theorem orientTwoGate_isAdjacent (a : Gate 2) : (orientTwoGate a).IsAdjacent := by
  cases a with
  | scalar => exact Gate.isAdjacent_scalar
  | H i => exact Gate.isAdjacent_H i
  | S i => exact Gate.isAdjacent_S i
  | CZ i j hij => exact ⟨.CZ 0, rfl⟩

theorem orientTwoWord_isAdjacent (w : Word 2) : IsAdjacentWord (orientTwoWord w) := by
  intro a ha
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
  exact orientTwoGate_isAdjacent b

theorem reflectTwoWord_isAdjacent (w : Word 2) : IsAdjacentWord (reflectTwoWord w) :=
  orientTwoWord_isAdjacent _

theorem orientTwoGate_eq_of_adjacent (a : Gate 2) (ha : a.IsAdjacent) : orientTwoGate a = a := by
  obtain ⟨b, rfl⟩ := ha
  cases b with
  | scalar => rfl
  | H i => rfl
  | S i => rfl
  | CZ i => have hi : i = 0 := Fin.ext (by omega); subst i; rfl

theorem orientTwoWord_eq_of_adjacent (w : Word 2) (hw : IsAdjacentWord w) :
    orientTwoWord w = w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      rw [isAdjacentWord_cons] at hw
      rw [orientTwoWord_cons, orientTwoGate_eq_of_adjacent a hw.1, ih hw.2]

@[simp] theorem orientTwoWord_idempotent (w : Word 2) :
    orientTwoWord (orientTwoWord w) = orientTwoWord w :=
  orientTwoWord_eq_of_adjacent _ (orientTwoWord_isAdjacent _)

@[simp] theorem orientTwoWord_scalar (k : ℕ) :
    orientTwoWord (scalar k) = scalar k := by simp [scalar, orientTwoGate]

@[simp] theorem orientTwoWord_Sexp {d : ℕ} (i : Fin 2) (a : ZMod d) :
    orientTwoWord (Sexp i a) = Sexp i a := by simp [Sexp, orientTwoGate]

@[simp] theorem orientTwoWord_X {d : ℕ} (i : Fin 2) :
    orientTwoWord (X (d := d) i) = X (d := d) i :=
  orientTwoWord_eq_of_adjacent _ (isAdjacentWord_X i)
@[simp] theorem orientTwoWord_Z {d : ℕ} (i : Fin 2) :
    orientTwoWord (Z (d := d) i) = Z (d := d) i :=
  orientTwoWord_eq_of_adjacent _ (isAdjacentWord_Z i)
@[simp] theorem orientTwoWord_Xexp {d : ℕ} (i : Fin 2) (a : ZMod d) :
    orientTwoWord (Xexp i a) = Xexp i a := by simp [Xexp]
@[simp] theorem orientTwoWord_Zexp {d : ℕ} (i : Fin 2) (a : ZMod d) :
    orientTwoWord (Zexp i a) = Zexp i a := by simp [Zexp]
@[simp] theorem orientTwoWord_multiplier {d : ℕ} [NeZero d] (i : Fin 2) (a : (ZMod d)ˣ) :
    orientTwoWord (multiplier i a) = multiplier i a :=
  orientTwoWord_eq_of_adjacent _ (isAdjacentWord_multiplier i a)

@[simp] theorem reflectTwoWord_scalar (k : ℕ) : reflectTwoWord (scalar k) = scalar k := by
  simp [reflectTwoWord]
@[simp] theorem reflectTwoWord_Sexp {d : ℕ} (i : Fin 2) (a : ZMod d) :
    reflectTwoWord (Sexp i a) = Sexp (flipTwo i) a := by simp [reflectTwoWord]
@[simp] theorem reflectTwoWord_X {d : ℕ} (i : Fin 2) :
    reflectTwoWord (X (d := d) i) = X (d := d) (flipTwo i) := by simp [reflectTwoWord]
@[simp] theorem reflectTwoWord_Z {d : ℕ} (i : Fin 2) :
    reflectTwoWord (Z (d := d) i) = Z (d := d) (flipTwo i) := by simp [reflectTwoWord]
@[simp] theorem reflectTwoWord_Xexp {d : ℕ} (i : Fin 2) (a : ZMod d) :
    reflectTwoWord (Xexp i a) = Xexp (flipTwo i) a := by simp [reflectTwoWord]
@[simp] theorem reflectTwoWord_Zexp {d : ℕ} (i : Fin 2) (a : ZMod d) :
    reflectTwoWord (Zexp i a) = Zexp (flipTwo i) a := by simp [reflectTwoWord]
@[simp] theorem reflectTwoWord_multiplier {d : ℕ} [NeZero d] (i : Fin 2) (a : (ZMod d)ˣ) :
    reflectTwoWord (multiplier i a) = multiplier (flipTwo i) a := by simp [reflectTwoWord]

/-- Reflecting an already reflected named word only orients its CZ spelling. -/
@[simp] theorem reflectTwoWord_relabel_flip (w : Word 2) :
    reflectTwoWord (relabel flipTwo w) = orientTwoWord w := by
  unfold reflectTwoWord relabel orientTwoWord
  simp only [List.map_map]
  apply List.map_congr_left
  intro a _
  cases a <;> simp [Gate.relabel, orientTwoGate]

/-- Orienting a two-wire CZ does not alter its set of physical wires. -/
theorem orientTwoGate_support (a : Gate 2) : (orientTwoGate a).support = a.support := by
  cases a with
  | scalar => rfl
  | H i => rfl
  | S i => rfl
  | CZ i j hij =>
      fin_cases i <;> fin_cases j
      all_goals first | exact (hij rfl).elim | simp [orientTwoGate, Gate.support, Finset.pair_comm]

end QuditClifford.Circuit
