import QuditClifford.AdjacentCircuit
import QuditClifford.WireContextRewrites
import QuditClifford.NormalCircuit

/-!
# Explicit dirty syntax between the Z and X normalization sweeps

A Z sweep can emit S on any wire, adjacent CZ, and H away from its first wire.
The grammar below records that restriction syntactically. It is closed under
composition and the literal positive-power inverse expansion. Every elaborated
word fixes first-wire Z. This invariant is a soundness lemma, not a premise
that promotes arbitrary semantic equalities to rewrite derivations.

After the X sweep, the residual circuit is an ordinary word on one fewer
wires, embedded with `initialEmbedding`; the main normal-form induction can
then process that smaller circuit.
-/
noncomputable section
namespace QuditClifford.NormalBoxes
open Circuit

/-- Dirty gates allowed between the Z and X sweeps. A Fourier gate cannot act
on the distinguished first wire. -/
inductive ZSweepGate (n : ℕ)
  | scalar : ZSweepGate n
  | H (i : Fin n) : ZSweepGate n
  | S (i : Fin (n+1)) : ZSweepGate n
  | CZ (i : Fin n) : ZSweepGate n

/-- Elaborate the restricted gate grammar into the original primitive alphabet. -/
def ZSweepGate.toGate {n : ℕ} : ZSweepGate n → Gate (n+1)
  | .scalar => .scalar
  | .H i => .H i.succ
  | .S i => .S i
  | .CZ i => .CZ i.castSucc i.succ (adjacent_ne i)

/-- A finite dirty circuit carries its grammar restriction explicitly. -/
abbrev ZSweepWord (n : ℕ) := List (ZSweepGate n)

/-- Literal elaboration retains every scalar letter. -/
def ZSweepWord.toWord {n : ℕ} (w : ZSweepWord n) : Word (n+1) := w.map ZSweepGate.toGate

@[simp] theorem ZSweepWord.toWord_nil {n : ℕ} :
    ZSweepWord.toWord ([] : ZSweepWord n) = [] := rfl

@[simp] theorem ZSweepWord.toWord_cons {n : ℕ} (a : ZSweepGate n) (w : ZSweepWord n) :
    toWord (a::w) = a.toGate :: w.toWord := rfl

@[simp] theorem ZSweepWord.toWord_append {n : ℕ} (u v : ZSweepWord n) :
    (u++v).toWord = u.toWord ++ v.toWord := List.map_append

/-- An adjacent primitive on trailing wires is an allowed dirty gate. -/
def ZSweepGate.fromTail : {n : ℕ} → AdjacentGate n → ZSweepGate n
  | _, .scalar => .scalar
  | _, .H i => .H i
  | _, .S i => .S i.succ
  | _, .CZ i => .CZ i.succ

@[simp] theorem ZSweepGate.toGate_fromTail {n : ℕ} (a : AdjacentGate n) :
    (ZSweepGate.fromTail a).toGate = a.toGate.relabel (shiftEmbedding n) := by cases a <;> rfl

/-- Lift an adjacent circuit on trailing wires into the dirty grammar. -/
def ZSweepWord.fromTail {n : ℕ} (w : AdjacentWord n) : ZSweepWord n := w.map ZSweepGate.fromTail

@[simp] theorem ZSweepWord.toWord_fromTail {n : ℕ} (w : AdjacentWord n) :
    (ZSweepWord.fromTail w).toWord = relabel (shiftEmbedding n) w.toWord := by
  simp only [fromTail, toWord, AdjacentWord.toWord, relabel, List.map_map]
  congr 1
  funext a
  exact ZSweepGate.toGate_fromTail a

/-- Dirty generators remain inside the adjacent source alphabet. -/
def ZSweepGate.toAdjacent {n : ℕ} : ZSweepGate n → AdjacentGate (n+1)
  | .scalar => .scalar
  | .H i => .H i.succ
  | .S i => .S i
  | .CZ i => .CZ i

@[simp] theorem ZSweepGate.toGate_toAdjacent {n : ℕ} (a : ZSweepGate n) :
    a.toAdjacent.toGate = a.toGate := by cases a <;> rfl

/-- Dirty-word elaboration uses only adjacent primitive CZ gates. -/
theorem ZSweepWord.isAdjacent_toWord {n : ℕ} (w : ZSweepWord n) : IsAdjacentWord w.toWord := by
  intro a ha
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
  exact ⟨b.toAdjacent, b.toGate_toAdjacent⟩

/-- Any residue phase on the first wire is an allowed dirty word. -/
def ZSweepWord.firstPhase {d n : ℕ} (t : ZMod d) : ZSweepWord n :=
  List.replicate t.val (.S 0)

@[simp] theorem ZSweepWord.toWord_firstPhase {d n : ℕ} (t : ZMod d) :
    (ZSweepWord.firstPhase (n := n) t).toWord = Sexp 0 t := by
  simp only [toWord, firstPhase, List.map_replicate, ZSweepGate.toGate, Sexp]

/-- The literal inverse expansion remains inside the restricted grammar. -/
def ZSweepGate.inverseWord {n : ℕ} (d : ℕ) : ZSweepGate n → ZSweepWord n
  | .scalar => List.replicate (2*d-1) .scalar
  | .H i => List.replicate 3 (.H i)
  | .S i => List.replicate (d-1) (.S i)
  | .CZ i => List.replicate (d-1) (.CZ i)

@[simp] theorem ZSweepGate.toWord_inverseWord {n : ℕ} (d : ℕ) (a : ZSweepGate n) :
    (a.inverseWord d).toWord = a.toGate.inverseWord d := by
  cases a <;> simp only [inverseWord, ZSweepWord.toWord, List.map_replicate,
    toGate, Gate.inverseWord]

/-- Invert a dirty word by reversing factor order and expanding positive powers. -/
def ZSweepWord.inverseWord {n : ℕ} (d : ℕ) (w : ZSweepWord n) : ZSweepWord n :=
  (w.reverse.map (ZSweepGate.inverseWord d)).flatten

@[simp] theorem ZSweepWord.toWord_inverseWord {n : ℕ} (d : ℕ) (w : ZSweepWord n) :
    (w.inverseWord d).toWord = Circuit.inverseWord d w.toWord := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have hw : inverseWord d (a::w) = inverseWord d w ++ a.inverseWord d := by
      simp [inverseWord]
    rw [hw, toWord_append, ih, ZSweepGate.toWord_inverseWord, toWord_cons, Circuit.inverseWord_cons]

variable {d n : ℕ} [Fact d.Prime]

/-- Each dirty primitive fixes the distinguished first-wire Z vector. -/
theorem ZSweepGate.fixes_headZ (a : ZSweepGate n) :
    a.toGate.wireAction d (headZ n) = headZ n := by
  cases a with
  | scalar => rfl
  | H i =>
    funext k
    by_cases hki : k = i.succ
    · subst k
      simp [ZSweepGate.toGate, Gate.wireAction_H, headZ, zVector]
    · simp [ZSweepGate.toGate, Gate.wireAction_H, hki]
  | S i =>
    funext k
    by_cases hki : k=i
    · subst k
      cases i using Fin.cases <;> simp [ZSweepGate.toGate, Gate.wireAction_S, headZ, zVector]
    · simp [ZSweepGate.toGate, Gate.wireAction_S, hki]
  | CZ i =>
    funext k
    have hx : ∀ l : Fin (n+1), (headZ n (K := ZMod d) l).2 = 0 := by
      intro l
      cases l using Fin.cases <;> simp [headZ, zVector]
    apply Prod.ext <;> simp [ZSweepGate.toGate, Gate.wireAction_CZ, hx]

/-- Every syntactically restricted dirty word fixes first-wire Z. -/
theorem ZSweepWord.fixes_headZ (w : ZSweepWord n) :
    wireAction d w.toWord (headZ n) = headZ n := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [toWord_cons, wireAction_cons, ih]
    exact a.fixes_headZ

/-- The residual of an X sweep is compiled on the preceding wires. -/
def xSweepResidual (w : AdjacentWord n) : Word (n+1) := relabel (initialEmbedding n) w.toWord

end QuditClifford.NormalBoxes
