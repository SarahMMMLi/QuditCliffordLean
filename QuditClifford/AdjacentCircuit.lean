import QuditClifford.RelabelRewrites

/-!
# The adjacent primitive alphabet used by the normalization source

The pinned Agda release's `Circuit/Base.agda` builds generators from local
arity-one/arity-two gates and shifts. Its `Symplectic/Syntactics/Gates.agda`
therefore has only adjacent primitive CZ gates. The alphabet below makes that
restriction explicit while retaining the exact scalar letter. Elaboration
lands in the existing named-wire syntax; no new rewrite rule is introduced,
and no equality of a nonadjacent primitive CZ with a SWAP expansion is assumed.
-/
namespace QuditClifford.Circuit

/-- Neighboring finite-wire positions are distinct. -/
theorem adjacent_ne {n : ℕ} (i : Fin n) : i.castSucc ≠ i.succ := by
  intro h
  have hv := congrArg Fin.val h
  change i.val=i.val+1 at hv
  omega

/-- H, S, scalar, and nearest-neighbor CZ generators, as in the source alphabet. -/
inductive AdjacentGate : ℕ → Type
  | scalar {n : ℕ} : AdjacentGate n
  | H {n : ℕ} (i : Fin n) : AdjacentGate n
  | S {n : ℕ} (i : Fin n) : AdjacentGate n
  | CZ {n : ℕ} (i : Fin n) : AdjacentGate (n+1)

/-- Elaborate into the existing primitive syntax on named wires. -/
def AdjacentGate.toGate : {n : ℕ} → AdjacentGate n → Gate n
  | _, .scalar => .scalar
  | _, .H i => .H i
  | _, .S i => .S i
  | _, .CZ i => .CZ i.castSucc i.succ (adjacent_ne i)

/-- The explicit finite-word grammar for the adjacent generating alphabet. -/
abbrev AdjacentWord (n : ℕ) := List (AdjacentGate n)

/-- Elaboration preserves the original primitive letters, including scalars. -/
def AdjacentWord.toWord {n : ℕ} (w : AdjacentWord n) : Word n := w.map AdjacentGate.toGate

@[simp] theorem AdjacentWord.toWord_nil {n : ℕ} : toWord ([] : AdjacentWord n) = [] := rfl
@[simp] theorem AdjacentWord.toWord_cons {n : ℕ} (a : AdjacentGate n) (w : AdjacentWord n) :
    toWord (a::w) = a.toGate :: toWord w := rfl
@[simp] theorem AdjacentWord.toWord_append {n : ℕ} (u v : AdjacentWord n) :
    toWord (u++v) = toWord u ++ toWord v := List.map_append

/-- Membership in the adjacent alphabet as a predicate on existing primitive gates. -/
def Gate.IsAdjacent {n : ℕ} (a : Gate n) : Prop := ∃ b : AdjacentGate n, b.toGate=a

/-- Existing words can be checked for membership in the adjacent alphabet. -/
def IsAdjacentWord {n : ℕ} (w : Word n) : Prop := ∀ a ∈ w, a.IsAdjacent

/-- Every elaborated adjacent word has only adjacent primitive letters. -/
theorem AdjacentWord.isAdjacent_toWord {n : ℕ} (w : AdjacentWord n) : IsAdjacentWord w.toWord := by
  intro a ha
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
  exact ⟨b, rfl⟩

/-- The predicate and explicit grammar describe exactly the same primitive words. -/
theorem isAdjacentWord_iff_exists {n : ℕ} (w : Word n) :
    IsAdjacentWord w ↔ ∃ v : AdjacentWord n, v.toWord=w := by
  constructor
  · intro h
    induction w with
    | nil => exact ⟨[], rfl⟩
    | cons a w ih =>
      obtain ⟨b, hb⟩ := h a (by simp)
      obtain ⟨v, hv⟩ := ih (fun x hx => h x (by simp [hx]))
      exact ⟨b::v, by rw [AdjacentWord.toWord_cons, hb, hv]⟩
  · rintro ⟨v, rfl⟩
    exact v.isAdjacent_toWord

/-- Add an idle first wire, preserving adjacency. -/
def AdjacentGate.shift : {n : ℕ} → AdjacentGate n → AdjacentGate (n+1)
  | _, .scalar => .scalar
  | _, .H i => .H i.succ
  | _, .S i => .S i.succ
  | _, .CZ i => .CZ i.succ

/-- Add an idle last wire, preserving adjacency. -/
def AdjacentGate.initial : {n : ℕ} → AdjacentGate n → AdjacentGate (n+1)
  | _, .scalar => .scalar
  | _, .H i => .H i.castSucc
  | _, .S i => .S i.castSucc
  | _, .CZ i => .CZ i.castSucc

@[simp] theorem AdjacentGate.toGate_shift {n : ℕ} (a : AdjacentGate n) :
    a.shift.toGate = a.toGate.relabel (shiftEmbedding n) := by cases a <;> rfl

@[simp] theorem AdjacentGate.toGate_initial {n : ℕ} (a : AdjacentGate n) :
    a.initial.toGate = a.toGate.relabel (initialEmbedding n) := by cases a <;> rfl

/-- Adjacent-word shift in the typed grammar. -/
def AdjacentWord.shift {n : ℕ} (w : AdjacentWord n) : AdjacentWord (n+1) := w.map AdjacentGate.shift

/-- Adjacent-word widening in the typed grammar. -/
def AdjacentWord.initial {n : ℕ} (w : AdjacentWord n) : AdjacentWord (n+1) := w.map AdjacentGate.initial

@[simp] theorem AdjacentWord.toWord_shift {n : ℕ} (w : AdjacentWord n) :
    w.shift.toWord = relabel (shiftEmbedding n) w.toWord := by
  simp only [shift, toWord, relabel, List.map_map]
  congr 1
  funext a
  exact a.toGate_shift

@[simp] theorem AdjacentWord.toWord_initial {n : ℕ} (w : AdjacentWord n) :
    w.initial.toWord = relabel (initialEmbedding n) w.toWord := by
  simp only [initial, toWord, relabel, List.map_map]
  congr 1
  funext a
  exact a.toGate_initial

/-- The literal positive-power inverse of an adjacent primitive stays adjacent. -/
def AdjacentGate.inverseWord (d : ℕ) : {n : ℕ} → AdjacentGate n → AdjacentWord n
  | _, .scalar => List.replicate (2*d-1) .scalar
  | _, .H i => List.replicate 3 (.H i)
  | _, .S i => List.replicate (d-1) (.S i)
  | _, .CZ i => List.replicate (d-1) (.CZ i)

@[simp] theorem AdjacentGate.toWord_inverseWord {n : ℕ} (d : ℕ) (a : AdjacentGate n) :
    (a.inverseWord d).toWord = a.toGate.inverseWord d := by
  cases a <;> simp only [inverseWord, AdjacentWord.toWord, List.map_replicate,
    toGate, Gate.inverseWord]

/-- Reverse factors and replace each adjacent primitive by its inverse word. -/
def AdjacentWord.inverseWord {n : ℕ} (d : ℕ) (w : AdjacentWord n) : AdjacentWord n :=
  (w.reverse.map (AdjacentGate.inverseWord d)).flatten

@[simp] theorem AdjacentWord.toWord_inverseWord {n : ℕ} (d : ℕ) (w : AdjacentWord n) :
    (inverseWord d w).toWord = Circuit.inverseWord d w.toWord := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have hw : inverseWord d (a::w) = inverseWord d w ++ a.inverseWord d := by
      simp [inverseWord]
    rw [hw, toWord_append, ih, AdjacentGate.toWord_inverseWord, toWord_cons, Circuit.inverseWord_cons]

/-- With no wires, every available primitive is scalar and hence adjacent. -/
theorem isAdjacentWord_zero (w : Word 0) : IsAdjacentWord w := by
  intro a _
  cases a with
  | scalar => exact ⟨.scalar, rfl⟩
  | H i => exact Fin.elim0 i
  | S i => exact Fin.elim0 i
  | CZ i j hij => exact Fin.elim0 i

/-- At arity one, the primitive alphabet has no controlled-phase gate. -/
theorem isAdjacentWord_one (w : Word 1) : IsAdjacentWord w := by
  intro a _
  cases a with
  | scalar => exact ⟨.scalar, rfl⟩
  | H i => exact ⟨.H i, rfl⟩
  | S i => exact ⟨.S i, rfl⟩
  | CZ i j hij => exact (hij (Subsingleton.elim _ _)).elim

@[simp] theorem isAdjacentWord_nil {n : ℕ} : IsAdjacentWord ([] : Word n) := by
  intro a ha
  simp at ha

@[simp] theorem isAdjacentWord_cons {n : ℕ} (a : Gate n) (w : Word n) :
    IsAdjacentWord (a::w) ↔ a.IsAdjacent ∧ IsAdjacentWord w := by
  simp [IsAdjacentWord]

@[simp] theorem isAdjacentWord_append {n : ℕ} (u v : Word n) :
    IsAdjacentWord (u++v) ↔ IsAdjacentWord u ∧ IsAdjacentWord v := by
  simp only [IsAdjacentWord, List.mem_append, or_imp, forall_and]

@[simp] theorem Gate.isAdjacent_scalar {n : ℕ} : (Gate.scalar (n := n)).IsAdjacent := ⟨.scalar, rfl⟩
@[simp] theorem Gate.isAdjacent_H {n : ℕ} (i : Fin n) : (Gate.H i).IsAdjacent := ⟨.H i, rfl⟩
@[simp] theorem Gate.isAdjacent_S {n : ℕ} (i : Fin n) : (Gate.S i).IsAdjacent := ⟨.S i, rfl⟩
theorem Gate.isAdjacent_CZ {n : ℕ} (i : Fin n) (hij : i.castSucc ≠ i.succ) :
    (Gate.CZ i.castSucc i.succ hij).IsAdjacent := ⟨.CZ i, rfl⟩

/-- Adjacent circuits stay adjacent when an idle first wire is inserted. -/
theorem IsAdjacentWord.shift {n : ℕ} {w : Word n} (hw : IsAdjacentWord w) :
    IsAdjacentWord (relabel (shiftEmbedding n) w) := by
  obtain ⟨v, rfl⟩ := (isAdjacentWord_iff_exists w).mp hw
  rw [← AdjacentWord.toWord_shift]
  exact AdjacentWord.isAdjacent_toWord _

/-- Adjacent circuits stay adjacent when an idle last wire is inserted. -/
theorem IsAdjacentWord.initial {n : ℕ} {w : Word n} (hw : IsAdjacentWord w) :
    IsAdjacentWord (relabel (initialEmbedding n) w) := by
  obtain ⟨v, rfl⟩ := (isAdjacentWord_iff_exists w).mp hw
  rw [← AdjacentWord.toWord_initial]
  exact AdjacentWord.isAdjacent_toWord _

/-- Repeating an adjacent primitive produces an adjacent word. -/
theorem IsAdjacentWord.replicate {n : ℕ} {a : Gate n} (ha : a.IsAdjacent) (k : ℕ) :
    IsAdjacentWord (List.replicate k a) := by
  intro b hb
  have he := (List.mem_replicate.mp hb).2
  subst b
  exact ha

/-- Repeating an entire adjacent circuit preserves the alphabet. -/
theorem IsAdjacentWord.power {n : ℕ} {w : Word n} (hw : IsAdjacentWord w) (k : ℕ) :
    IsAdjacentWord (power w k) := by
  intro a ha
  obtain ⟨v, hv, ha⟩ := List.mem_flatten.mp ha
  have he := (List.mem_replicate.mp hv).2
  subst v
  exact hw a ha

end QuditClifford.Circuit
