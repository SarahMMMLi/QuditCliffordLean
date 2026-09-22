import QuditClifford.AdjacentTwoWireSyntax
import QuditClifford.AdjacentSymplecticRewrites
import QuditClifford.AdjacentTwoWireRewrites

/-!
# Replaying two-wire helper derivations in the adjacent presentation

Every two-wire Figure 1 schema is either in its printed orientation or its
wire reflection. Reflection is implemented by the derived SWAP, rather than
silently added as a primitive rule. The three-wire schemas have no instances
on two wires.
-/
namespace QuditClifford.Circuit
variable {d : ℕ} [NeZero d] (g : (ZMod d)ˣ)

private theorem cz_adj : (Gate.CZ (0 : Fin 2) 1 (by decide)).IsAdjacent := ⟨.CZ 0, rfl⟩

omit [NeZero d] in
private theorem swap_adj : IsAdjacentWord (SWAP (d := d) (0 : Fin 2) 1 (by decide)) :=
  isAdjacentWord_SWAP_neighbor 0

private theorem cx_adj : IsAdjacentWord (CX (0 : Fin 2) 1 (by decide)) :=
  isAdjacentWord_CX_neighbor 0

/-- A two-wire rule is local in either the printed orientation or its reflection. -/
private theorem figure1_two_local {u v : Word 2} (h : Figure1Rule g u v) :
    (IsAdjacentWord u ∧ IsAdjacentWord v) ∨
      (IsAdjacentWord (relabel flipTwo u) ∧ IsAdjacentWord (relabel flipTwo v)) := by
  cases h with
  | C0 => left; simp
  | C1 i => left; exact ⟨IsAdjacentWord.replicate (Gate.isAdjacent_S i) _, isAdjacentWord_nil⟩
  | C2 i => left; simp
  | C3 i k => left; exact ⟨(isAdjacentWord_multiplier _ _).power _, isAdjacentWord_multiplier _ _⟩
  | C4 i => left; simp
  | C5 i => left; simp
  | C6 i j hij =>
      fin_cases i <;> fin_cases j
      all_goals try exact (hij rfl).elim
      · left; exact ⟨IsAdjacentWord.replicate cz_adj _, isAdjacentWord_nil⟩
      · right; simp only [relabel_replicate, relabel_nil, Gate.relabel, flipTwo_zero, flipTwo_one]
        exact ⟨IsAdjacentWord.replicate cz_adj _, isAdjacentWord_nil⟩
  | C7 i j hij =>
      fin_cases i <;> fin_cases j
      all_goals try exact (hij rfl).elim
      · left; simp only [isAdjacentWord_append, swap_adj, isAdjacentWord_nil, and_self]
        exact ⟨swap_adj, trivial⟩
      · right; simp only [relabel_append, relabel_SWAP, flipTwo_zero, flipTwo_one,
          relabel_nil, isAdjacentWord_append, swap_adj, isAdjacentWord_nil, and_self]
        exact ⟨swap_adj, trivial⟩
  | C8 i j hij =>
      fin_cases i <;> fin_cases j
      all_goals try exact (hij rfl).elim
      · left; simp [cz_adj]
      · right; simp [Gate.relabel, cz_adj]
  | C9 i j hij =>
      fin_cases i <;> fin_cases j
      all_goals try exact (hij rfl).elim
      · left; simp only [isAdjacentWord_append, isAdjacentWord_cons, isAdjacentWord_nil,
          cz_adj, isAdjacentWord_multiplier, true_and, and_true]
        exact ⟨cz_adj, IsAdjacentWord.replicate cz_adj _⟩
      · right; simp only [relabel_append, relabel_cons, relabel_nil, relabel_multiplier,
          relabel_replicate, Gate.relabel, flipTwo_zero, flipTwo_one,
          isAdjacentWord_append, isAdjacentWord_cons, isAdjacentWord_nil,
          cz_adj, isAdjacentWord_multiplier, true_and, and_true]
        exact ⟨cz_adj, IsAdjacentWord.replicate cz_adj _⟩
  | C10 i j hij =>
      fin_cases i <;> fin_cases j
      all_goals try exact (hij rfl).elim
      · left; simp [swap_adj]
      · right; simp [Gate.relabel, swap_adj]
  | C11 i j hij =>
      fin_cases i <;> fin_cases j
      all_goals try exact (hij rfl).elim
      · left; simp [swap_adj]
      · right; simp [Gate.relabel, swap_adj]
  | C12 i j hij =>
      fin_cases i <;> fin_cases j
      all_goals try exact (hij rfl).elim
      · left; simp [cx_adj, IsAdjacentWord.power cx_adj, cz_adj]
      · right; simp [Gate.relabel, cx_adj, IsAdjacentWord.power cx_adj, cz_adj]
  | C13 i j k hij hjk hik =>
      fin_cases i <;> fin_cases j <;> fin_cases k
      all_goals first | exact (hij rfl).elim | exact (hjk rfl).elim | exact (hik rfl).elim
  | C14 i j k hij hjk hik =>
      fin_cases i <;> fin_cases j <;> fin_cases k
      all_goals first | exact (hij rfl).elim | exact (hjk rfl).elim | exact (hik rfl).elim
  | C15 i j k hij hjk hik =>
      fin_cases i <;> fin_cases j <;> fin_cases k
      all_goals first | exact (hij rfl).elim | exact (hjk rfl).elim | exact (hik rfl).elim

/-- The only nonlocal ingredient needed for orienting the two-wire schemas
is an actual adjacent derivation of wire reflection. -/
private theorem orientTwo_figure1_of_reflection
    (hr : ∀ {u v : Word 2}, IsAdjacentWord u → IsAdjacentWord v → AdjacentDerives g u v →
      AdjacentDerives g (reflectTwoWord u) (reflectTwoWord v))
    {u v : Word 2} (h : Figure1Rule g u v) :
    AdjacentDerives g (orientTwoWord u) (orientTwoWord v) := by
  rcases figure1_two_local g h with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · rw [orientTwoWord_eq_of_adjacent u hu, orientTwoWord_eq_of_adjacent v hv]
    exact .rule ⟨Or.inr h, hu, hv⟩
  · have he := hr hu hv (.rule ⟨Or.inr (h.relabel g flipTwo), hu, hv⟩)
    simpa only [reflectTwoWord_relabel_flip] using he

private theorem orientTwo_structural {u v : Word 2} (h : Structural u v) :
    AdjacentDerives g (orientTwoWord u) (orientTwoWord v) := by
  cases h with
  | CZ_symmetry i j hij => exact .refl _
  | disjoint a b hab =>
      apply Presentation.Derives.rule
      refine ⟨Or.inl (.disjoint (orientTwoGate a) (orientTwoGate b) ?_),
        orientTwoWord_isAdjacent _, orientTwoWord_isAdjacent _⟩
      simpa only [orientTwoGate_support] using hab

variable [Fact d.Prime] [Fact (Odd d)] [Fact (orderOf g = d-1)]

/-- Every two-wire helper derivation replays after canonical CZ orientation.
The proof checks every schema and uses derived reflection for reversed ones. -/
theorem adjacentDerives_orientTwoWord {u v : Word 2} (h : Derives g u v) :
    AdjacentDerives g (orientTwoWord u) (orientTwoWord v) :=
  h.map orientTwoGate (fun _ _ hr => hr.elim (orientTwo_structural g)
    (orientTwo_figure1_of_reflection g (adjacentDerives_reflectTwoWord g)))

/-- For canonical two-wire endpoints the original words themselves are related
by the source presentation. Every intermediate step is replayed, not assumed. -/
theorem adjacentDerives_of_twoWire {u v : Word 2}
    (hu : IsAdjacentWord u) (hv : IsAdjacentWord v) (h : Derives g u v) :
    AdjacentDerives g u v := by
  have he := adjacentDerives_orientTwoWord g h
  simpa only [orientTwoWord_eq_of_adjacent u hu, orientTwoWord_eq_of_adjacent v hv] using he

/-- The exact helper and source relations agree on canonical two-wire circuits. -/
theorem adjacentDerives_iff_twoWire {u v : Word 2}
    (hu : IsAdjacentWord u) (hv : IsAdjacentWord v) :
    AdjacentDerives g u v ↔ Derives g u v :=
  ⟨AdjacentDerives.toDerives g, adjacentDerives_of_twoWire g hu hv⟩

private theorem orientTwo_symplecticRules {u v : Word 2} (h : SymplecticRules g u v) :
    AdjacentSymplecticDerives g (orientTwoWord u) (orientTwoWord v) := by
  rcases h with (he | ⟨rfl, rfl⟩) | ⟨i, (rfl | rfl), rfl⟩
  · exact adjacentDerives_symplectic g (adjacentDerives_orientTwoWord g (.rule he))
  · exact .rule ⟨Or.inl (Or.inr ⟨rfl, rfl⟩), by simp [orientTwoGate], by simp⟩
  · simp only [orientTwoWord_X, orientTwoWord_nil]
    exact .rule ⟨Or.inr ⟨i, Or.inl rfl, rfl⟩, isAdjacentWord_X i, isAdjacentWord_nil⟩
  · simp only [orientTwoWord_Z, orientTwoWord_nil]
    exact .rule ⟨Or.inr ⟨i, Or.inr rfl, rfl⟩, isAdjacentWord_Z i, isAdjacentWord_nil⟩

/-- Scalar/Pauli-erased two-wire helper proofs also replay step by step. -/
theorem adjacentSymplecticDerives_orientTwoWord {u v : Word 2}
    (h : SymplecticDerives g u v) :
    AdjacentSymplecticDerives g (orientTwoWord u) (orientTwoWord v) :=
  h.map orientTwoGate (fun _ _ hr => orientTwo_symplecticRules g hr)

/-- Replay an erased box proof with canonical two-wire endpoints. -/
theorem adjacentSymplecticDerives_of_twoWire {u v : Word 2}
    (hu : IsAdjacentWord u) (hv : IsAdjacentWord v) (h : SymplecticDerives g u v) :
    AdjacentSymplecticDerives g u v := by
  have he := adjacentSymplecticDerives_orientTwoWord g h
  simpa only [orientTwoWord_eq_of_adjacent u hu, orientTwoWord_eq_of_adjacent v hv] using he

/-- The erased helper and source relations agree on canonical two-wire circuits. -/
theorem adjacentSymplecticDerives_iff_twoWire {u v : Word 2}
    (hu : IsAdjacentWord u) (hv : IsAdjacentWord v) :
    AdjacentSymplecticDerives g u v ↔ SymplecticDerives g u v :=
  ⟨AdjacentSymplecticDerives.toSymplecticDerives g, adjacentSymplecticDerives_of_twoWire g hu hv⟩

end QuditClifford.Circuit
