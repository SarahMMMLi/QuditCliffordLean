import QuditClifford.AdjacentOneWireRewrites
import QuditClifford.AdjacentNormalCircuit

/-!
# Explicit Pauli erasure within the adjacent source alphabet

Each generating step is a named-wire symplectic helper rule whose two words
are canonical adjacent circuits. This guards the complete derivation, not
just its endpoints. Exact lifting back into `AdjacentDerives` is separate.
-/
namespace QuditClifford.Circuit
variable {d n m : ℕ} [NeZero d]

/-- Scalar/Pauli erasure restricted to adjacent source circuits. -/
def AdjacentSymplecticRules (g : (ZMod d)ˣ) (u v : Word n) : Prop :=
  SymplecticRules g u v ∧ IsAdjacentWord u ∧ IsAdjacentWord v

/-- The restricted erased relation has its own contextual closure. -/
def AdjacentSymplecticDerives (g : (ZMod d)ˣ) : Word n → Word n → Prop :=
  Presentation.Derives (AdjacentSymplecticRules g)

theorem adjacentDerives_symplectic (g : (ZMod d)ˣ) {u v : Word n}
    (h : AdjacentDerives g u v) : AdjacentSymplecticDerives g u v :=
  h.mono (fun _ _ hr => .rule ⟨Or.inl (Or.inl hr.1), hr.2⟩)

theorem AdjacentSymplecticDerives.toSymplecticDerives (g : (ZMod d)ˣ) {u v : Word n}
    (h : AdjacentSymplecticDerives g u v) : SymplecticDerives g u v :=
  h.mono (fun _ _ hr => .rule hr.1)

theorem AdjacentSymplecticDerives.isAdjacent_iff (g : (ZMod d)ˣ) {u v : Word n}
    (h : AdjacentSymplecticDerives g u v) : IsAdjacentWord u ↔ IsAdjacentWord v := by
  induction h with
  | refl w => rfl
  | rule h => exact iff_of_true h.2.1 h.2.2
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | context l r h ih => simp only [isAdjacentWord_append, ih]

theorem adjacentSymplecticDerives_of_all_words_adjacent (g : (ZMod d)ˣ)
    (ha : ∀ w : Word n, IsAdjacentWord w) {u v : Word n} (h : SymplecticDerives g u v) :
    AdjacentSymplecticDerives g u v :=
  h.mono (fun u v hr => .rule ⟨hr, ha u, ha v⟩)

theorem adjacentSymplecticDerives_relabel (g : (ZMod d)ˣ) (ι : Fin n ↪ Fin m)
    (hι : ∀ w : Word n, IsAdjacentWord w → IsAdjacentWord (relabel ι w))
    {u v : Word n} (h : AdjacentSymplecticDerives g u v) :
    AdjacentSymplecticDerives g (relabel ι u) (relabel ι v) :=
  h.map (Gate.relabel ι) (fun u v hr =>
    .rule ⟨hr.1.relabel g ι, hι u hr.2.1, hι v hr.2.2⟩)

theorem adjacentSymplecticDerives_shift (g : (ZMod d)ˣ) {u v : Word n}
    (h : AdjacentSymplecticDerives g u v) :
    AdjacentSymplecticDerives g (relabel (shiftEmbedding n) u)
      (relabel (shiftEmbedding n) v) :=
  adjacentSymplecticDerives_relabel g _ (fun _ hw => hw.shift) h

theorem adjacentSymplecticDerives_initial (g : (ZMod d)ˣ) {u v : Word n}
    (h : AdjacentSymplecticDerives g u v) :
    AdjacentSymplecticDerives g (relabel (initialEmbedding n) u)
      (relabel (initialEmbedding n) v) :=
  adjacentSymplecticDerives_relabel g _ (fun _ hw => hw.initial) h

/-- All one-wire erased proofs can be replayed on a chosen source wire. -/
theorem adjacentSymplecticDerives_singleWire (g : (ZMod d)ˣ) (i : Fin n)
    {u v : Word 1} (h : SymplecticDerives g u v) :
    AdjacentSymplecticDerives g (relabel (singleWireEmbedding i) u)
      (relabel (singleWireEmbedding i) v) :=
  adjacentSymplecticDerives_relabel g _ (fun w _ => isAdjacentWord_singleWire i w)
    (adjacentSymplecticDerives_of_all_words_adjacent g isAdjacentWord_one h)

variable [Fact d.Prime]

/-- Restricted erased derivations preserve the established exponent action. -/
theorem adjacentSymplecticDerives_sound (hd : Odd d) (g : (ZMod d)ˣ) {u v : Word n}
    (h : AdjacentSymplecticDerives g u v) :
    ∀ p, symplecticAction d u p = symplecticAction d v p :=
  symplecticDerives_sound hd g (h.toSymplecticDerives g)

end QuditClifford.Circuit
