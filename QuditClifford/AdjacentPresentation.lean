import QuditClifford.AdjacentCircuit
import QuditClifford.OneQuditCompleteness

/-!
# Figure 1 on the adjacent circuit alphabet

The paper's tensor generators act on one wire or two neighboring wires.
Figure 4 T7 defines a remote CZ by a SWAP expansion. Independent remote CZ
letters in `Circuit.Gate` are useful for matrix statements but enlarge the
rewrite-completeness target beyond the source presentation.

Here both sides of every generating equation must be adjacent words. Contexts
remain explicit. In particular, derivations starting at an adjacent word
cannot introduce an independent nonadjacent CZ letter. Completeness is proved
below only at arities zero and one.
-/

namespace QuditClifford.Circuit
variable {d n : ℕ} [NeZero d]

/-- The actual local equations restricted to the source's adjacent alphabet. -/
def AdjacentRules (g : (ZMod d)ˣ) (u v : Word n) : Prop :=
  Rules g u v ∧ IsAdjacentWord u ∧ IsAdjacentWord v

/-- Contextual rewriting by adjacent instances of Figure 1 and structural equations. -/
def AdjacentDerives (g : (ZMod d)ˣ) : Word n → Word n → Prop :=
  Presentation.Derives (AdjacentRules g)

/-- Forgetting the alphabet restriction gives a valid named-wire derivation. -/
theorem AdjacentDerives.toDerives (g : (ZMod d)ˣ) {u v : Word n}
    (h : AdjacentDerives g u v) : Derives g u v :=
  h.mono (fun _ _ hr => .rule hr.1)

private theorem adjacent_append_iff (u v : Word n) :
    IsAdjacentWord (u ++ v) ↔ IsAdjacentWord u ∧ IsAdjacentWord v := by
  simp only [IsAdjacentWord, List.mem_append, or_imp, forall_and]

/-- Every intermediate word reachable from an adjacent word is still adjacent. -/
theorem AdjacentDerives.isAdjacent_iff (g : (ZMod d)ˣ) {u v : Word n}
    (h : AdjacentDerives g u v) : IsAdjacentWord u ↔ IsAdjacentWord v := by
  induction h with
  | refl w => rfl
  | rule h => exact iff_of_true h.2.1 h.2.2
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | context l r h ih => simp only [adjacent_append_iff, ih]

/-- If an entire arity has no remote CZ letters, all existing derivations
at that arity already use adjacent primitive words. -/
theorem adjacentDerives_of_all_words_adjacent (g : (ZMod d)ˣ)
    (ha : ∀ w : Word n, IsAdjacentWord w) {u v : Word n} (h : Derives g u v) :
    AdjacentDerives g u v :=
  h.mono (fun u v hr => .rule ⟨hr, ha u, ha v⟩)

/-- An embedding is permitted when it preserves the canonical adjacent
alphabet. Unlike arbitrary named-wire relabeling, this has an explicit
adjacency obligation. -/
theorem adjacentDerives_relabel {m : ℕ} (g : (ZMod d)ˣ) (ι : Fin n ↪ Fin m)
    (hι : ∀ w : Word n, IsAdjacentWord w → IsAdjacentWord (relabel ι w))
    {u v : Word n} (h : AdjacentDerives g u v) :
    AdjacentDerives g (relabel ι u) (relabel ι v) :=
  h.map (Gate.relabel ι) (fun u v hr =>
    .rule ⟨hr.1.relabel g ι, hι u hr.2.1, hι v hr.2.2⟩)

/-- Tensoring an idle wire on the left preserves source-restricted derivations. -/
theorem adjacentDerives_shift (g : (ZMod d)ˣ) {u v : Word n}
    (h : AdjacentDerives g u v) :
    AdjacentDerives g (relabel (shiftEmbedding n) u) (relabel (shiftEmbedding n) v) :=
  adjacentDerives_relabel g (shiftEmbedding n) (fun _ hw => hw.shift) h

/-- Tensoring an idle wire on the right preserves source-restricted derivations. -/
theorem adjacentDerives_initial (g : (ZMod d)ˣ) {u v : Word n}
    (h : AdjacentDerives g u v) :
    AdjacentDerives g (relabel (initialEmbedding n) u) (relabel (initialEmbedding n) v) :=
  adjacentDerives_relabel g (initialEmbedding n) (fun _ hw => hw.initial) h

/-- Exact completeness for the adjacent alphabet and its own contextual relation. -/
def AdjacentFigure1Complete (g : (ZMod d)ˣ) : Prop :=
  ∀ u v : Word n, IsAdjacentWord u → IsAdjacentWord v →
    denote d u = denote d v → AdjacentDerives g u v

/-- Source-faithful target for Theorem 4.10, with Figure 1's exact minus-omega
scalar. `Circuit.mainTheorem` in `AdjacentCompleteness.lean` proves it at every arity. -/
def MainTheorem (d : ℕ) [NeZero d] : Prop :=
  d.Prime → Odd d → ∀ g : (ZMod d)ˣ, orderOf g = d-1 →
    ∀ n, Figure1Sound (n := n) g ∧ AdjacentFigure1Complete (n := n) g

variable [Fact d.Prime]

/-- The source-restricted derivations retain the previously proved exact soundness. -/
theorem adjacentDerives_sound (hd : Odd d) (g : (ZMod d)ˣ) {u v : Word n}
    (h : AdjacentDerives g u v) : denote d u = denote d v :=
  figure1_sound hd g u v (h.toDerives g)

private theorem all_words_adjacent_of_subsingleton [Subsingleton (Fin n)] (w : Word n) :
    IsAdjacentWord w := by
  intro a _
  cases a with
  | scalar => exact ⟨.scalar, rfl⟩
  | H i => exact ⟨.H i, rfl⟩
  | S i => exact ⟨.S i, rfl⟩
  | CZ i j hij => exact (hij (Subsingleton.elim _ _)).elim

/-- The scalar-only completeness proof is also a proof in the adjacent presentation. -/
theorem adjacentFigure1Complete_zero (hd : Odd d) (g : (ZMod d)ˣ) :
    AdjacentFigure1Complete (n := 0) g := by
  intro u v _ _ huv
  exact adjacentDerives_of_all_words_adjacent g all_words_adjacent_of_subsingleton
    (zero_wire_complete hd g u v huv)

/-- The proved one-qudit theorem needs no nonadjacent intermediate letters,
so it establishes the paper's restricted presentation as well. -/
theorem adjacentFigure1Complete_one (g : (ZMod d)ˣ) [Fact (Odd d)]
    [Fact (orderOf g = d-1)] : AdjacentFigure1Complete (n := 1) g := by
  intro u v _ _ huv
  exact adjacentDerives_of_all_words_adjacent g all_words_adjacent_of_subsingleton
    (figure1Complete_one g u v huv)

end QuditClifford.Circuit
