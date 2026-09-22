import QuditClifford.AdjacentWireRewrites

/-!
# Replaying one-wire proofs in the adjacent presentation

A one-wire word cannot contain CZ. Every step of an existing one-wire exact
derivation can therefore be replayed on any selected wire, including its
intermediate words, without introducing nonadjacent generators.
-/

namespace QuditClifford.Circuit
variable {d n : ℕ}

/-- Placing an arbitrary one-wire word on a selected wire stays in the
canonical adjacent alphabet. No hypothesis on the source word is necessary. -/
theorem isAdjacentWord_singleWire (i : Fin n) (w : Word 1) :
    IsAdjacentWord (relabel (singleWireEmbedding i) w) := by
  intro a ha
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
  cases b with
  | scalar => exact ⟨.scalar, rfl⟩
  | H j => exact ⟨.H i, rfl⟩
  | S j => exact ⟨.S i, rfl⟩
  | CZ j k hjk => exact (hjk (Subsingleton.elim _ _)).elim

variable [NeZero d] (g : (ZMod d)ˣ)

/-- Replay every step of a one-wire exact derivation on any wire. This uses
syntactic relabeling and alphabet preservation, not a completeness assumption. -/
theorem adjacentDerives_singleWire (i : Fin n) {u v : Word 1} (h : Derives g u v) :
    AdjacentDerives g (relabel (singleWireEmbedding i) u)
      (relabel (singleWireEmbedding i) v) :=
  adjacentDerives_relabel g (singleWireEmbedding i)
    (fun w _ => isAdjacentWord_singleWire i w)
    (adjacentDerives_of_all_words_adjacent g isAdjacentWord_one h)

/-- The exact minus-omega scalar has the Figure 1 order relation at every arity,
including zero wires. -/
theorem adjacentDerives_scalar_order :
    AdjacentDerives (n := n) g (scalar (2*d)) [] :=
  .rule ⟨Or.inr .C0,
    IsAdjacentWord.replicate (Gate.isAdjacent_scalar (n := n)) (2*d), isAdjacentWord_nil⟩

/-- Addition of residue-valued S exponents, replayed from the one-wire C1 proof. -/
theorem adjacentDerives_Sexp_add (i : Fin n) (a b : ZMod d) :
    AdjacentDerives g (Sexp i a ++ Sexp i b) (Sexp i (a+b)) := by
  simpa only [relabel_append, relabel_Sexp, singleWireEmbedding, Function.Embedding.coeFn_mk]
    using adjacentDerives_singleWire g i (derives_Sexp_add g (0 : Fin 1) a b)

/-- The expanded unit multiplier is removed using the one-wire C3-at-zero proof. -/
theorem adjacentDerives_multiplier_one (i : Fin n) :
    AdjacentDerives g (multiplier (d := d) i 1) [] := by
  simpa only [relabel_multiplier, relabel_nil, singleWireEmbedding, Function.Embedding.coeFn_mk]
    using adjacentDerives_singleWire g i (derives_multiplier_one g (0 : Fin 1))

end QuditClifford.Circuit
