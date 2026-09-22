import QuditClifford.AdjacentPresentation

/-!
# Embedding two-wire derivations at any neighboring pair

The embedding sends the canonical two-wire CZ to the selected canonical
adjacent CZ. Thus every intermediate word of a restricted two-wire proof
can be replayed in a larger register, with no alphabet-coherence assumption.
-/
namespace QuditClifford.Circuit
variable {d n : ℕ}

/-- Place a two-wire register at neighboring positions `i` and `i+1`. -/
def adjacentPairEmbedding (i : Fin (n+1)) : Fin 2 ↪ Fin (n+2) where
  toFun q := if q=0 then i.castSucc else i.succ
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b
    · rfl
    · exact ((adjacent_ne i) (by simpa using h)).elim
    · exact ((adjacent_ne i) (by simpa using h.symm)).elim
    · rfl

@[simp] theorem adjacentPairEmbedding_zero (i : Fin (n+1)) :
    adjacentPairEmbedding i 0=i.castSucc := by simp [adjacentPairEmbedding]

@[simp] theorem adjacentPairEmbedding_one (i : Fin (n+1)) :
    adjacentPairEmbedding i 1=i.succ := by simp [adjacentPairEmbedding]

/-- A canonical two-wire primitive remains canonical and adjacent under the
neighboring-pair embedding. -/
theorem Gate.isAdjacent_relabel_adjacentPair {a : Gate 2} (ha : a.IsAdjacent)
    (i : Fin (n+1)) : (a.relabel (adjacentPairEmbedding i)).IsAdjacent := by
  obtain ⟨b, rfl⟩ := ha
  cases b with
  | scalar => exact Gate.isAdjacent_scalar
  | H j => exact Gate.isAdjacent_H _
  | S j => exact Gate.isAdjacent_S _
  | CZ j =>
    have hj : j=0 := Fin.ext (by omega)
    subst j
    simpa only [AdjacentGate.toGate, Gate.relabel, adjacentPairEmbedding_zero,
      adjacentPairEmbedding_one] using Gate.isAdjacent_CZ i (adjacent_ne i)

/-- Every letter of an embedded canonical two-wire word stays adjacent. -/
theorem IsAdjacentWord.relabel_adjacentPair {w : Word 2} (hw : IsAdjacentWord w)
    (i : Fin (n+1)) : IsAdjacentWord (relabel (adjacentPairEmbedding i) w) := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  exact Gate.isAdjacent_relabel_adjacentPair (hw b hb) i

variable [NeZero d] (g : (ZMod d)ˣ)

/-- Replay a restricted two-wire derivation at any neighboring pair. The
adjacency proof applies to every intermediate rule instance. -/
theorem adjacentDerives_pair (i : Fin (n+1)) {u v : Word 2}
    (h : AdjacentDerives g u v) :
    AdjacentDerives g (relabel (adjacentPairEmbedding i) u)
      (relabel (adjacentPairEmbedding i) v) :=
  adjacentDerives_relabel g (adjacentPairEmbedding i)
    (fun _ hw => hw.relabel_adjacentPair i) h

end QuditClifford.Circuit
