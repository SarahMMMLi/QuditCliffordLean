import QuditClifford.AdjacentSymplecticRewrites

/-!
# Embedding derivations at three consecutive wires

The arithmetic embedding preserves the two canonical adjacent CZ locations.
Consequently every intermediate word of an exact or Pauli-erased restricted
three-wire derivation remains in the adjacent source alphabet.
-/
namespace QuditClifford.Circuit
variable {d n : ℕ}

/-- Place three wires at positions `i`, `i+1`, and `i+2`. -/
def adjacentTripleEmbedding (i : Fin (n+1)) : Fin 3 ↪ Fin (n+3) where
  toFun q := ⟨i.val+q.val, by omega⟩
  inj' := by
    intro a b h
    apply Fin.ext
    have hv := congrArg Fin.val h
    dsimp only at hv
    omega

@[simp] theorem adjacentTripleEmbedding_zero (i : Fin (n+1)) :
    adjacentTripleEmbedding i 0=i.castSucc.castSucc := by
  apply Fin.ext
  simp [adjacentTripleEmbedding]

@[simp] theorem adjacentTripleEmbedding_one (i : Fin (n+1)) :
    adjacentTripleEmbedding i 1=i.succ.castSucc := by
  apply Fin.ext
  simp [adjacentTripleEmbedding]

@[simp] theorem adjacentTripleEmbedding_two (i : Fin (n+1)) :
    adjacentTripleEmbedding i 2=i.succ.succ := by
  apply Fin.ext
  simp [adjacentTripleEmbedding]

/-- Both canonical edges of a three-wire register remain canonical edges. -/
theorem Gate.isAdjacent_relabel_adjacentTriple {a : Gate 3} (ha : a.IsAdjacent)
    (i : Fin (n+1)) : (a.relabel (adjacentTripleEmbedding i)).IsAdjacent := by
  obtain ⟨b, rfl⟩ := ha
  cases b with
  | scalar => exact Gate.isAdjacent_scalar
  | H j => exact Gate.isAdjacent_H _
  | S j => exact Gate.isAdjacent_S _
  | CZ j =>
    fin_cases j
    · simpa only [AdjacentGate.toGate, Gate.relabel, adjacentTripleEmbedding_zero,
        adjacentTripleEmbedding_one] using
        Gate.isAdjacent_CZ i.castSucc (adjacent_ne i.castSucc)
    · simpa only [AdjacentGate.toGate, Gate.relabel, adjacentTripleEmbedding_one,
        adjacentTripleEmbedding_two] using
        Gate.isAdjacent_CZ i.succ (adjacent_ne i.succ)

/-- Every letter of an embedded adjacent three-wire word stays adjacent. -/
theorem IsAdjacentWord.relabel_adjacentTriple {w : Word 3} (hw : IsAdjacentWord w)
    (i : Fin (n+1)) : IsAdjacentWord (relabel (adjacentTripleEmbedding i) w) := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  exact Gate.isAdjacent_relabel_adjacentTriple (hw b hb) i

variable [NeZero d] (g : (ZMod d)ˣ)

/-- Replay an exact restricted three-wire derivation at consecutive wires. -/
theorem adjacentDerives_triple (i : Fin (n+1)) {u v : Word 3}
    (h : AdjacentDerives g u v) :
    AdjacentDerives g (relabel (adjacentTripleEmbedding i) u)
      (relabel (adjacentTripleEmbedding i) v) :=
  adjacentDerives_relabel g (adjacentTripleEmbedding i)
    (fun _ hw => hw.relabel_adjacentTriple i) h

/-- Replay a restricted Pauli-erased three-wire derivation at consecutive wires. -/
theorem adjacentSymplecticDerives_triple (i : Fin (n+1)) {u v : Word 3}
    (h : AdjacentSymplecticDerives g u v) :
    AdjacentSymplecticDerives g (relabel (adjacentTripleEmbedding i) u)
      (relabel (adjacentTripleEmbedding i) v) :=
  adjacentSymplecticDerives_relabel g (adjacentTripleEmbedding i)
    (fun _ hw => hw.relabel_adjacentTriple i) h

end QuditClifford.Circuit
