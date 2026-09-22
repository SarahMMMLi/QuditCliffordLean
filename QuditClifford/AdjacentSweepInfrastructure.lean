import QuditClifford.AdjacentXNormalPushH
import QuditClifford.AdjacentThreeWireShuffle

/-! # Restricted context and embedding lemmas for recursive box sweeps -/
namespace QuditClifford.Circuit
variable {d n : ℕ} [NeZero d] (g : (ZMod d)ˣ)

omit [NeZero d] in
/-- The right member of the first adjacent pair is the head of its shifted tail. -/
theorem relabel_pair_singleWire_one (w : Word 1) :
    relabel (adjacentPairEmbedding (0 : Fin (n+1)))
      (relabel (singleWireEmbedding (1 : Fin 2)) w) =
    relabel (shiftEmbedding (n+1)) (relabel (singleWireEmbedding (0 : Fin (n+1))) w) := by
  rw [← relabel_trans, ← relabel_trans]
  congr 1

/-- H on the head wire moves past any adjacent circuit on the trailing wires. -/
theorem adjacentDerives_H_head_tail (w : Word n) (hw : IsAdjacentWord w) :
    AdjacentDerives g (relabel (shiftEmbedding n) w ++ [.H 0])
      ([.H 0] ++ relabel (shiftEmbedding n) w) := by
  apply adjacentDerives_word_gate_commute g _ _ hw.shift (Gate.isAdjacent_H 0)
  intro a ha
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
  rw [Gate.support_relabel]
  change Disjoint (Finset.map (shiftEmbedding n) b.support) {0}
  rw [Finset.disjoint_singleton_right]
  intro h
  obtain ⟨j, _, hj⟩ := Finset.mem_map.mp h
  exact Fin.succ_ne_zero j hj

end QuditClifford.Circuit
