import QuditClifford.AdjacentTwoWireReplay
import QuditClifford.AdjacentPairEmbedding
import QuditClifford.ControlledXPauliRewrites

/-!
# Exact adjacent CZ Pauli pushing

The two-wire proof is replayed rule by rule into the canonical orientation,
then embedded at a neighboring pair. This preserves the complete restricted
derivation, rather than inferring a restricted proof from adjacent endpoints.
-/

namespace QuditClifford.Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ)

private theorem cz_two_adj : (Gate.CZ (0 : Fin 2) 1 (by decide)).IsAdjacent :=
  ⟨.CZ 0, rfl⟩

/-- Exact X pushing on the lower wire of an arbitrary neighboring pair. -/
theorem adjacentDerives_CZ_X_left_neighbor (hd : Odd d) (hg : orderOf g = d-1)
    (i : Fin (n+1)) :
    AdjacentDerives g ([.CZ i.castSucc i.succ (adjacent_ne i)] ++ X (d := d) i.castSucc)
      (X (d := d) i.castSucc ++ Z (d := d) i.succ ++ [.CZ i.castSucc i.succ (adjacent_ne i)]) := by
  letI : Fact (Odd d) := ⟨hd⟩
  letI : Fact (orderOf g = d-1) := ⟨hg⟩
  have h := adjacentDerives_of_twoWire g
    (by simp [cz_two_adj]) (by simp [cz_two_adj])
    (derives_CZ_X_left g hd hg (0 : Fin 2) 1 (by decide))
  simpa only [relabel_append, relabel_X, relabel_Z, relabel_cons, relabel_nil,
    Gate.relabel, adjacentPairEmbedding_zero, adjacentPairEmbedding_one]
    using adjacentDerives_pair g i h

/-- Exact X pushing on the upper wire of an arbitrary neighboring pair. -/
theorem adjacentDerives_CZ_X_right_neighbor (hd : Odd d) (hg : orderOf g = d-1)
    (i : Fin (n+1)) :
    AdjacentDerives g ([.CZ i.castSucc i.succ (adjacent_ne i)] ++ X (d := d) i.succ)
      (X (d := d) i.succ ++ Z (d := d) i.castSucc ++ [.CZ i.castSucc i.succ (adjacent_ne i)]) := by
  letI : Fact (Odd d) := ⟨hd⟩
  letI : Fact (orderOf g = d-1) := ⟨hg⟩
  have h := adjacentDerives_of_twoWire g
    (by simp [cz_two_adj]) (by simp [cz_two_adj])
    (derives_CZ_X_right g hd hg (0 : Fin 2) 1 (by decide))
  simpa only [relabel_append, relabel_X, relabel_Z, relabel_cons, relabel_nil,
    Gate.relabel, adjacentPairEmbedding_zero, adjacentPairEmbedding_one]
    using adjacentDerives_pair g i h

/-- Exact Z commutation on the lower wire of an arbitrary neighboring pair. -/
theorem adjacentDerives_CZ_Z_left_neighbor (hd : Odd d) (hg : orderOf g = d-1)
    (i : Fin (n+1)) :
    AdjacentDerives g ([.CZ i.castSucc i.succ (adjacent_ne i)] ++ Z (d := d) i.castSucc)
      (Z (d := d) i.castSucc ++ [.CZ i.castSucc i.succ (adjacent_ne i)]) := by
  letI : Fact (Odd d) := ⟨hd⟩
  letI : Fact (orderOf g = d-1) := ⟨hg⟩
  have h := adjacentDerives_of_twoWire g
    (by simp [cz_two_adj]) (by simp [cz_two_adj])
    (derives_CZ_Z_left g hd hg (0 : Fin 2) 1 (by decide))
  simpa only [relabel_append, relabel_Z, relabel_cons, relabel_nil,
    Gate.relabel, adjacentPairEmbedding_zero, adjacentPairEmbedding_one]
    using adjacentDerives_pair g i h

/-- Exact Z commutation on the upper wire of an arbitrary neighboring pair. -/
theorem adjacentDerives_CZ_Z_right_neighbor (hd : Odd d) (hg : orderOf g = d-1)
    (i : Fin (n+1)) :
    AdjacentDerives g ([.CZ i.castSucc i.succ (adjacent_ne i)] ++ Z (d := d) i.succ)
      (Z (d := d) i.succ ++ [.CZ i.castSucc i.succ (adjacent_ne i)]) := by
  letI : Fact (Odd d) := ⟨hd⟩
  letI : Fact (orderOf g = d-1) := ⟨hg⟩
  have h := adjacentDerives_of_twoWire g
    (by simp [cz_two_adj]) (by simp [cz_two_adj])
    (derives_CZ_Z_right g hd hg (0 : Fin 2) 1 (by decide))
  simpa only [relabel_append, relabel_Z, relabel_cons, relabel_nil,
    Gate.relabel, adjacentPairEmbedding_zero, adjacentPairEmbedding_one]
    using adjacentDerives_pair g i h

/-- The lower-wire X rule expressed using a canonical-adjacency certificate. -/
theorem adjacentDerives_CZ_X_left (hd : Odd d) (hg : orderOf g = d-1)
    (i j : Fin n) (hij : i ≠ j) (hadj : (Gate.CZ i j hij).IsAdjacent) :
    AdjacentDerives g ([.CZ i j hij] ++ X (d := d) i)
      (X (d := d) i ++ Z (d := d) j ++ [.CZ i j hij]) := by
  obtain ⟨a, ha⟩ := hadj
  cases a with
  | scalar => cases ha
  | H k => cases ha
  | S k => cases ha
  | @CZ m k =>
    cases m with
    | zero => exact Fin.elim0 k
    | succ m =>
      cases ha
      exact adjacentDerives_CZ_X_left_neighbor g hd hg k

/-- The upper-wire X rule expressed using a canonical-adjacency certificate. -/
theorem adjacentDerives_CZ_X_right (hd : Odd d) (hg : orderOf g = d-1)
    (i j : Fin n) (hij : i ≠ j) (hadj : (Gate.CZ i j hij).IsAdjacent) :
    AdjacentDerives g ([.CZ i j hij] ++ X (d := d) j)
      (X (d := d) j ++ Z (d := d) i ++ [.CZ i j hij]) := by
  obtain ⟨a, ha⟩ := hadj
  cases a with
  | scalar => cases ha
  | H k => cases ha
  | S k => cases ha
  | @CZ m k =>
    cases m with
    | zero => exact Fin.elim0 k
    | succ m =>
      cases ha
      exact adjacentDerives_CZ_X_right_neighbor g hd hg k

/-- The lower-wire Z rule expressed using a canonical-adjacency certificate. -/
theorem adjacentDerives_CZ_Z_left (hd : Odd d) (hg : orderOf g = d-1)
    (i j : Fin n) (hij : i ≠ j) (hadj : (Gate.CZ i j hij).IsAdjacent) :
    AdjacentDerives g ([.CZ i j hij] ++ Z (d := d) i)
      (Z (d := d) i ++ [.CZ i j hij]) := by
  obtain ⟨a, ha⟩ := hadj
  cases a with
  | scalar => cases ha
  | H k => cases ha
  | S k => cases ha
  | @CZ m k =>
    cases m with
    | zero => exact Fin.elim0 k
    | succ m =>
      cases ha
      exact adjacentDerives_CZ_Z_left_neighbor g hd hg k

/-- The upper-wire Z rule expressed using a canonical-adjacency certificate. -/
theorem adjacentDerives_CZ_Z_right (hd : Odd d) (hg : orderOf g = d-1)
    (i j : Fin n) (hij : i ≠ j) (hadj : (Gate.CZ i j hij).IsAdjacent) :
    AdjacentDerives g ([.CZ i j hij] ++ Z (d := d) j)
      (Z (d := d) j ++ [.CZ i j hij]) := by
  obtain ⟨a, ha⟩ := hadj
  cases a with
  | scalar => cases ha
  | H k => cases ha
  | S k => cases ha
  | @CZ m k =>
    cases m with
    | zero => exact Fin.elim0 k
    | succ m =>
      cases ha
      exact adjacentDerives_CZ_Z_right_neighbor g hd hg k

end QuditClifford.Circuit
