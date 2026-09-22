import QuditClifford.AdjacentPresentation

/-!
# SWAP transport in the source's adjacent presentation

These derivations use only canonical adjacent CZ letters. Transport from the
second wire follows from C7 and the printed C10/C11 orientation; no reversed
CZ spelling, arbitrary permutation of rule wires, or semantic equality is used.
-/

namespace QuditClifford.Circuit
variable {d n : ℕ} [NeZero d]
variable (g : (ZMod d)ˣ)

private theorem adjacent_nil : IsAdjacentWord ([] : Word n) := by simp [IsAdjacentWord]

private theorem adjacent_singleton {a : Gate n} (ha : a.IsAdjacent) :
    IsAdjacentWord [a] := by simpa only [IsAdjacentWord, List.mem_singleton, forall_eq] using ha

private theorem adjacent_append {u v : Word n} (hu : IsAdjacentWord u) (hv : IsAdjacentWord v) :
    IsAdjacentWord (u++v) := by
  intro a ha
  exact (List.mem_append.mp ha).elim (hu a) (hv a)

private theorem adjacent_replicate {a : Gate n} (ha : a.IsAdjacent) (k : ℕ) :
    IsAdjacentWord (List.replicate k a) := by
  intro b hb
  rw [(List.mem_replicate.mp hb).2]
  exact ha

private theorem adjacent_power {w : Word n} (hw : IsAdjacentWord w) (k : ℕ) :
    IsAdjacentWord (power w k) := by
  intro a ha
  obtain ⟨v, hv, hav⟩ := List.mem_flatten.mp ha
  have hvw : v=w := (List.mem_replicate.mp hv).2
  exact hw a (hvw ▸ hav)

omit [NeZero d] in
/-- The literal expanded SWAP stays in the adjacent alphabet. -/
theorem isAdjacentWord_SWAP (i j : Fin n) (hij : i ≠ j)
    (hadj : (Gate.CZ i j hij).IsAdjacent) : IsAdjacentWord (SWAP (d := d) i j hij) := by
  apply adjacent_append
  · exact adjacent_replicate ⟨.scalar, rfl⟩ _
  · apply adjacent_power
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact hadj
    · exact ⟨.H i, rfl⟩
    · exact ⟨.H j, rfl⟩

/-- C7, as a derivation whose entire rule instance has adjacent letters. -/
theorem adjacentDerives_SWAP_sq (i j : Fin n) (hij : i ≠ j)
    (hadj : (Gate.CZ i j hij).IsAdjacent) :
    AdjacentDerives g (SWAP (d := d) i j hij ++ SWAP (d := d) i j hij) [] :=
  .rule ⟨Or.inr (.C7 i j hij),
    adjacent_append (isAdjacentWord_SWAP i j hij hadj) (isAdjacentWord_SWAP i j hij hadj),
    adjacent_nil⟩

/-- Reverse the direction of transport through an involution using explicit
word contexts. This lemma is valid for any adjacent derivations supplied. -/
theorem AdjacentDerives.reverse_involution_transport {t a b : Word n}
    (ht : AdjacentDerives g (t++t) [])
    (hab : AdjacentDerives g (t++a) (b++t)) :
    AdjacentDerives g (t++b) (a++t) := by
  have h₁ := ht.symm.append_left (t++b)
  have h₂ := hab.symm.context t t
  have h₃ := ht.append_right (a++t)
  have h₁' : AdjacentDerives g (t++b) (t++(b++t)++t) := by
    simpa only [List.append_assoc, List.append_nil] using h₁
  have h₃' : AdjacentDerives g (t++(t++a)++t) (a++t) := by
    simpa only [List.append_assoc, List.nil_append] using h₃
  exact h₁'.trans (h₂.trans h₃')

/-- C10 in its printed orientation. -/
theorem adjacentDerives_SWAP_S_left (i j : Fin n) (hij : i ≠ j)
    (hadj : (Gate.CZ i j hij).IsAdjacent) :
    AdjacentDerives g (SWAP (d := d) i j hij ++ [.S i])
      ([.S j] ++ SWAP (d := d) i j hij) :=
  .rule ⟨Or.inr (.C10 i j hij),
    adjacent_append (isAdjacentWord_SWAP i j hij hadj) (adjacent_singleton ⟨.S i, rfl⟩),
    adjacent_append (adjacent_singleton ⟨.S j, rfl⟩) (isAdjacentWord_SWAP i j hij hadj)⟩

/-- C11 in its printed orientation. -/
theorem adjacentDerives_SWAP_H_left (i j : Fin n) (hij : i ≠ j)
    (hadj : (Gate.CZ i j hij).IsAdjacent) :
    AdjacentDerives g (SWAP (d := d) i j hij ++ [.H i])
      ([.H j] ++ SWAP (d := d) i j hij) :=
  .rule ⟨Or.inr (.C11 i j hij),
    adjacent_append (isAdjacentWord_SWAP i j hij hadj) (adjacent_singleton ⟨.H i, rfl⟩),
    adjacent_append (adjacent_singleton ⟨.H j, rfl⟩) (isAdjacentWord_SWAP i j hij hadj)⟩

/-- Opposite-wire S transport is derived from C7 and canonical C10. -/
theorem adjacentDerives_SWAP_S_right (i j : Fin n) (hij : i ≠ j)
    (hadj : (Gate.CZ i j hij).IsAdjacent) :
    AdjacentDerives g (SWAP (d := d) i j hij ++ [.S j])
      ([.S i] ++ SWAP (d := d) i j hij) :=
  AdjacentDerives.reverse_involution_transport g (adjacentDerives_SWAP_sq g i j hij hadj)
    (adjacentDerives_SWAP_S_left g i j hij hadj)

/-- Opposite-wire H transport is derived from C7 and canonical C11. -/
theorem adjacentDerives_SWAP_H_right (i j : Fin n) (hij : i ≠ j)
    (hadj : (Gate.CZ i j hij).IsAdjacent) :
    AdjacentDerives g (SWAP (d := d) i j hij ++ [.H j])
      ([.H i] ++ SWAP (d := d) i j hij) :=
  AdjacentDerives.reverse_involution_transport g (adjacentDerives_SWAP_sq g i j hij hadj)
    (adjacentDerives_SWAP_H_left g i j hij hadj)

/-- Transport through a repeated primitive uses only the original adjacent
transport equation and sequential contexts. -/
theorem AdjacentDerives.transport_replicate {t : Word n} {a b : Gate n}
    (h : AdjacentDerives g (t++[a]) ([b]++t)) (k : ℕ) :
    AdjacentDerives g (t++List.replicate k a) (List.replicate k b++t) := by
  induction k with
  | zero => simpa only [List.replicate_zero, List.append_nil, List.nil_append] using
      (show AdjacentDerives g t t from .refl t)
  | succ k ih =>
    have h₁ := h.append_right (List.replicate k a)
    have h₂ := ih.append_left [b]
    have h₁' : AdjacentDerives g (t++List.replicate (k+1) a)
        ([b]++(t++List.replicate k a)) := by
      simpa only [List.replicate_succ, List.append_assoc, List.singleton_append] using h₁
    simpa only [List.replicate_succ, List.singleton_append, List.cons_append] using h₁'.trans h₂

/-- Every residue power of S transports from the second wire in the restricted
presentation, with the same literal finite exponent convention as Figure 1. -/
theorem adjacentDerives_SWAP_Sexp_right (i j : Fin n) (hij : i ≠ j)
    (hadj : (Gate.CZ i j hij).IsAdjacent) (a : ZMod d) :
    AdjacentDerives g (SWAP (d := d) i j hij ++ Sexp j a)
      (Sexp i a ++ SWAP (d := d) i j hij) :=
  AdjacentDerives.transport_replicate g (adjacentDerives_SWAP_S_right g i j hij hadj) a.val

theorem adjacentDerives_SWAP_Sexp_left (i j : Fin n) (hij : i ≠ j)
    (hadj : (Gate.CZ i j hij).IsAdjacent) (a : ZMod d) :
    AdjacentDerives g (SWAP (d := d) i j hij ++ Sexp i a)
      (Sexp j a ++ SWAP (d := d) i j hij) :=
  AdjacentDerives.transport_replicate g (adjacentDerives_SWAP_S_left g i j hij hadj) a.val

end QuditClifford.Circuit
