import QuditClifford.AdjacentOneWireRewrites

/-!
# Inverses in the adjacent Figure 1 presentation

All cancellations below are derivations in the canonical adjacent alphabet.
The Fourier order relation is replayed from a one-wire derivation, and the
other primitive orders are guarded instances of C0, C1 and C6.
-/

namespace QuditClifford.Circuit
variable {d n : ℕ}

/-- The explicit inverse of an adjacent word stays in the adjacent alphabet. -/
theorem IsAdjacentWord.inverseWord {w : Word n} (hw : IsAdjacentWord w) (d : ℕ) :
    IsAdjacentWord (Circuit.inverseWord d w) := by
  obtain ⟨v, rfl⟩ := (isAdjacentWord_iff_exists w).mp hw
  rw [← AdjacentWord.toWord_inverseWord]
  exact AdjacentWord.isAdjacent_toWord _

variable [NeZero d] [Fact d.Prime]

/-- The derived fourth-order Fourier relation remains an adjacent derivation. -/
theorem adjacentDerives_H_four (hd : Odd d) (g : (ZMod d)ˣ)
    (hg : orderOf g = d-1) (i : Fin n) :
    AdjacentDerives g (List.replicate 4 (.H i)) [] := by
  simpa only [relabel_replicate, relabel_nil, Gate.relabel,
    singleWireEmbedding, Function.Embedding.coeFn_mk] using
    adjacentDerives_singleWire g i (derives_H_four hd g hg (0 : Fin 1))

private theorem adjacentDerives_replicate_cancel (g : (ZMod d)ˣ) (a : Gate n)
    (m : ℕ) (hm : 1 ≤ m) (h : AdjacentDerives g (List.replicate m a) []) :
    AdjacentDerives g ([a] ++ List.replicate (m-1) a) [] ∧
      AdjacentDerives g (List.replicate (m-1) a ++ [a]) [] := by
  have hl : [a] ++ List.replicate (m-1) a = List.replicate m a := by
    change List.replicate 1 a ++ List.replicate (m-1) a = _
    rw [← List.replicate_add, Nat.add_sub_of_le hm]
  have hr : List.replicate (m-1) a ++ [a] = List.replicate m a := by
    change List.replicate (m-1) a ++ List.replicate 1 a = _
    rw [← List.replicate_add, Nat.sub_add_cancel hm]
  exact ⟨hl.symm ▸ h, hr.symm ▸ h⟩

/-- Every canonical adjacent primitive cancels its explicit inverse word. -/
theorem adjacentDerives_gate_inverse (hd : Odd d) (g : (ZMod d)ˣ)
    (hg : orderOf g = d-1) (a : Gate n) (ha : a.IsAdjacent) :
    AdjacentDerives g ([a] ++ a.inverseWord d) [] ∧
      AdjacentDerives g (a.inverseWord d ++ [a]) [] := by
  cases a with
  | scalar =>
    exact adjacentDerives_replicate_cancel g .scalar (2*d)
      (by have hp := NeZero.pos d; omega) (adjacentDerives_scalar_order g)
  | H i =>
    exact adjacentDerives_replicate_cancel g (.H i) 4 (by decide)
      (adjacentDerives_H_four hd g hg i)
  | S i =>
    exact adjacentDerives_replicate_cancel g (.S i) d (NeZero.pos d)
      (.rule ⟨Or.inr (Figure1Rule.C1 i), IsAdjacentWord.replicate ha d, isAdjacentWord_nil⟩)
  | CZ i j h =>
    exact adjacentDerives_replicate_cancel g (.CZ i j h) d (NeZero.pos d)
      (.rule ⟨Or.inr (Figure1Rule.C6 i j h), IsAdjacentWord.replicate ha d, isAdjacentWord_nil⟩)

/-- An adjacent word followed by its inverse cancels syntactically. -/
theorem adjacentDerives_append_inverseWord (hd : Odd d) (g : (ZMod d)ˣ)
    (hg : orderOf g = d-1) (w : Word n) (hw : IsAdjacentWord w) :
    AdjacentDerives g (w ++ inverseWord d w) [] := by
  induction w with
  | nil => exact .refl _
  | cons a w ih =>
    obtain ⟨ha, hw⟩ := (isAdjacentWord_cons a w).mp hw
    have h₁ := (ih hw).context [a] (a.inverseWord d)
    have h₂ := (adjacentDerives_gate_inverse hd g hg a ha).1
    simpa only [inverseWord_cons, List.append_assoc, List.cons_append, List.nil_append]
      using h₁.trans h₂

/-- The inverse word cancels in the other multiplication order too. -/
theorem adjacentDerives_inverseWord_append (hd : Odd d) (g : (ZMod d)ˣ)
    (hg : orderOf g = d-1) (w : Word n) (hw : IsAdjacentWord w) :
    AdjacentDerives g (inverseWord d w ++ w) [] := by
  induction w with
  | nil => exact .refl _
  | cons a w ih =>
    obtain ⟨ha, hw⟩ := (isAdjacentWord_cons a w).mp hw
    have h₁ := ((adjacentDerives_gate_inverse hd g hg a ha).2).context (inverseWord d w) w
    have h₁' : AdjacentDerives g (inverseWord d (a::w) ++ (a::w))
        (inverseWord d w ++ w) := by
      simpa only [inverseWord_cons, List.append_assoc, List.cons_append,
        List.nil_append, List.append_nil] using h₁
    exact h₁'.trans (ih hw)

/-- Cancellation of a common adjacent right context uses the proved inverse. -/
theorem adjacentDerives_cancel_right (hd : Odd d) (g : (ZMod d)ˣ)
    (hg : orderOf g = d-1) {u v w : Word n} (hw : IsAdjacentWord w)
    (h : AdjacentDerives g (u ++ w) (v ++ w)) : AdjacentDerives g u v := by
  have hc := adjacentDerives_append_inverseWord hd g hg w hw
  have hu : AdjacentDerives g (u ++ (w ++ inverseWord d w)) u := by
    simpa only [List.append_nil] using hc.append_left u
  have hv : AdjacentDerives g (v ++ (w ++ inverseWord d w)) v := by
    simpa only [List.append_nil] using hc.append_left v
  have hm : AdjacentDerives g (u ++ (w ++ inverseWord d w))
      (v ++ (w ++ inverseWord d w)) := by
    simpa only [List.append_assoc] using h.append_right (inverseWord d w)
  exact hu.symm.trans (hm.trans hv)

/-- Cancellation of a common adjacent left context is also syntactic. -/
theorem adjacentDerives_cancel_left (hd : Odd d) (g : (ZMod d)ˣ)
    (hg : orderOf g = d-1) {u v w : Word n} (hw : IsAdjacentWord w)
    (h : AdjacentDerives g (w ++ u) (w ++ v)) : AdjacentDerives g u v := by
  have hc := adjacentDerives_inverseWord_append hd g hg w hw
  have hu : AdjacentDerives g (inverseWord d w ++ (w ++ u)) u := by
    simpa only [List.append_assoc, List.nil_append] using hc.append_right u
  have hv : AdjacentDerives g (inverseWord d w ++ (w ++ v)) v := by
    simpa only [List.append_assoc, List.nil_append] using hc.append_right v
  exact hu.symm.trans ((h.append_left (inverseWord d w)).trans hv)

/-- Explicit inverse words respect the restricted presentation relation. -/
theorem adjacentDerives_inverseWord (hd : Odd d) (g : (ZMod d)ˣ)
    (hg : orderOf g = d-1) {u v : Word n} (hu : IsAdjacentWord u)
    (hv : IsAdjacentWord v) (h : AdjacentDerives g u v) :
    AdjacentDerives g (inverseWord d u) (inverseWord d v) := by
  apply adjacentDerives_cancel_left hd g hg hu
  exact (adjacentDerives_append_inverseWord hd g hg u hu).trans
    ((adjacentDerives_append_inverseWord hd g hg v hv).symm.trans
      (h.symm.append_right (inverseWord d v)))

end QuditClifford.Circuit
