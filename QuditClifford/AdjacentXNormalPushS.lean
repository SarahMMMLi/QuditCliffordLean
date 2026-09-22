import QuditClifford.AdjacentXNormalPhase

/-!
# Exact S pushing through X-normal sweeps at arbitrary input wires

The residual is a literal adjacent word on one fewer wire. The recursive
proof either absorbs the phase, emits an S on the preceding wire, or moves
past the disjoint outer D box and recurses on the shifted tail. No semantic
normalization or unrestricted higher-arity rewrite is used.
-/
noncomputable section
namespace QuditClifford.Circuit
variable {d m n : ℕ} [NeZero d] (g : (ZMod d)ˣ)

/-- A disjoint adjacent primitive moves through an entire adjacent word using
only the guarded structural commutation rule and word contexts. -/
theorem adjacentDerives_word_gate_commute (w : Word n) (a : Gate n)
    (hw : IsAdjacentWord w) (ha : a.IsAdjacent)
    (hdis : ∀ b ∈ w, Disjoint b.support a.support) :
    AdjacentDerives g (w ++ [a]) ([a] ++ w) := by
  induction w with
  | nil => exact .refl _
  | cons b w ih =>
    have hb : b.IsAdjacent := hw b (by simp)
    have hwt : IsAdjacentWord w := fun c hc => hw c (by simp [hc])
    have hdt : ∀ c ∈ w, Disjoint c.support a.support :=
      fun c hc => hdis c (by simp [hc])
    have h₁ := (ih hwt hdt).append_left [b]
    have h₂ := (adjacentDerives_disjoint g b a hb ha (hdis b (by simp))).append_right w
    simpa only [List.singleton_append, List.cons_append, List.append_assoc] using h₁.trans h₂

/-- An S outside an embedded circuit's wire image commutes with that circuit
inside the restricted presentation. -/
theorem adjacentDerives_S_commute_relabel (ι : Fin m ↪ Fin n) (i : Fin n)
    (hi : ∀ j, ι j ≠ i) (v : Word m) (hv : IsAdjacentWord (relabel ι v)) :
    AdjacentDerives g (relabel ι v ++ [.S i]) ([.S i] ++ relabel ι v) := by
  apply adjacentDerives_word_gate_commute g _ _ hv (Gate.isAdjacent_S i)
  intro a ha
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
  rw [Gate.support_relabel]
  change Disjoint (Finset.map ι b.support) {i}
  rw [Finset.disjoint_singleton_right]
  intro hi'
  obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hi'
  exact hi j hj

omit [NeZero d] in
/-- Shifting a circuit and adding a final idle wire commute literally. -/
theorem relabel_shift_initial (w : Word n) :
    relabel (shiftEmbedding (n+1)) (relabel (initialEmbedding n) w) =
      relabel (initialEmbedding (n+1)) (relabel (shiftEmbedding n) w) := by
  unfold relabel
  simp only [List.map_map]
  congr 1
  funext a
  cases a <;> rfl

end QuditClifford.Circuit

namespace QuditClifford.NormalBoxes
open Circuit
variable {d : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
private theorem dWord_S_offwire {n : ℕ} (a b : ZMod d) (k : Fin n) :
    AdjacentDerives g
      (dWord a b (0 : Fin (n+2)) 1 (adjacent_ne (0 : Fin (n+1))) ++ [.S k.succ.succ])
      ([.S k.succ.succ] ++ dWord a b (0 : Fin (n+2)) 1 (adjacent_ne (0 : Fin (n+1)))) := by
  have hi : ∀ j : Fin 2, adjacentPairEmbedding (0 : Fin (n+1)) j ≠ k.succ.succ := by
    intro j
    fin_cases j <;> simp only [adjacentPairEmbedding_zero, adjacentPairEmbedding_one]
    all_goals intro h; have hv := congrArg Fin.val h; simp at hv
  have hw : IsAdjacentWord
      (relabel (adjacentPairEmbedding (0 : Fin (n+1)))
        (dWord a b (0 : Fin 2) 1 (by decide))) :=
    (dWord_isAdjacent a b (0 : Fin 1)).relabel_adjacentPair 0
  have h := adjacentDerives_S_commute_relabel g (adjacentPairEmbedding (0 : Fin (n+1)))
      k.succ.succ hi (dWord a b (0 : Fin 2) 1 (by decide)) hw
  rw [relabel_dWord] at h
  simpa only [adjacentPairEmbedding_zero, adjacentPairEmbedding_one] using h

/-- Every S input is pushed through an X-normal sweep by exact adjacent
rewrites, leaving an explicit adjacent residual on the preceding wires. -/
theorem XNormal.adjacentDerives_pushS {n : ℕ}
    (N : XNormal (ZMod d) (n+1)) (i : Fin (n+1)) :
    ∃ (r : AdjacentWord n) (N' : XNormal (ZMod d) (n+1)),
      AdjacentDerives g (N.toWord ++ [.S i])
        (relabel (initialEmbedding n) r.toWord ++ N'.toWord) := by
  induction n with
  | zero =>
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    refine ⟨[], N.absorbPhase 1, ?_⟩
    simpa only [AdjacentWord.toWord_nil, relabel_nil, List.nil_append] using
      N.adjacentDerives_absorbS g
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · refine ⟨[], N.absorbPhase 1, ?_⟩
      simpa only [AdjacentWord.toWord_nil, relabel_nil, List.nil_append] using
        N.adjacentDerives_absorbS g
    · cases N with
      | step a b N =>
        refine Fin.cases ?_ (fun k => ?_) i
        · by_cases ha : a = 0
          · subst a
            refine ⟨[.S 0], .step 0 b N, ?_⟩
            have hd := adjacentDerives_pair g (0 : Fin (n+1))
              (adjacentDerives_D_S_right_zero g b)
            simp only [relabel_append, relabel_dWord, relabel_cons, relabel_nil,
              Gate.relabel, adjacentPairEmbedding_zero, adjacentPairEmbedding_one] at hd
            have hc := adjacentDerives_S_commute_relabel g (shiftEmbedding (n+1))
              0 (fun j => Fin.succ_ne_zero j) N.toWord N.toWord_isAdjacent.shift
            have h₁ := hd.append_left (relabel (shiftEmbedding _) N.toWord)
            have h₂ := hc.append_right
              (dWord (0 : ZMod d) b (0 : Fin (n+2)) 1 (adjacent_ne (0 : Fin (n+1))))
            simp only [List.append_assoc] at h₂
            simpa only [XNormal.toWord, AdjacentWord.toWord_cons, AdjacentWord.toWord_nil,
              AdjacentGate.toGate, relabel_cons, relabel_nil, Gate.relabel,
              initialEmbedding, Function.Embedding.coeFn_mk, List.append_assoc,
              List.singleton_append] using h₁.trans h₂
          · refine ⟨[], .step a (b-a) N, ?_⟩
            have hd := adjacentDerives_pair g (0 : Fin (n+1))
              (adjacentDerives_D_S_right_nonzero g a b ha)
            simp only [relabel_append, relabel_dWord, relabel_cons, relabel_nil,
              Gate.relabel, adjacentPairEmbedding_zero, adjacentPairEmbedding_one] at hd
            simpa only [XNormal.toWord, AdjacentWord.toWord_nil, relabel_nil,
              List.nil_append, List.append_assoc] using
              hd.append_left (relabel (shiftEmbedding _) N.toWord)
        · obtain ⟨r, N', hr⟩ := ih N k.succ
          refine ⟨r.shift, .step a b N', ?_⟩
          have h₁ := (dWord_S_offwire g a b k).append_left
            (relabel (shiftEmbedding _) N.toWord)
          have h₂ := (adjacentDerives_shift g hr).append_right
            (dWord a b (0 : Fin (n+2)) 1 (adjacent_ne (0 : Fin (n+1))))
          simp only [relabel_append, relabel_cons, relabel_nil, Gate.relabel] at h₂
          simp only [List.append_assoc] at h₂
          have ht := h₁.trans h₂
          simpa only [XNormal.toWord, AdjacentWord.toWord_shift,
            relabel_shift_initial, List.append_assoc] using ht

end QuditClifford.NormalBoxes
