import QuditClifford.AdjacentXNormalPushS

/-!
# Fourier pushing through X-normal sweeps away from the head wire

The local D/H branches emit a circuit on the preceding wire. Disjoint
structural interchange moves it past the shifted tail. Recursing past outer
D boxes handles every non-head input wire. The residual remains an explicit
adjacent word on one fewer wire; the relation explicitly erases scalar and
Pauli corrections, as required by the nonzero/nonzero D/H branch.
-/
noncomputable section
namespace QuditClifford.Circuit
variable {d l m n : ℕ} [NeZero d] (g : (ZMod d)ˣ)

/-- Two words with disjoint supports interchange inside the adjacent relation. -/
theorem adjacentDerives_words_commute (u v : Word n)
    (hu : IsAdjacentWord u) (hv : IsAdjacentWord v)
    (hdis : ∀ a ∈ u, ∀ b ∈ v, Disjoint a.support b.support) :
    AdjacentDerives g (u ++ v) (v ++ u) := by
  induction v with
  | nil => simpa only [List.append_nil, List.nil_append] using (show AdjacentDerives g u u from .refl _)
  | cons b v ih =>
    have hb := hv b (by simp)
    have hvt : IsAdjacentWord v := fun a ha => hv a (by simp [ha])
    have hdt : ∀ a ∈ u, ∀ c ∈ v, Disjoint a.support c.support :=
      fun a ha c hc => hdis a ha c (by simp [hc])
    have h₁ := (adjacentDerives_word_gate_commute g u b hu hb
      (fun a ha => hdis a ha b (by simp))).append_right v
    have h₂ := (ih hvt hdt).append_left [b]
    simpa only [List.append_assoc, List.singleton_append] using h₁.trans h₂

/-- Disjoint wire embeddings give a restricted contextual interchange of
complete expanded words, including every scalar letter. -/
theorem adjacentDerives_relabel_interchange (ι : Fin l ↪ Fin n) (κ : Fin m ↪ Fin n)
    (hικ : ∀ i j, ι i ≠ κ j) (u : Word l) (v : Word m)
    (hu : IsAdjacentWord (relabel ι u)) (hv : IsAdjacentWord (relabel κ v)) :
    AdjacentDerives g (relabel ι u ++ relabel κ v) (relabel κ v ++ relabel ι u) := by
  apply adjacentDerives_words_commute g _ _ hu hv
  intro a ha b hb
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp ha
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hb
  rw [Gate.support_relabel, Gate.support_relabel]
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hy
  exact hικ i j hj.symm

/-- An H outside an embedded circuit's wire image commutes with it using
only restricted structural steps. -/
theorem adjacentDerives_H_commute_relabel (ι : Fin m ↪ Fin n) (i : Fin n)
    (hi : ∀ j, ι j ≠ i) (v : Word m) (hv : IsAdjacentWord (relabel ι v)) :
    AdjacentDerives g (relabel ι v ++ [.H i]) ([.H i] ++ relabel ι v) := by
  apply adjacentDerives_word_gate_commute g _ _ hv (Gate.isAdjacent_H i)
  intro a ha
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
  rw [Gate.support_relabel]
  change Disjoint (Finset.map ι b.support) {i}
  rw [Finset.disjoint_singleton_right]
  intro hi'
  obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hi'
  exact hi j hj

/-- Place a restricted erased two-wire proof at any neighboring pair. -/
theorem adjacentSymplecticDerives_pair (i : Fin (n+1)) {u v : Word 2}
    (h : AdjacentSymplecticDerives g u v) :
    AdjacentSymplecticDerives g (relabel (adjacentPairEmbedding i) u)
      (relabel (adjacentPairEmbedding i) v) :=
  adjacentSymplecticDerives_relabel g (adjacentPairEmbedding i)
    (fun _ hw => hw.relabel_adjacentPair i) h

omit [NeZero d] in
/-- Relabeling a one-wire placement composes its chosen wire literally. -/
theorem relabel_singleWire_comp (ι : Fin m ↪ Fin n) (i : Fin m) (u : Word 1) :
    relabel ι (relabel (singleWireEmbedding i) u) =
      relabel (singleWireEmbedding (ι i)) u := by
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

/-- All four D/H branches emit a literal one-wire word on the first wire. -/
theorem adjacentSymplectic_D_H_right (a b : ZMod d) :
    ∃ (u : Word 1) (a' b' : ZMod d),
      AdjacentSymplecticDerives g
        (dWord a b (0 : Fin 2) 1 (by decide) ++ [.H 1])
        (relabel (singleWireEmbedding 0) u ++ dWord a' b' 0 1 (by decide)) := by
  by_cases ha : a = 0
  · subst a
    by_cases hb : b = 0
    · subst b
      refine ⟨[.H 0], 0, 0, ?_⟩
      simpa only [relabel_cons, relabel_nil, Gate.relabel, singleWireEmbedding,
        Function.Embedding.coeFn_mk] using
        adjacentDerives_symplectic g (adjacentDerives_D_H_zero_zero g)
    · refine ⟨[], b, 0, ?_⟩
      simpa only [relabel_nil, List.nil_append] using
        adjacentDerives_symplectic g (adjacentDerives_D_H_zero_nonzero g b hb)
  · by_cases hb : b = 0
    · subst b
      refine ⟨List.replicate 2 (.H 0), 0, -a, ?_⟩
      simpa only [relabel_replicate, Gate.relabel, singleWireEmbedding,
        Function.Embedding.coeFn_mk] using
        adjacentDerives_symplectic g (adjacentDerives_D_H_nonzero_zero g a ha)
    · refine ⟨Circuit.multiplier 0 (Units.mk0 (b/a) (div_ne_zero hb ha)) ++
        Sexp 0 (b/a), b, -a, ?_⟩
      simpa only [relabel_append, relabel_multiplier, relabel_Sexp, singleWireEmbedding,
        Function.Embedding.coeFn_mk] using
        adjacentSymplectic_D_H_nonzero_nonzero_source g a b ha hb

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
private theorem dWord_H_offwire {n : ℕ} (a b : ZMod d) (k : Fin n) :
    AdjacentDerives g
      (dWord a b (0 : Fin (n+2)) 1 (adjacent_ne (0 : Fin (n+1))) ++ [.H k.succ.succ])
      ([.H k.succ.succ] ++ dWord a b (0 : Fin (n+2)) 1 (adjacent_ne (0 : Fin (n+1)))) := by
  have hi : ∀ j : Fin 2, adjacentPairEmbedding (0 : Fin (n+1)) j ≠ k.succ.succ := by
    intro j
    fin_cases j <;> simp only [adjacentPairEmbedding_zero, adjacentPairEmbedding_one]
    all_goals intro h; have hv := congrArg Fin.val h; simp at hv
  have hw : IsAdjacentWord
      (relabel (adjacentPairEmbedding (0 : Fin (n+1)))
        (dWord a b (0 : Fin 2) 1 (by decide))) :=
    (dWord_isAdjacent a b (0 : Fin 1)).relabel_adjacentPair 0
  have h := adjacentDerives_H_commute_relabel g (adjacentPairEmbedding (0 : Fin (n+1)))
      k.succ.succ hi (dWord a b (0 : Fin 2) 1 (by decide)) hw
  rw [relabel_dWord] at h
  simpa only [adjacentPairEmbedding_zero, adjacentPairEmbedding_one] using h

/-- An H on any non-head input wire crosses an X-normal sweep in the
restricted erased relation, leaving a typed adjacent residual on fewer wires. -/
theorem XNormal.adjacentSymplecticDerives_pushH {n : ℕ}
    (N : XNormal (ZMod d) (n+1)) (i : Fin n) :
    ∃ (r : AdjacentWord n) (N' : XNormal (ZMod d) (n+1)),
      AdjacentSymplecticDerives g (N.toWord ++ [.H i.succ])
        (relabel (initialEmbedding n) r.toWord ++ N'.toWord) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases N with
    | step a b N =>
      refine Fin.cases ?_ (fun k => ?_) i
      · obtain ⟨u, a', b', hd⟩ := adjacentSymplectic_D_H_right g a b
        obtain ⟨r, hr⟩ := (isAdjacentWord_iff_exists
          (relabel (singleWireEmbedding (0 : Fin (n+1))) u)).mp
            (isAdjacentWord_singleWire 0 u)
        refine ⟨r, .step a' b' N, ?_⟩
        have hdp := adjacentSymplecticDerives_pair g (0 : Fin (n+1)) hd
        simp only [relabel_append, relabel_dWord, relabel_cons, relabel_nil,
          Gate.relabel, relabel_singleWire_comp, adjacentPairEmbedding_zero,
          adjacentPairEmbedding_one] at hdp
        have hc := adjacentDerives_relabel_interchange g (shiftEmbedding (n+1))
          (singleWireEmbedding (0 : Fin (n+2)))
          (fun j _ => Fin.succ_ne_zero j) N.toWord u
          N.toWord_isAdjacent.shift (isAdjacentWord_singleWire 0 u)
        have h₁ := hdp.append_left (relabel (shiftEmbedding _) N.toWord)
        have h₂ := (adjacentDerives_symplectic g hc).append_right
          (dWord a' b' (0 : Fin (n+2)) 1 (adjacent_ne (0 : Fin (n+1))))
        simp only [List.append_assoc] at h₂
        have ht := h₁.trans h₂
        simpa only [XNormal.toWord, hr, relabel_singleWire_comp, initialEmbedding,
          Function.Embedding.coeFn_mk, List.append_assoc] using ht
      · obtain ⟨r, N', hr⟩ := ih N k
        refine ⟨r.shift, .step a b N', ?_⟩
        have h₁ := (adjacentDerives_symplectic g (dWord_H_offwire g a b k)).append_left
          (relabel (shiftEmbedding _) N.toWord)
        have h₂ := (adjacentSymplecticDerives_shift g hr).append_right
          (dWord a b (0 : Fin (n+2)) 1 (adjacent_ne (0 : Fin (n+1))))
        simp only [relabel_append, relabel_cons, relabel_nil, Gate.relabel,
          List.append_assoc] at h₂
        have ht := h₁.trans h₂
        simpa only [XNormal.toWord, AdjacentWord.toWord_shift,
          relabel_shift_initial, List.append_assoc] using ht

end QuditClifford.NormalBoxes
