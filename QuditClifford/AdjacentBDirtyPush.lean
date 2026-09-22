import QuditClifford.AdjacentXNormalPushH
import QuditClifford.AdjacentThreeWireBoxCases
import QuditClifford.AdjacentTripleEmbedding
import QuditClifford.AdjacentZSweepWord

/-!
# Passing a B box through a shifted dirty Z-sweep word

The B labels remain unchanged. Scalar letters and gates away from its two
wires pass by restricted structural commutation; the overlapping S/CZ
letters use the checked local branches. The output remains in the explicit
dirty grammar, including the routed remote-CZ correction.
-/
noncomputable section
namespace QuditClifford.NormalBoxes
open Circuit
variable {d : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ)

/-- A neighboring B box commutes with an adjacent primitive outside its wires. -/
theorem adjacentDerives_B_offwire {m : ℕ} (a b : ZMod d) (q : Gate (m+2))
    (hq : q.IsAdjacent)
    (haway : ∀ j : Fin 2, adjacentPairEmbedding (0 : Fin (m+1)) j ∉ q.support) :
    AdjacentDerives g
      (bWord a b (0 : Fin (m+2)) 1 (adjacent_ne (0 : Fin (m+1))) ++ [q])
      ([q] ++ bWord a b (0 : Fin (m+2)) 1 (adjacent_ne (0 : Fin (m+1)))) := by
  have hu : IsAdjacentWord
      (relabel (adjacentPairEmbedding (0 : Fin (m+1)))
        (bWord a b (0 : Fin 2) 1 (by decide))) :=
    (bWord_isAdjacent a b (0 : Fin 1)).relabel_adjacentPair 0
  have ht := adjacentDerives_word_gate_commute g
    (relabel (adjacentPairEmbedding (0 : Fin (m+1)))
      (bWord a b (0 : Fin 2) 1 (by decide))) q hu hq
  have hd : ∀ c ∈ relabel (adjacentPairEmbedding (0 : Fin (m+1)))
      (bWord a b (0 : Fin 2) 1 (by decide)), Disjoint c.support q.support := by
    intro c hc
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hc
    rw [Gate.support_relabel]
    apply Finset.disjoint_left.mpr
    intro x hx hxq
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hx
    exact haway j hxq
  have h := ht hd
  rw [relabel_bWord] at h
  simpa only [adjacentPairEmbedding_zero, adjacentPairEmbedding_one] using h

variable [Fact (Odd d)] [Fact (orderOf g = d-1)]

private theorem b_tail_S_local (a b : ZMod d) :
    ∃ t : ZMod d, AdjacentSymplecticDerives g
      (bWord a b (0 : Fin 2) 1 (by decide) ++ [.S 1])
      ([.S 0] ++ Sexp 1 (t*t) ++ List.replicate (-t).val (.CZ 0 1 (by decide)) ++
        bWord a b 0 1 (by decide)) := by
  by_cases ha : a = 0
  · subst a
    exact ⟨b, adjacentSymplecticDerives_B_S_right_zero g b⟩
  · exact ⟨a, adjacentSymplecticDerives_B_S_right_nonzero g a b ha⟩

/-- A phase on the first tail wire passes a B box without changing its labels. -/
theorem adjacentSymplecticDerives_B_tail_S {m : ℕ} (a b : ZMod d) :
    ∃ r : ZSweepWord (m+1), AdjacentSymplecticDerives g
      (bWord a b (0 : Fin (m+2)) 1 (adjacent_ne (0 : Fin (m+1))) ++ [.S 1])
      (r.toWord ++ bWord a b 0 1 (adjacent_ne (0 : Fin (m+1)))) := by
  obtain ⟨t, ht⟩ := b_tail_S_local g a b
  refine ⟨[.S 0] ++ List.replicate (t*t).val (.S 1) ++
    List.replicate (-t).val (.CZ 0), ?_⟩
  have h := adjacentSymplecticDerives_pair g (0 : Fin (m+1)) ht
  simpa only [relabel_append, relabel_bWord, relabel_cons, relabel_nil,
    relabel_Sexp, relabel_replicate, Gate.relabel, adjacentPairEmbedding_zero,
    adjacentPairEmbedding_one, ZSweepWord.toWord_append, ZSweepWord.toWord,
    List.map_append, List.map_cons, List.map_nil, List.map_replicate, ZSweepGate.toGate, Sexp] using h

private theorem b_tail_CZ_local (a b : ZMod d) :
    ∃ t : ZMod d, AdjacentDerives g
      (bWord a b (0 : Fin 3) 1 (by decide) ++ [.CZ 1 2 (by decide)])
      (Circuit.CIZ (d := d) 0 1 2 (by decide) (by decide) (by decide) ++
        List.replicate (-t).val (.CZ 1 2 (by decide)) ++ bWord a b 0 1 (by decide)) := by
  by_cases ha : a = 0
  · subst a
    exact ⟨b, adjacentDerives_B_CZ_lower_zero g b⟩
  · exact ⟨a, adjacentDerives_B_CZ_lower_nonzero g a b ha⟩

/-- The first tail CZ passes a B box with a routed remote-phase dirty residual. -/
theorem adjacentSymplecticDerives_B_tail_CZ {m : ℕ} (a b : ZMod d) :
    ∃ r : ZSweepWord (m+2), AdjacentSymplecticDerives g
      (bWord a b (0 : Fin (m+3)) 1 (adjacent_ne (0 : Fin (m+2))) ++
        [.CZ 1 2 (adjacent_ne (1 : Fin (m+2)))])
      (r.toWord ++ bWord a b 0 1 (adjacent_ne (0 : Fin (m+2)))) := by
  obtain ⟨t, ht⟩ := b_tail_CZ_local g a b
  have hR : IsZSweepWord
      (Circuit.CIZ (d := d) (0 : Fin 3) 1 2 (by decide) (by decide) (by decide) ++
        List.replicate (-t).val (.CZ 1 2 (by decide))) :=
    (isZSweepWord_append _ _).mpr ⟨isZSweepWord_CIZ012,
      IsZSweepWord.replicate _ (isZSweepWord_CZ (1 : Fin 2)) _⟩
  obtain ⟨r, hr⟩ := (isZSweepWord_iff_exists _).mp (hR.relabel_triple (n := m))
  refine ⟨r, ?_⟩
  have h := adjacentDerives_symplectic g (adjacentDerives_triple g (0 : Fin (m+1)) ht)
  simpa only [hr, relabel_append, relabel_bWord, relabel_cons, relabel_nil,
    Gate.relabel, adjacentTripleEmbedding_zero, adjacentTripleEmbedding_one,
    adjacentTripleEmbedding_two] using h

/-- One shifted dirty letter passes a B box without changing its labels. -/
theorem adjacentSymplecticDerives_B_dirtyGate {m : ℕ} (a b : ZMod d) (q : ZSweepGate m) :
    ∃ r : ZSweepWord (m+1), AdjacentSymplecticDerives g
      (bWord a b (0 : Fin (m+2)) 1 (adjacent_ne (0 : Fin (m+1))) ++
        [q.toGate.relabel (shiftEmbedding (m+1))])
      (r.toWord ++ bWord a b 0 1 (adjacent_ne (0 : Fin (m+1)))) := by
  cases q with
  | scalar =>
    refine ⟨[.scalar], ?_⟩
    simpa only [ZSweepWord.toWord_cons, ZSweepWord.toWord_nil, ZSweepGate.toGate,
      Gate.relabel] using adjacentDerives_symplectic g
        (adjacentDerives_scalar_one_commute g _ (bWord_isAdjacent a b (0 : Fin (m+1)))).symm
  | H i =>
    refine ⟨[.H i.succ], ?_⟩
    have h := adjacentDerives_B_offwire g a b (.H i.succ.succ) (Gate.isAdjacent_H _) (by
      intro j hj
      fin_cases j <;> simp only [adjacentPairEmbedding_zero, adjacentPairEmbedding_one,
        Gate.support, Finset.mem_singleton] at hj
      all_goals have hv := congrArg Fin.val hj; simp at hv)
    simpa only [ZSweepWord.toWord_cons, ZSweepWord.toWord_nil, ZSweepGate.toGate,
      Gate.relabel, shiftEmbedding, Function.Embedding.coeFn_mk] using
        adjacentDerives_symplectic g h
  | S i =>
    refine Fin.cases ?_ (fun k => ?_) i
    · simpa only [ZSweepGate.toGate, Gate.relabel, shiftEmbedding,
        Function.Embedding.coeFn_mk] using adjacentSymplecticDerives_B_tail_S (m := m) g a b
    · refine ⟨[.S k.succ.succ], ?_⟩
      have h := adjacentDerives_B_offwire g a b (.S k.succ.succ) (Gate.isAdjacent_S _) (by
        intro j hj
        fin_cases j <;> simp only [adjacentPairEmbedding_zero, adjacentPairEmbedding_one,
          Gate.support, Finset.mem_singleton] at hj
        all_goals have hv := congrArg Fin.val hj; simp at hv)
      simpa only [ZSweepWord.toWord_cons, ZSweepWord.toWord_nil, ZSweepGate.toGate,
        Gate.relabel, shiftEmbedding, Function.Embedding.coeFn_mk] using
          adjacentDerives_symplectic g h
  | CZ i =>
    cases m with
    | zero => exact Fin.elim0 i
    | succ m =>
      refine Fin.cases ?_ (fun k => ?_) i
      · simpa only [ZSweepGate.toGate, Gate.relabel, shiftEmbedding,
          Function.Embedding.coeFn_mk] using adjacentSymplecticDerives_B_tail_CZ (m := m) g a b
      · refine ⟨[.CZ k.succ.succ], ?_⟩
        have h := adjacentDerives_B_offwire g a b
          (.CZ k.succ.succ.castSucc k.succ.succ.succ (adjacent_ne k.succ.succ))
          (Gate.isAdjacent_CZ _ _) (by
            intro j hj
            fin_cases j <;> simp only [adjacentPairEmbedding_zero, adjacentPairEmbedding_one,
              Gate.support, Finset.mem_insert, Finset.mem_singleton] at hj
            all_goals rcases hj with hj | hj <;> have hv := congrArg Fin.val hj <;> simp at hv)
        simpa only [ZSweepWord.toWord_cons, ZSweepWord.toWord_nil, ZSweepGate.toGate,
          Gate.relabel, shiftEmbedding, Function.Embedding.coeFn_mk] using
            adjacentDerives_symplectic g h

/-- Any shifted dirty Z-sweep word passes a B box by a literal word induction.
The B labels stay fixed, and the complete residual is again a typed dirty word. -/
theorem adjacentSymplecticDerives_B_dirtyWord {m : ℕ} (a b : ZMod d) (w : ZSweepWord m) :
    ∃ r : ZSweepWord (m+1), AdjacentSymplecticDerives g
      (bWord a b (0 : Fin (m+2)) 1 (adjacent_ne (0 : Fin (m+1))) ++
        relabel (shiftEmbedding (m+1)) w.toWord)
      (r.toWord ++ bWord a b 0 1 (adjacent_ne (0 : Fin (m+1)))) := by
  induction w with
  | nil =>
    refine ⟨[], ?_⟩
    simp only [ZSweepWord.toWord_nil, relabel_nil, List.append_nil, List.nil_append]
    exact .refl _
  | cons q w ih =>
    obtain ⟨r₁, h₁⟩ := adjacentSymplecticDerives_B_dirtyGate g a b q
    obtain ⟨r₂, h₂⟩ := ih
    refine ⟨r₁ ++ r₂, ?_⟩
    have ht₁ := h₁.append_right (relabel (shiftEmbedding (m+1)) (ZSweepWord.toWord w))
    have ht₂ := h₂.append_left r₁.toWord
    simp only [List.append_assoc] at ht₁
    simpa only [ZSweepWord.toWord_cons, ZSweepWord.toWord_append, relabel_cons,
      List.append_assoc, List.singleton_append] using ht₁.trans ht₂

end QuditClifford.NormalBoxes
