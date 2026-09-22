import QuditClifford.AdjacentXNormalPushH
import QuditClifford.AdjacentThreeWireBoxCases
import QuditClifford.AdjacentTripleEmbedding

/-!
# Adjacent controlled-phase pushing through X-normal sweeps

The first pair uses the D/CZ branch and exact tail phase absorption. The
second pair uses DD/CZ and disjoint interchange of its residual. More distant
pairs recurse after passing the outer D box. Residual circuits inhabit the
literal adjacent alphabet on one fewer wire.
-/

noncomputable section
namespace QuditClifford.Circuit
variable {n : ℕ}

/-- Widening a placement on the first pair leaves that pair in place. -/
theorem relabel_initial_pair_zero (w : Word 2) :
    relabel (initialEmbedding (n+2)) (relabel (adjacentPairEmbedding (0 : Fin (n+1))) w) =
      relabel (adjacentPairEmbedding (0 : Fin (n+2))) w := by
  rw [← relabel_trans]
  congr 1
  ext i
  fin_cases i <;> rfl

/-- A first-pair word stays on the first pair under the first-triple embedding. -/
theorem relabel_triple_initial_zero (w : Word 2) :
    relabel (adjacentTripleEmbedding (0 : Fin (n+1))) (relabel (initialEmbedding 2) w) =
      relabel (adjacentPairEmbedding (0 : Fin (n+2))) w := by
  rw [← relabel_trans]
  congr 1
  ext i
  fin_cases i <;> rfl

end QuditClifford.Circuit

namespace QuditClifford.NormalBoxes
open Circuit
variable {d : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

/-- Both D/CZ branches emit a first-wire word and a phase to be absorbed by the tail. -/
theorem adjacentSymplectic_D_CZ (a b : ZMod d) :
    ∃ (u : Word 1) (t a' b' : ZMod d),
      AdjacentSymplecticDerives g
        (dWord a b (0 : Fin 2) 1 (by decide) ++ [.CZ 0 1 (by decide)])
        (Sexp 1 t ++ relabel (singleWireEmbedding 0) u ++ dWord a' b' 0 1 (by decide)) := by
  by_cases ha : a = 0
  · subst a
    refine ⟨[], 0, 0, b-1, ?_⟩
    simpa only [Sexp, ZMod.val_zero, List.replicate_zero, relabel_nil, List.nil_append] using
      adjacentDerives_symplectic g (adjacentDerives_D_CZ_zero g b)
  · refine ⟨[.H 0] ++ Sexp 0 (-a⁻¹) ++ inverseWord d [.H 0], a, a, b-1, ?_⟩
    simpa only [relabel_append, relabel_cons, relabel_nil, relabel_Sexp,
      relabel_inverseWord, Gate.relabel, singleWireEmbedding, Function.Embedding.coeFn_mk,
      List.append_assoc] using adjacentSymplectic_D_CZ_nonzero g a b ha

/-- All DD/CZ branches emit an adjacent residual confined to the first pair. -/
theorem adjacentSymplectic_DD_CZ (a b c e : ZMod d) :
    ∃ (u : Word 2), IsAdjacentWord u ∧ ∃ (a' b' c' e' : ZMod d),
      AdjacentSymplecticDerives g
        (dWord a b (1 : Fin 3) 2 (by decide) ++ dWord c e 0 1 (by decide) ++ [.CZ 1 2 (by decide)])
        (relabel (initialEmbedding 2) u ++
          dWord a' b' (1 : Fin 3) 2 (by decide) ++ dWord c' e' 0 1 (by decide)) := by
  have hcza : (Gate.CZ (0 : Fin 2) 1 (by decide)).IsAdjacent := ⟨.CZ 0, rfl⟩
  by_cases ha : a = 0
  · subst a
    by_cases hc : c = 0
    · subst c
      refine ⟨[.CZ 0 1 (by decide)], by simpa using hcza, 0, b, 0, e, ?_⟩
      simpa only [relabel_cons, relabel_nil, Gate.relabel, initialEmbedding,
        Function.Embedding.coeFn_mk] using
        adjacentDerives_symplectic g (adjacentDerives_DD_CZ_zero_zero g b e)
    · refine ⟨[.H 0, .CZ 0 1 (by decide)] ++ inverseWord d [.H 0],
        by simp [hcza, Gate.inverseWord], 0, b-c, c, e, ?_⟩
      simpa only [relabel_append, relabel_cons, relabel_nil, relabel_inverseWord,
        Gate.relabel, initialEmbedding, Function.Embedding.coeFn_mk, List.append_assoc] using
        adjacentDerives_symplectic g (adjacentDerives_DD_CZ_zero_nonzero g b c e hc)
  · by_cases hc : c = 0
    · subst c
      refine ⟨[.H 1, .CZ 0 1 (by decide)] ++ inverseWord d [.H 1],
        by simp [hcza, Gate.inverseWord], a, b, 0, e-a, ?_⟩
      simpa only [relabel_append, relabel_cons, relabel_nil, relabel_inverseWord,
        Gate.relabel, initialEmbedding, Function.Embedding.coeFn_mk, List.append_assoc] using
        adjacentDerives_symplectic g (adjacentDerives_DD_CZ_nonzero_zero g a b e ha)
    · refine ⟨[.H 1, .H 0, .CZ 0 1 (by decide)] ++ Sexp 1 (-c/a) ++ inverseWord d [.H 1] ++
        Sexp 0 (-a/c) ++ inverseWord d [.H 0], by simp [hcza, Gate.inverseWord],
        a, b-c, c, e-a, ?_⟩
      simpa only [relabel_append, relabel_cons, relabel_nil, relabel_inverseWord,
        relabel_Sexp, Gate.relabel, initialEmbedding, Function.Embedding.coeFn_mk,
        List.append_assoc] using adjacentSymplectic_DD_CZ_nonzero_nonzero g a b c e ha hc

/-- Pushing a CZ on the first pair, absorbing its phase in the shifted tail. -/
theorem XNormal.adjacentSymplecticDerives_pushCZ_head {n : ℕ}
    (a b : ZMod d) (N : XNormal (ZMod d) (n+1)) :
    ∃ (r : AdjacentWord (n+1)) (N' : XNormal (ZMod d) (n+2)),
      AdjacentSymplecticDerives g
        ((XNormal.step a b N).toWord ++ [.CZ 0 1 (adjacent_ne (0 : Fin (n+1)))])
        (relabel (initialEmbedding (n+1)) r.toWord ++ N'.toWord) := by
  obtain ⟨u, t, a', b', hd⟩ := adjacentSymplectic_D_CZ g a b
  obtain ⟨r, hr⟩ := (isAdjacentWord_iff_exists
    (relabel (singleWireEmbedding (0 : Fin (n+1))) u)).mp (isAdjacentWord_singleWire 0 u)
  refine ⟨r, .step a' b' (N.absorbPhase t), ?_⟩
  have hdp := adjacentSymplecticDerives_pair g (0 : Fin (n+1)) hd
  simp only [relabel_append, relabel_dWord, relabel_cons, relabel_nil, relabel_Sexp,
    Gate.relabel, relabel_singleWire_comp, adjacentPairEmbedding_zero,
    adjacentPairEmbedding_one] at hdp
  have ht := adjacentDerives_symplectic g
    (adjacentDerives_shift g (N.adjacentDerives_absorbPhase g t))
  simp only [relabel_append, relabel_Sexp, shiftEmbedding, Function.Embedding.coeFn_mk] at ht
  have hc := adjacentDerives_symplectic g
    (adjacentDerives_relabel_interchange g (shiftEmbedding (n+1))
      (singleWireEmbedding (0 : Fin (n+2))) (fun j _ => Fin.succ_ne_zero j)
      (N.absorbPhase t).toWord u (N.absorbPhase t).toWord_isAdjacent.shift
      (isAdjacentWord_singleWire 0 u))
  have h₁ := hdp.append_left (relabel (shiftEmbedding _) N.toWord)
  have h₂ := ht.append_right
    (relabel (singleWireEmbedding (0 : Fin (n+2))) u ++
      dWord a' b' 0 1 (adjacent_ne (0 : Fin (n+1))))
  have h₃ := hc.append_right (dWord a' b' 0 1 (adjacent_ne (0 : Fin (n+1))))
  simp only [List.append_assoc] at h₁ h₂ h₃
  simpa only [XNormal.toWord, hr, relabel_singleWire_comp, initialEmbedding,
    Function.Embedding.coeFn_mk, List.append_assoc] using h₁.trans (h₂.trans h₃)

/-- Pushing a CZ on the second pair, using the four DD cases and off-tail interchange. -/
theorem XNormal.adjacentSymplecticDerives_pushCZ_second {n : ℕ}
    (a b c e : ZMod d) (N : XNormal (ZMod d) (n+1)) :
    ∃ (r : AdjacentWord (n+2)) (N' : XNormal (ZMod d) (n+3)),
      AdjacentSymplecticDerives g
        ((XNormal.step c e (.step a b N)).toWord ++
          [.CZ 1 2 (adjacent_ne (1 : Fin (n+2)))])
        (relabel (initialEmbedding (n+2)) r.toWord ++ N'.toWord) := by
  obtain ⟨u, hu, a', b', c', e', hd⟩ := adjacentSymplectic_DD_CZ g a b c e
  obtain ⟨r, hr⟩ := (isAdjacentWord_iff_exists
    (relabel (adjacentPairEmbedding (0 : Fin (n+1))) u)).mp (hu.relabel_adjacentPair 0)
  refine ⟨r, .step c' e' (.step a' b' N), ?_⟩
  have hdp := adjacentSymplecticDerives_triple g (0 : Fin (n+1)) hd
  simp only [relabel_append, relabel_dWord, relabel_cons, relabel_nil, Gate.relabel,
    relabel_triple_initial_zero, adjacentTripleEmbedding_zero, adjacentTripleEmbedding_one,
    adjacentTripleEmbedding_two] at hdp
  let ι := (shiftEmbedding (n+1)).trans (shiftEmbedding (n+2))
  have hi : ∀ i j, ι i ≠ adjacentPairEmbedding (0 : Fin (n+2)) j := by
    intro i j h
    have hv := congrArg Fin.val h
    fin_cases j <;> simp [ι, shiftEmbedding, adjacentPairEmbedding] at hv
  have htadj : IsAdjacentWord (relabel ι N.toWord) := by
    simpa only [ι, relabel_trans] using N.toWord_isAdjacent.shift.shift
  have hc := adjacentDerives_symplectic g
    (adjacentDerives_relabel_interchange g ι (adjacentPairEmbedding (0 : Fin (n+2)))
      hi N.toWord u htadj (hu.relabel_adjacentPair 0))
  have h₁ := hdp.append_left (relabel ι N.toWord)
  have h₂ := hc.append_right
    (dWord a' b' (1 : Fin (n+3)) 2 (adjacent_ne (1 : Fin (n+2))) ++
      dWord c' e' 0 1 (adjacent_ne (0 : Fin (n+2))))
  simp only [List.append_assoc] at h₁ h₂
  simpa only [XNormal.toWord, hr, relabel_initial_pair_zero, relabel_append,
    relabel_dWord, ι, relabel_trans, shiftEmbedding, Function.Embedding.coeFn_mk,
    List.append_assoc] using h₁.trans h₂

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
private theorem dWord_CZ_offwire {n : ℕ} (a b : ZMod d) (k : Fin n) :
    AdjacentDerives g
      (dWord a b (0 : Fin (n+3)) 1 (adjacent_ne (0 : Fin (n+2))) ++
        [.CZ k.succ.succ.castSucc k.succ.succ.succ (adjacent_ne k.succ.succ)])
      ([.CZ k.succ.succ.castSucc k.succ.succ.succ (adjacent_ne k.succ.succ)] ++
        dWord a b (0 : Fin (n+3)) 1 (adjacent_ne (0 : Fin (n+2)))) := by
  have hw : IsAdjacentWord
      (relabel (adjacentPairEmbedding (0 : Fin (n+2)))
        (dWord a b (0 : Fin 2) 1 (by decide))) :=
    (dWord_isAdjacent a b (0 : Fin 1)).relabel_adjacentPair 0
  have h : AdjacentDerives g
      (relabel (adjacentPairEmbedding (0 : Fin (n+2))) (dWord a b (0 : Fin 2) 1 (by decide)) ++
        [.CZ k.succ.succ.castSucc k.succ.succ.succ (adjacent_ne k.succ.succ)])
      ([.CZ k.succ.succ.castSucc k.succ.succ.succ (adjacent_ne k.succ.succ)] ++
        relabel (adjacentPairEmbedding (0 : Fin (n+2))) (dWord a b (0 : Fin 2) 1 (by decide))) := by
    apply adjacentDerives_word_gate_commute g _ _ hw
      (Gate.isAdjacent_CZ k.succ.succ (adjacent_ne k.succ.succ))
    intro x hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    rw [Gate.support_relabel]
    apply Finset.disjoint_left.mpr
    intro z hz hk
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hz
    fin_cases j <;> simp only [adjacentPairEmbedding_zero, adjacentPairEmbedding_one,
      Gate.support, Finset.mem_insert, Finset.mem_singleton] at hk
    all_goals rcases hk with h | h <;> have hv := congrArg Fin.val h <;> simp at hv
  rw [relabel_dWord] at h
  simpa only [adjacentPairEmbedding_zero, adjacentPairEmbedding_one] using h

/-- Every adjacent CZ crosses an arbitrary X-normal sweep, leaving a typed
adjacent residual on one fewer wire and another X-normal sweep. -/
theorem XNormal.adjacentSymplecticDerives_pushCZ {n : ℕ}
    (N : XNormal (ZMod d) (n+1)) (i : Fin n) :
    ∃ (r : AdjacentWord n) (N' : XNormal (ZMod d) (n+1)),
      AdjacentSymplecticDerives g (N.toWord ++ [.CZ i.castSucc i.succ (adjacent_ne i)])
        (relabel (initialEmbedding n) r.toWord ++ N'.toWord) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases N with
    | step c e N =>
      refine Fin.cases ?_ (fun j => ?_) i
      · exact N.adjacentSymplecticDerives_pushCZ_head g c e
      · cases n with
        | zero => exact Fin.elim0 j
        | succ n =>
          refine Fin.cases ?_ (fun k => ?_) j
          · cases N with
            | step a b N => exact N.adjacentSymplecticDerives_pushCZ_second g a b c e
          · obtain ⟨r, N', hr⟩ := ih N k.succ
            refine ⟨r.shift, .step c e N', ?_⟩
            have h₁ := (adjacentDerives_symplectic g (dWord_CZ_offwire g c e k)).append_left
              (relabel (shiftEmbedding _) N.toWord)
            have h₂ := (adjacentSymplecticDerives_shift g hr).append_right
              (dWord c e (0 : Fin (n+3)) 1 (adjacent_ne (0 : Fin (n+2))))
            simp only [relabel_append, relabel_cons, relabel_nil, Gate.relabel,
              List.append_assoc] at h₂
            have ht := h₁.trans h₂
            simpa only [XNormal.toWord, AdjacentWord.toWord_shift, relabel_shift_initial,
              List.append_assoc] using ht

end QuditClifford.NormalBoxes
