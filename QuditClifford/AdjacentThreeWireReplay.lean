import QuditClifford.AdjacentThreeWireShuffle
import QuditClifford.AdjacentThreeWireTransport
import QuditClifford.AdjacentSymplecticRewrites

/-!
# Routing three-wire rewrite proofs to adjacent circuits

Wire permutations are implemented by the source's derived adjacent SWAPs.
The compiler therefore transports rule instances by proved conjugations,
without assuming completeness or a remote-CZ coherence equation.
-/
noncomputable section
namespace QuditClifford.Circuit
variable {d : ℕ} [NeZero d] (g : (ZMod d)ˣ)

/-- The routed circuit's class in the actual adjacent presentation. -/
def routeThreeClass (w : Word 3) : AdjacentPresentedCircuit g 3 :=
  adjacentClassWord g (routeThreeWord d w) (routeThreeWord_isAdjacent d w)

@[simp] theorem routeThreeClass_nil : routeThreeClass g [] = 1 := rfl
@[simp] theorem routeThreeClass_append (u v : Word 3) :
    routeThreeClass g (u++v) = routeThreeClass g u * routeThreeClass g v := by
  unfold routeThreeClass
  simp only [routeThreeWord_append, adjacentClassWord_append_certified]

theorem routeThreeClass_cons (a : Gate 3) (w : Word 3) :
    routeThreeClass g (a::w) = routeThreeClass g [a] * routeThreeClass g w :=
  routeThreeClass_append g [a] w

theorem routeThreeClass_eq_of_adjacent (w : Word 3) (hw : IsAdjacentWord w) :
    routeThreeClass g w = adjacentClassWord g w hw := by
  unfold routeThreeClass
  congr 1
  exact routeThreeWord_eq_of_adjacent d w hw

private theorem routeThreeClass_cz (i j : Fin 3) (hij : i ≠ j) :
    routeThreeClass g [.CZ i j hij] =
      if (i=0 ∧ j=2) ∨ (i=2 ∧ j=0) then AdjacentThreeWire.phase02 g
      else if i=0 ∨ j=0 then AdjacentThreeWire.phase01 g else AdjacentThreeWire.phase12 g := by
  unfold routeThreeClass
  simp only [routeThreeWord_cons, routeThreeWord_nil, List.append_nil]
  by_cases hr : (i=0 ∧ j=2) ∨ (i=2 ∧ j=0)
  · simp only [routeThreeGate, if_pos hr]
    exact (AdjacentThreeWire.phase02_classWord g).symm
  · simp only [routeThreeGate, if_neg hr]
    split <;> rfl

variable [Fact d.Prime] [Fact (Odd d)] [Fact (orderOf g = d-1)]

/-- Routed primitives transform naturally under the first adjacent SWAP. -/
theorem routeThreeClass_gate_swap01 (a : Gate 3) :
    routeThreeClass g [a.relabel swapThree01] =
      MulAut.conj (AdjacentThreeWire.swap01 g) (routeThreeClass g [a]) := by
  cases a with
  | scalar => exact (AdjacentThreeWire.swap01_conj_scalar g).symm
  | H i => exact (AdjacentThreeWire.swap01_conj_H g i).symm
  | S i => exact (AdjacentThreeWire.swap01_conj_S g i).symm
  | CZ i j hij =>
      simp only [Gate.relabel, routeThreeClass_cz]
      fin_cases i <;> fin_cases j
      all_goals try exact (hij rfl).elim
      all_goals first
        | exact (AdjacentThreeWire.swap01_conj_phase01 g).symm
        | exact (AdjacentThreeWire.swap01_conj_phase02 g).symm
        | exact (AdjacentThreeWire.swap01_conj_phase12 g).symm

/-- Routed primitives transform naturally under the second adjacent SWAP. -/
theorem routeThreeClass_gate_swap12 (a : Gate 3) :
    routeThreeClass g [a.relabel swapThree12] =
      MulAut.conj (AdjacentThreeWire.swap12 g) (routeThreeClass g [a]) := by
  cases a with
  | scalar => exact (AdjacentThreeWire.swap12_conj_scalar g).symm
  | H i => exact (AdjacentThreeWire.swap12_conj_H g i).symm
  | S i => exact (AdjacentThreeWire.swap12_conj_S g i).symm
  | CZ i j hij =>
      simp only [Gate.relabel, routeThreeClass_cz]
      fin_cases i <;> fin_cases j
      all_goals try exact (hij rfl).elim
      all_goals first
        | exact (AdjacentThreeWire.swap12_conj_phase01 g).symm
        | exact (AdjacentThreeWire.swap12_conj_phase02 g).symm
        | exact (AdjacentThreeWire.swap12_conj_phase12 g).symm

theorem routeThreeClass_relabel_swap01 (w : Word 3) :
    routeThreeClass g (relabel swapThree01 w) =
      MulAut.conj (AdjacentThreeWire.swap01 g) (routeThreeClass g w) := by
  induction w with
  | nil => simp only [relabel_nil, routeThreeClass_nil, map_one]
  | cons a w ih =>
      calc
        routeThreeClass g (relabel swapThree01 (a::w)) =
            routeThreeClass g [a.relabel swapThree01] *
              routeThreeClass g (relabel swapThree01 w) := routeThreeClass_cons g _ _
        _ = MulAut.conj (AdjacentThreeWire.swap01 g) (routeThreeClass g [a]) *
              MulAut.conj (AdjacentThreeWire.swap01 g) (routeThreeClass g w) := by
              rw [routeThreeClass_gate_swap01, ih]
        _ = MulAut.conj (AdjacentThreeWire.swap01 g)
              (routeThreeClass g [a] * routeThreeClass g w) := (map_mul _ _ _).symm
        _ = _ := congrArg _ (routeThreeClass_cons g a w).symm

theorem routeThreeClass_relabel_swap12 (w : Word 3) :
    routeThreeClass g (relabel swapThree12 w) =
      MulAut.conj (AdjacentThreeWire.swap12 g) (routeThreeClass g w) := by
  induction w with
  | nil => simp only [relabel_nil, routeThreeClass_nil, map_one]
  | cons a w ih =>
      calc
        routeThreeClass g (relabel swapThree12 (a::w)) =
            routeThreeClass g [a.relabel swapThree12] *
              routeThreeClass g (relabel swapThree12 w) := routeThreeClass_cons g _ _
        _ = MulAut.conj (AdjacentThreeWire.swap12 g) (routeThreeClass g [a]) *
              MulAut.conj (AdjacentThreeWire.swap12 g) (routeThreeClass g w) := by
              rw [routeThreeClass_gate_swap12, ih]
        _ = MulAut.conj (AdjacentThreeWire.swap12 g)
              (routeThreeClass g [a] * routeThreeClass g w) := (map_mul _ _ _).symm
        _ = _ := congrArg _ (routeThreeClass_cons g a w).symm

/-- Every finite adjacent wire shuffle acts by an explicit inner automorphism. -/
theorem routeThreeClass_shuffle (s : List Bool) :
    ∃ A : MulAut (AdjacentPresentedCircuit g 3), ∀ w : Word 3,
      routeThreeClass g (relabel (threeShuffle s) w) = A (routeThreeClass g w) := by
  induction s with
  | nil => exact ⟨MulEquiv.refl _, fun w => by simp [threeShuffle]⟩
  | cons b s ih =>
      obtain ⟨A, hA⟩ := ih
      cases b with
      | false =>
          refine ⟨A.trans (MulAut.conj (AdjacentThreeWire.swap01 g)), ?_⟩
          intro w
          simp only [threeShuffle, relabel_trans, routeThreeClass_relabel_swap01, hA, MulEquiv.trans_apply]
      | true =>
          refine ⟨A.trans (MulAut.conj (AdjacentThreeWire.swap12 g)), ?_⟩
          intro w
          simp only [threeShuffle, relabel_trans, routeThreeClass_relabel_swap12, hA, MulEquiv.trans_apply]

private theorem cx01_adj : IsAdjacentWord (CX (0 : Fin 3) 1 (by decide)) :=
  isAdjacentWord_CX_neighbor 0

omit [Fact d.Prime] [Fact (Odd d)] [Fact (orderOf g = d-1)] in
/-- Every printed schema can be moved to its canonical neighboring locations. -/
private theorem figure1_three_local {u v : Word 3} (h : Figure1Rule g u v) :
    ∃ s : List Bool, IsAdjacentWord (relabel (threeShuffle s) u) ∧
      IsAdjacentWord (relabel (threeShuffle s) v) := by
  cases h with
  | C0 => exact ⟨[], by simp, by simp⟩
  | C1 i => exact ⟨[], by simpa only [threeShuffle, relabel_refl] using
      IsAdjacentWord.replicate (Gate.isAdjacent_S i) d, by simp⟩
  | C2 i => exact ⟨[], by simp [Gate.relabel], by simp⟩
  | C3 i k => exact ⟨[], by simp [IsAdjacentWord.power], by simp⟩
  | C4 i =>
      refine ⟨[], ?_, ?_⟩
      all_goals simp only [threeShuffle, relabel_refl, isAdjacentWord_append,
        isAdjacentWord_cons, isAdjacentWord_nil, Gate.isAdjacent_S,
        isAdjacentWord_multiplier, isAdjacentWord_Zexp, isAdjacentWord_Sexp, and_self]
  | C5 i => exact ⟨[], by simp [Gate.relabel], by simp [Gate.relabel]⟩
  | C6 i j hij | C7 i j hij | C8 i j hij | C9 i j hij |
    C10 i j hij | C11 i j hij | C12 i j hij =>
      obtain ⟨s, hi, hj⟩ := threeShuffle_pair i j hij
      refine ⟨s, ?_, ?_⟩
      all_goals simp only [relabel_append, relabel_cons, relabel_nil, relabel_scalar,
        relabel_replicate, relabel_power, relabel_SWAP, relabel_CX, relabel_multiplier,
        relabel_Sexp, relabel_Zexp, Gate.relabel, hi, hj]
      all_goals simp only [isAdjacentWord_append, isAdjacentWord_cons,
        isAdjacentWord_nil, Gate.isAdjacent_S, Gate.isAdjacent_H,
        isAdjacentWord_multiplier, isAdjacentWord_Zexp, isAdjacentWord_Sexp,
        AdjacentThreeWire.cz01_adj, AdjacentThreeWire.swap01_adj,
        cx01_adj, IsAdjacentWord.power, IsAdjacentWord.replicate, and_self, true_and, and_true]
  | C13 i j k hij hjk hik | C14 i j k hij hjk hik | C15 i j k hij hjk hik =>
      obtain ⟨s, hi, hj, hk⟩ := threeShuffle_triple i j k hij hjk hik
      refine ⟨s, ?_, ?_⟩
      all_goals simp only [relabel_append, relabel_cons, relabel_nil, relabel_SWAP,
        relabel_CX, relabel_CIZ, Gate.relabel, hi, hj, hk]
      all_goals simp [AdjacentThreeWire.cz01_adj, AdjacentThreeWire.cz12_adj,
        AdjacentThreeWire.swap01_adj, AdjacentThreeWire.swap12_adj, cx01_adj,
        AdjacentThreeWire.remote_adj]

private theorem routeThreeClass_of_local {u v : Word 3}
    (h : Rules g u v) (s : List Bool)
    (hu : IsAdjacentWord (relabel (threeShuffle s) u))
    (hv : IsAdjacentWord (relabel (threeShuffle s) v)) :
    routeThreeClass g u = routeThreeClass g v := by
  have he : AdjacentDerives g (relabel (threeShuffle s) u) (relabel (threeShuffle s) v) :=
    .rule ⟨h.elim (fun hs => Or.inl (hs.relabel _))
      (fun hf => Or.inr (hf.relabel g _)), hu, hv⟩
  have hq := (adjacentClassWord_eq_iff_derives g _ _ hu hv).mpr he
  rw [← routeThreeClass_eq_of_adjacent g _ hu,
    ← routeThreeClass_eq_of_adjacent g _ hv] at hq
  obtain ⟨A, hA⟩ := routeThreeClass_shuffle g s
  rw [hA, hA] at hq
  exact A.injective hq

private theorem routeThreeClass_figure1 {u v : Word 3} (h : Figure1Rule g u v) :
    routeThreeClass g u = routeThreeClass g v := by
  obtain ⟨s, hu, hv⟩ := figure1_three_local g h
  exact routeThreeClass_of_local g (Or.inr h) s hu hv

private theorem disjoint_three_local (a b : Gate 3) (hab : Disjoint a.support b.support) :
    ∃ s : List Bool, IsAdjacentWord (relabel (threeShuffle s) [a,b]) ∧
      IsAdjacentWord (relabel (threeShuffle s) [b,a]) := by
  cases a with
  | scalar | H i | S i =>
      cases b with
      | scalar | H j | S j => exact ⟨[], by simp [Gate.relabel], by simp [Gate.relabel]⟩
      | CZ j k hjk =>
          obtain ⟨s, hj, hk⟩ := threeShuffle_pair j k hjk
          exact ⟨s, by simp [Gate.relabel, hj, hk, AdjacentThreeWire.cz01_adj],
            by simp [Gate.relabel, hj, hk, AdjacentThreeWire.cz01_adj]⟩
  | CZ i j hij =>
      cases b with
      | scalar | H k | S k =>
          obtain ⟨s, hi, hj⟩ := threeShuffle_pair i j hij
          exact ⟨s, by simp [Gate.relabel, hi, hj, AdjacentThreeWire.cz01_adj],
            by simp [Gate.relabel, hi, hj, AdjacentThreeWire.cz01_adj]⟩
      | CZ k l hkl =>
          have hnone : ∀ i j k l : Fin 3, i ≠ j → k ≠ l →
              ¬ Disjoint ({i,j} : Finset (Fin 3)) {k,l} := by decide
          exact (hnone i j k l hij hkl hab).elim

private theorem routeThreeClass_structural {u v : Word 3} (h : Structural u v) :
    routeThreeClass g u = routeThreeClass g v := by
  cases h with
  | CZ_symmetry i j hij =>
      simp only [routeThreeClass_cz]
      congr 1 <;> simp only [and_comm, or_comm]
  | disjoint a b hab =>
      obtain ⟨s, hu, hv⟩ := disjoint_three_local a b hab
      exact routeThreeClass_of_local g (Or.inl (.disjoint a b hab)) s hu hv

/-- Every exact three-wire helper proof survives canonical adjacent routing. -/
theorem adjacentDerives_routeThreeWord {u v : Word 3} (h : Derives g u v) :
    AdjacentDerives g (routeThreeWord d u) (routeThreeWord d v) := by
  apply (adjacentClassWord_eq_iff_derives g _ _
    (routeThreeWord_isAdjacent d u) (routeThreeWord_isAdjacent d v)).mp
  change routeThreeClass g u = routeThreeClass g v
  induction h with
  | refl w => rfl
  | rule h => exact h.elim (routeThreeClass_structural g) (routeThreeClass_figure1 g)
  | symm h ih => exact ih.symm
  | trans h k ih ik => exact ih.trans ik
  | context l r h ih => simp only [routeThreeClass_append, ih]

/-- Canonical three-wire endpoints need no compilation in the final statement. -/
theorem adjacentDerives_of_threeWire {u v : Word 3}
    (hu : IsAdjacentWord u) (hv : IsAdjacentWord v) (h : Derives g u v) :
    AdjacentDerives g u v := by
  have he := adjacentDerives_routeThreeWord g h
  simpa only [routeThreeWord_eq_of_adjacent d u hu, routeThreeWord_eq_of_adjacent d v hv] using he

private theorem routeThree_symplecticRules {u v : Word 3} (h : SymplecticRules g u v) :
    AdjacentSymplecticDerives g (routeThreeWord d u) (routeThreeWord d v) := by
  rcases h with (he | ⟨rfl, rfl⟩) | ⟨i, (rfl | rfl), rfl⟩
  · exact adjacentDerives_symplectic g (adjacentDerives_routeThreeWord g (.rule he))
  · rw [routeThreeWord_eq_of_adjacent d [.scalar] (by simp), routeThreeWord_nil]
    exact .rule ⟨Or.inl (Or.inr ⟨rfl, rfl⟩), by simp, by simp⟩
  · rw [routeThreeWord_eq_of_adjacent d (X i) (isAdjacentWord_X i), routeThreeWord_nil]
    exact .rule ⟨Or.inr ⟨i, Or.inl rfl, rfl⟩, isAdjacentWord_X i, isAdjacentWord_nil⟩
  · rw [routeThreeWord_eq_of_adjacent d (Z i) (isAdjacentWord_Z i), routeThreeWord_nil]
    exact .rule ⟨Or.inr ⟨i, Or.inr rfl, rfl⟩, isAdjacentWord_Z i, isAdjacentWord_nil⟩

/-- Three-wire proofs with explicit scalar/Pauli erasure also survive routing. -/
theorem adjacentSymplecticDerives_routeThreeWord {u v : Word 3}
    (h : SymplecticDerives g u v) :
    AdjacentSymplecticDerives g (routeThreeWord d u) (routeThreeWord d v) := by
  induction h with
  | refl w => exact .refl _
  | rule h => exact routeThree_symplecticRules g h
  | symm h ih => exact ih.symm
  | trans h k ih ik => exact ih.trans ik
  | context l r h ih =>
      simpa only [routeThreeWord_append] using
        ih.context (routeThreeWord d l) (routeThreeWord d r)

/-- Replay an erased three-wire box proof with canonical adjacent endpoints. -/
theorem adjacentSymplecticDerives_of_threeWire {u v : Word 3}
    (hu : IsAdjacentWord u) (hv : IsAdjacentWord v) (h : SymplecticDerives g u v) :
    AdjacentSymplecticDerives g u v := by
  have he := adjacentSymplecticDerives_routeThreeWord g h
  simpa only [routeThreeWord_eq_of_adjacent d u hu, routeThreeWord_eq_of_adjacent d v hv] using he

/-- The exact helper and source relations agree on canonical three-wire words. -/
theorem adjacentDerives_iff_threeWire {u v : Word 3}
    (hu : IsAdjacentWord u) (hv : IsAdjacentWord v) :
    AdjacentDerives g u v ↔ Derives g u v :=
  ⟨AdjacentDerives.toDerives g, adjacentDerives_of_threeWire g hu hv⟩

/-- The explicitly erased relations agree on canonical three-wire words. -/
theorem adjacentSymplecticDerives_iff_threeWire {u v : Word 3}
    (hu : IsAdjacentWord u) (hv : IsAdjacentWord v) :
    AdjacentSymplecticDerives g u v ↔ SymplecticDerives g u v :=
  ⟨AdjacentSymplecticDerives.toSymplecticDerives g, adjacentSymplecticDerives_of_threeWire g hu hv⟩

end QuditClifford.Circuit
