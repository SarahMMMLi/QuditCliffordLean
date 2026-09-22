import QuditClifford.AdjacentOneWireRewrites
import QuditClifford.AdjacentTwoWireSyntax
import QuditClifford.AdjacentPresentedCircuit

/-!
# Exact two-wire commutations in the adjacent presentation

All controlled-phase letters retain their canonical operand order. The
second-operand equations are derived through the involutive expanded
SWAP, rather than by introducing a reversed CZ letter.
-/
namespace QuditClifford.Circuit
variable {d n : ℕ} [NeZero d] (g : (ZMod d)ˣ)

/-- Structural interchange is available when both displayed letters are
in the canonical adjacent alphabet. -/
theorem adjacentDerives_disjoint (a b : Gate n) (ha : a.IsAdjacent) (hb : b.IsAdjacent)
    (hab : Disjoint a.support b.support) : AdjacentDerives g [a,b] [b,a] :=
  .rule ⟨Or.inl (.disjoint a b hab), by simpa using And.intro ha hb,
    by simpa using And.intro hb ha⟩

/-- One exact scalar letter commutes with an arbitrary adjacent word. -/
theorem adjacentDerives_scalar_one_commute (w : Word n) (hw : IsAdjacentWord w) :
    AdjacentDerives g ([.scalar]++w) (w++[.scalar]) := by
  induction w with
  | nil => exact .refl _
  | cons a w ih =>
    have ha := hw a (by simp)
    have hw' : IsAdjacentWord w := fun x hx => hw x (by simp [hx])
    have he := adjacentDerives_disjoint g .scalar a Gate.isAdjacent_scalar ha
      (by simp [Gate.support])
    have h₁ := he.append_right w
    have h₂ := (ih hw').append_left [a]
    simpa only [List.singleton_append, List.cons_append, List.nil_append] using h₁.trans h₂

/-- Every power of the exact scalar is central by adjacent structural steps. -/
theorem adjacentDerives_scalar_commute (k : ℕ) (w : Word n) (hw : IsAdjacentWord w) :
    AdjacentDerives g (scalar k++w) (w++scalar k) := by
  induction k with
  | zero => simpa only [scalar, List.replicate_zero, List.nil_append, List.append_nil]
      using (show AdjacentDerives g w w from .refl w)
  | succ k ih =>
    have h₁ := ih.append_left [.scalar]
    have h₂ := (adjacentDerives_scalar_one_commute g w hw).append_right (scalar k)
    simpa only [scalar, List.replicate_succ, List.singleton_append, List.cons_append,
      List.nil_append, List.append_assoc] using h₁.trans h₂

/-- C8 in the source's canonical orientation. -/
theorem adjacentDerives_CZ_S_left (i j : Fin n) (hij : i ≠ j)
    (hadj : (Gate.CZ i j hij).IsAdjacent) :
    AdjacentDerives g [.CZ i j hij, .S i] [.S i, .CZ i j hij] :=
  .rule ⟨Or.inr (.C8 i j hij), by simpa using hadj, by simpa using hadj⟩

/-- Cancel a common right-hand word using an explicitly supplied adjacent
right inverse, keeping every step in sequential contexts. -/
theorem AdjacentDerives.cancel_right_word {u v a r : Word n}
    (h : AdjacentDerives g (u++a) (v++a)) (hr : AdjacentDerives g (a++r) []) :
    AdjacentDerives g u v := by
  have h₁ : AdjacentDerives g u ((u++a)++r) := by
    simpa only [List.append_assoc, List.append_nil] using hr.symm.append_left u
  have h₃ : AdjacentDerives g ((v++a)++r) v := by
    simpa only [List.append_assoc, List.append_nil] using hr.append_left v
  exact h₁.trans ((h.append_right r).trans h₃)

variable [Fact d.Prime] [Fact (Odd d)] [Fact (orderOf g = d-1)]

private theorem H_four_adjacent (i : Fin n) :
    AdjacentDerives g (List.replicate 4 (.H i)) [] := by
  simpa only [relabel, List.map_replicate, List.map_nil, Gate.relabel,
    singleWireEmbedding, Function.Embedding.coeFn_mk] using
    adjacentDerives_singleWire g i (derives_H_four Fact.out g Fact.out (0 : Fin 1))

/-- The expanded SWAP commutes with its canonical CZ by the two restricted
Fourier transports and explicit cancellation of the Fourier pair. -/
theorem adjacentDerives_SWAP_commute_CZ (i j : Fin n) (hij : i ≠ j)
    (hadj : (Gate.CZ i j hij).IsAdjacent) :
    AdjacentDerives g (SWAP (d := d) i j hij++[.CZ i j hij])
      ([.CZ i j hij]++SWAP (d := d) i j hij) := by
  let W := SWAP (d := d) i j hij
  let A : Word n := [.H i, .H j]
  let B : Word n := [.CZ i j hij, .H i, .H j]
  have hB : IsAdjacentWord B := by simpa [B] using hadj
  have hWB : AdjacentDerives g (W++B) (B++W) := by
    have he := (adjacentDerives_scalar_commute g (d*((d-1)/2)) B hB).append_right (power B 3)
    simpa [W, SWAP, B, power, List.append_assoc] using he
  have hWA : AdjacentDerives g (W++A) (A++W) := by
    have h₁ := (adjacentDerives_SWAP_H_left g i j hij hadj).append_right [.H j]
    have h₂ := (adjacentDerives_SWAP_H_right g i j hij hadj).append_left [.H j]
    have h₃ := (adjacentDerives_disjoint g (.H j) (.H i) (Gate.isAdjacent_H j)
      (Gate.isAdjacent_H i) (by simp [Gate.support, hij, hij.symm])).append_right W
    have h₁' : AdjacentDerives g (W++A) ([.H j]++(W++[.H j])) := by
      simpa only [W, A, List.append_assoc, List.singleton_append] using h₁
    have h₂' : AdjacentDerives g ([.H j]++(W++[.H j])) ([.H j,.H i]++W) := by
      simpa only [W, List.singleton_append, List.cons_append, List.nil_append] using h₂
    exact h₁'.trans (h₂'.trans h₃)
  have hCA : AdjacentDerives g ((W++[.CZ i j hij])++A) (([.CZ i j hij]++W)++A) := by
    have he := hWB.trans (by
      simpa only [B, A, List.singleton_append, List.cons_append, List.nil_append,
        List.append_assoc] using hWA.symm.append_left [.CZ i j hij])
    simpa only [A, B, List.append_assoc, List.singleton_append, List.cons_append,
      List.nil_append] using he
  have hAi : AdjacentDerives g (A++[.H j,.H j,.H j,.H i,.H i,.H i]) [] := by
    have hj := (H_four_adjacent g j).context [.H i] [.H i,.H i,.H i]
    have hj' : AdjacentDerives g (A++[.H j,.H j,.H j,.H i,.H i,.H i])
        (List.replicate 4 (.H i)) := by
      simpa [A] using hj
    exact hj'.trans (H_four_adjacent g i)
  exact AdjacentDerives.cancel_right_word g hCA hAi

/-- C8 on the second operand follows from C8 on the first operand through the
involutive expanded SWAP, with no noncanonical CZ spelling. -/
theorem adjacentDerives_CZ_S_right (i j : Fin n) (hij : i ≠ j)
    (hadj : (Gate.CZ i j hij).IsAdjacent) :
    AdjacentDerives g [.CZ i j hij, .S j] [.S j, .CZ i j hij] := by
  let W := SWAP (d := d) i j hij
  have hWC := adjacentDerives_SWAP_commute_CZ g i j hij hadj
  have hWS := adjacentDerives_SWAP_S_right g i j hij hadj
  have hC := adjacentDerives_CZ_S_left g i j hij hadj
  have h₁ : AdjacentDerives g (W++[.CZ i j hij,.S j])
      ([.CZ i j hij]++(W++[.S j])) := by
    simpa only [List.append_assoc, List.singleton_append] using hWC.append_right [.S j]
  have h₂ := hWS.append_left [.CZ i j hij]
  have h₃ := hC.append_right W
  have h₄ := hWC.symm.append_left [.S i]
  have h₅ := hWS.symm.append_right [.CZ i j hij]
  have he : AdjacentDerives g (W++[.CZ i j hij,.S j]) (W++[.S j,.CZ i j hij]) := by
    exact h₁.trans (by
      simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]
        using h₂.trans (h₃.trans (h₄.trans h₅)))
  have hWW := adjacentDerives_SWAP_sq g i j hij hadj
  have he' := he.append_left W
  have hu : AdjacentDerives g ([.CZ i j hij,.S j]) (W++(W++[.CZ i j hij,.S j])) := by
    simpa only [List.append_assoc, List.nil_append] using hWW.symm.append_right [.CZ i j hij,.S j]
  have hv : AdjacentDerives g (W++(W++[.S j,.CZ i j hij])) [.S j,.CZ i j hij] := by
    simpa only [List.append_assoc, List.nil_append] using hWW.append_right [.S j,.CZ i j hij]
  exact hu.trans (he'.trans hv)

private theorem reflect_gate_transport (a : Gate 2) (ha : a.IsAdjacent) :
    AdjacentDerives g (SWAP (d := d) 0 1 (by decide)++[a])
      ([orientTwoGate (a.relabel flipTwo)]++SWAP (d := d) 0 1 (by decide)) := by
  have hadj : (Gate.CZ (0 : Fin 2) 1 (by decide)).IsAdjacent := ⟨.CZ 0, rfl⟩
  cases a with
  | scalar =>
    simpa only [orientTwoGate, Gate.relabel] using
      (adjacentDerives_scalar_one_commute g (SWAP (d := d) 0 1 (by decide))
        (isAdjacentWord_SWAP 0 1 (by decide) hadj)).symm
  | H i =>
    fin_cases i
    · simpa only [Gate.relabel, orientTwoGate, flipTwo_zero] using
        adjacentDerives_SWAP_H_left g 0 1 (by decide) hadj
    · simpa only [Gate.relabel, orientTwoGate, flipTwo_one] using
        adjacentDerives_SWAP_H_right g 0 1 (by decide) hadj
  | S i =>
    fin_cases i
    · simpa only [Gate.relabel, orientTwoGate, flipTwo_zero] using
        adjacentDerives_SWAP_S_left g 0 1 (by decide) hadj
    · simpa only [Gate.relabel, orientTwoGate, flipTwo_one] using
        adjacentDerives_SWAP_S_right g 0 1 (by decide) hadj
  | CZ i j hij =>
    have he : Gate.CZ i j hij=Gate.CZ (0 : Fin 2) 1 (by decide) :=
      (orientTwoGate_eq_of_adjacent _ ha).symm
    rw [he]
    exact adjacentDerives_SWAP_commute_CZ g 0 1 (by decide) hadj

/-- The canonical expanded SWAP transports every canonical two-wire word
to its reflected word, retaining the unique CZ spelling. -/
theorem adjacentDerives_SWAP_reflectTwoWord (w : Word 2) (hw : IsAdjacentWord w) :
    AdjacentDerives g (SWAP (d := d) 0 1 (by decide)++w)
      (reflectTwoWord w++SWAP (d := d) 0 1 (by decide)) := by
  induction w with
  | nil => simpa using (show AdjacentDerives g (SWAP (d := d) 0 1 (by decide))
      (SWAP (d := d) 0 1 (by decide)) from .refl _)
  | cons a w ih =>
    rw [isAdjacentWord_cons] at hw
    have h₁ := (reflect_gate_transport g a hw.1).append_right w
    have h₂ := (ih hw.2).append_left [orientTwoGate (a.relabel flipTwo)]
    have h₁' : AdjacentDerives g (SWAP (d := d) 0 1 (by decide)++(a::w))
        ([orientTwoGate (a.relabel flipTwo)]++(SWAP (d := d) 0 1 (by decide)++w)) := by
      simpa only [List.append_assoc, List.singleton_append] using h₁
    simpa only [reflectTwoWord_cons, List.singleton_append, List.cons_append,
      List.nil_append] using h₁'.trans h₂

/-- Reflection is conjugation by the adjacent SWAP inside the restricted
presentation, proved at the level of literal words. -/
theorem adjacentDerives_SWAP_conjugate_reflectTwoWord (w : Word 2) (hw : IsAdjacentWord w) :
    AdjacentDerives g (SWAP (d := d) 0 1 (by decide)++w++SWAP (d := d) 0 1 (by decide))
      (reflectTwoWord w) := by
  let W := SWAP (d := d) (0 : Fin 2) 1 (by decide)
  have h₁ := (adjacentDerives_SWAP_reflectTwoWord g w hw).append_right W
  have h₂ := (adjacentDerives_SWAP_sq g (0 : Fin 2) 1 (by decide)
    (show (Gate.CZ (0 : Fin 2) 1 (by decide)).IsAdjacent from ⟨.CZ 0, rfl⟩)).append_left
      (reflectTwoWord w)
  have h₂' : AdjacentDerives g ((reflectTwoWord w++W)++W) (reflectTwoWord w) := by
    simpa only [W, List.append_assoc, List.append_nil] using h₂
  exact h₁.trans h₂'

/-- Every already-adjacent derivation can be reflected canonically by SWAP
conjugation. This transports proofs without adding a CZ-symmetry rule. -/
theorem adjacentDerives_reflectTwoWord {u v : Word 2}
    (hu : IsAdjacentWord u) (hv : IsAdjacentWord v) (h : AdjacentDerives g u v) :
    AdjacentDerives g (reflectTwoWord u) (reflectTwoWord v) :=
  (adjacentDerives_SWAP_conjugate_reflectTwoWord g u hu).symm.trans
    ((h.context (SWAP (d := d) 0 1 (by decide)) (SWAP (d := d) 0 1 (by decide))).trans
      (adjacentDerives_SWAP_conjugate_reflectTwoWord g v hv))

/-- Quotient form of the exact restricted SWAP/CZ commutation. -/
theorem adjacentClassWord_SWAP_commute_CZ (i j : Fin n) (hij : i ≠ j)
    (hadj : (Gate.CZ i j hij).IsAdjacent) :
    Commute (adjacentClassWord g (SWAP (d := d) i j hij) (isAdjacentWord_SWAP i j hij hadj))
      (adjacentClassWord g [.CZ i j hij] (by simpa using hadj)) :=
  (adjacentClassWord_eq_iff_derives g _ _ (by simp [hadj, isAdjacentWord_SWAP i j hij hadj])
    (by simp [hadj, isAdjacentWord_SWAP i j hij hadj])).mpr
      (adjacentDerives_SWAP_commute_CZ g i j hij hadj)

omit [Fact d.Prime] [Fact (Odd d)] [Fact (orderOf g = d-1)] in
/-- Quotient form of canonical C8. -/
theorem adjacentClassWord_CZ_commute_S_left (i j : Fin n) (hij : i ≠ j)
    (hadj : (Gate.CZ i j hij).IsAdjacent) :
    Commute (adjacentClassWord g [.CZ i j hij] (by simpa using hadj))
      (adjacentClassWord g [.S i] (by simp)) :=
  (adjacentClassWord_eq_iff_derives g _ _ (by simp [hadj]) (by simp [hadj])).mpr
    (adjacentDerives_CZ_S_left g i j hij hadj)

/-- Quotient form of the derived second-operand C8 equation. -/
theorem adjacentClassWord_CZ_commute_S_right (i j : Fin n) (hij : i ≠ j)
    (hadj : (Gate.CZ i j hij).IsAdjacent) :
    Commute (adjacentClassWord g [.CZ i j hij] (by simpa using hadj))
      (adjacentClassWord g [.S j] (by simp)) :=
  (adjacentClassWord_eq_iff_derives g _ _ (by simp [hadj]) (by simp [hadj])).mpr
    (adjacentDerives_CZ_S_right g i j hij hadj)

end QuditClifford.Circuit
