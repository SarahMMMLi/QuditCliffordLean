import QuditClifford.AdjacentTwoWireReplay
import QuditClifford.AdjacentOneWireAlgebra
import QuditClifford.SymplecticTwoWireABNonzero
import QuditClifford.SymplecticTwoWireDCZ

/-!
# The one- and two-wire Appendix F branches in the adjacent presentation

The six one-wire branches are replayed from `Word 1` on any chosen wire.
The 26 two-wire printed branches are replayed on the canonical pair `0,1`.
Every intermediate step is transported by the proved restricted replay
maps. Exact branches remain exact; other branches explicitly use the
scalar/Pauli-erased relation. No three-wire replay or normalization theorem
is asserted here.

Coverage: A/E 6, A/CZ 2, B/H/S 9, D/H/S/CZ 9, AB/CZ 6. The uniform
B lower-S zero-a theorem covers its nonzero-b printed row as well as b=0;
the separately named zero/zero branch retains the exact equation. Likewise
the AB zero-a/zero-c formula covers arbitrary k; its k=0 printed row has a
separate simplified wrapper.
-/
noncomputable section
namespace QuditClifford.NormalBoxes
open Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ)

/-- Restricted replay of `derives_A_H_zero`. -/
theorem adjacentDerives_A_H_zero (A : ABox (ZMod d))
    (ha : A.a = 0) (i : Fin n) :
    AdjacentDerives g (A.toWord i ++ [.H i]) ((A.hadamardZero ha).toWord i) := by
  simpa only [relabel_append, ABox.relabel_toWord, relabel_eWord, relabel_Sexp,
    relabel_cons, relabel_nil, Gate.relabel, singleWireEmbedding,
    Function.Embedding.coeFn_mk] using
    adjacentDerives_singleWire g i (derives_A_H_zero g A ha (0 : Fin 1))

/-- Restricted replay of `derives_A_S_nonzero`. -/
theorem adjacentDerives_A_S_nonzero (A : ABox (ZMod d))
    (ha : A.a ≠ 0) (i : Fin n) :
    AdjacentDerives g (A.toWord i ++ [.S i]) ((A.phaseStep ha).toWord i) := by
  simpa only [relabel_append, ABox.relabel_toWord, relabel_eWord, relabel_Sexp,
    relabel_cons, relabel_nil, Gate.relabel, singleWireEmbedding,
    Function.Embedding.coeFn_mk] using
    adjacentDerives_singleWire g i (derives_A_S_nonzero g A ha (0 : Fin 1))

/-- Restricted replay of `derives_E_S`. -/
theorem adjacentDerives_E_S (b : ZMod d) (i : Fin n) :
    AdjacentDerives g (eWord b i ++ [.S i]) (eWord (b-1) i) := by
  simpa only [relabel_append, ABox.relabel_toWord, relabel_eWord, relabel_Sexp,
    relabel_cons, relabel_nil, Gate.relabel, singleWireEmbedding,
    Function.Embedding.coeFn_mk] using
    adjacentDerives_singleWire g i (derives_E_S g b (0 : Fin 1))

variable [Fact (Odd d)] [Fact (orderOf g = d-1)]

/-- Restricted replay of `symplectic_A_H_nonzero_zero`. -/
theorem adjacentSymplectic_A_H_nonzero_zero (A : ABox (ZMod d))
    (ha : A.a ≠ 0) (hb : A.b = 0) (i : Fin n) :
    AdjacentSymplecticDerives g (A.toWord i ++ [.H i]) (A.hadamardStep.toWord i) := by
  simpa only [relabel_append, ABox.relabel_toWord, relabel_eWord, relabel_Sexp,
    relabel_cons, relabel_nil, Gate.relabel, singleWireEmbedding,
    Function.Embedding.coeFn_mk] using
    adjacentSymplecticDerives_singleWire g i (symplectic_A_H_nonzero_zero g A ha hb (0 : Fin 1))

omit [Fact (Odd d)] in
/-- Restricted replay of `symplectic_A_S_zero`. -/
theorem adjacentSymplectic_A_S_zero (A : ABox (ZMod d))
    (ha : A.a = 0) (i : Fin n) :
    AdjacentSymplecticDerives g (A.toWord i ++ [.S i])
      (Sexp i (A.b⁻¹^2) ++ A.toWord i) := by
  simpa only [relabel_append, ABox.relabel_toWord, relabel_eWord, relabel_Sexp,
    relabel_cons, relabel_nil, Gate.relabel, singleWireEmbedding,
    Function.Embedding.coeFn_mk] using
    adjacentSymplecticDerives_singleWire g i (symplectic_A_S_zero g A ha (0 : Fin 1))

/-- Restricted replay of `symplectic_A_H_nonzero_nonzero`. -/
theorem adjacentSymplectic_A_H_nonzero_nonzero (A : ABox (ZMod d))
    (ha : A.a ≠ 0) (hb : A.b ≠ 0) (i : Fin n) :
    AdjacentSymplecticDerives g (A.toWord i ++ [.H i])
      (Sexp i ((A.a*A.b)⁻¹) ++ A.hadamardStep.toWord i) := by
  simpa only [relabel_append, ABox.relabel_toWord, relabel_eWord, relabel_Sexp,
    relabel_cons, relabel_nil, Gate.relabel, singleWireEmbedding,
    Function.Embedding.coeFn_mk] using
    adjacentSymplecticDerives_singleWire g i (symplectic_A_H_nonzero_nonzero g A ha hb (0 : Fin 1))

omit [NeZero d] [Fact (Odd d)] in
private theorem b_adj (a b : ZMod d) :
    IsAdjacentWord (bWord a b (0 : Fin 2) 1 (by decide)) := bWord_isAdjacent a b 0

omit [NeZero d] [Fact (Odd d)] in
private theorem d_adj (a b : ZMod d) :
    IsAdjacentWord (dWord a b (0 : Fin 2) 1 (by decide)) := dWord_isAdjacent a b 0

private theorem cz_adj : (Gate.CZ (0 : Fin 2) 1 (by decide)).IsAdjacent := ⟨.CZ 0, rfl⟩

attribute [local simp] b_adj d_adj cz_adj ABox.toWord_isAdjacent
  IsAdjacentWord.replicate IsAdjacentWord.inverseWord

/-- Restricted replay of `derives_A_CZ_zero` on the canonical pair. -/
theorem adjacentDerives_A_CZ_zero (A : ABox (ZMod d)) (ha : A.a=0) :
    AdjacentDerives g (A.toWord (0 : Fin 2) ++ [.CZ (0 : Fin 2) (1 : Fin 2) (by decide)])
      (List.replicate (A.b⁻¹).val (.CZ (0 : Fin 2) (1 : Fin 2) (by decide)) ++ A.toWord (0 : Fin 2)) :=
  adjacentDerives_of_twoWire g (by simp [Gate.inverseWord]) (by simp [Gate.inverseWord])
    (derives_A_CZ_zero g A ha (0 : Fin 2) 1 (by decide))

/-- Restricted replay of `symplecticDerives_A_CZ_nonzero` on the canonical pair. -/
theorem adjacentSymplecticDerives_A_CZ_nonzero (A : ABox (ZMod d)) (ha : A.a ≠ 0) :
    AdjacentSymplecticDerives g (A.toWord (0 : Fin 2) ++ [.CZ (0 : Fin 2) (1 : Fin 2) (by decide)])
      ([.H (1 : Fin 2)] ++ List.replicate (A.a⁻¹).val (.CZ (0 : Fin 2) (1 : Fin 2) (by decide)) ++ List.replicate 3 (.H (1 : Fin 2)) ++
        bWord A.a A.b (0 : Fin 2) (1 : Fin 2) (by decide) ++ (A.controlledPhaseStep ha).toWord (1 : Fin 2)) :=
  adjacentSymplecticDerives_of_twoWire g (by simp [Gate.inverseWord]) (by simp [Gate.inverseWord])
    (symplecticDerives_A_CZ_nonzero g A ha (0 : Fin 2) 1 (by decide))

/-- Restricted replay of `derives_B_H_zero_zero` on the canonical pair. -/
theorem adjacentDerives_B_H_zero_zero :
    AdjacentDerives g (bWord (0 : ZMod d) 0 (0 : Fin 2) (1 : Fin 2) (by decide) ++ [.H (0 : Fin 2)])
      ([.H (1 : Fin 2)] ++ bWord (0 : ZMod d) 0 (0 : Fin 2) (1 : Fin 2) (by decide)) :=
  adjacentDerives_of_twoWire g (by simp [Gate.inverseWord]) (by simp [Gate.inverseWord])
    (derives_B_H_zero_zero g  (0 : Fin 2) 1 (by decide))

/-- Restricted replay of `derives_B_H_zero_nonzero` on the canonical pair. -/
theorem adjacentDerives_B_H_zero_nonzero (b : ZMod d) (hb : b ≠ 0) :
    AdjacentDerives g (bWord 0 b (0 : Fin 2) (1 : Fin 2) (by decide) ++ [.H (0 : Fin 2)]) (bWord b 0 (0 : Fin 2) (1 : Fin 2) (by decide)) :=
  adjacentDerives_of_twoWire g (by simp [Gate.inverseWord]) (by simp [Gate.inverseWord])
    (derives_B_H_zero_nonzero g b hb (0 : Fin 2) 1 (by decide))

/-- Restricted replay of `derives_B_H_nonzero_zero` on the canonical pair. -/
theorem adjacentDerives_B_H_nonzero_zero (a : ZMod d) (ha : a ≠ 0) :
    AdjacentDerives g (bWord a 0 (0 : Fin 2) (1 : Fin 2) (by decide) ++ [.H (0 : Fin 2)])
      ([.H (1 : Fin 2), .H (1 : Fin 2)] ++ bWord 0 (-a) (0 : Fin 2) (1 : Fin 2) (by decide)) :=
  adjacentDerives_of_twoWire g (by simp [Gate.inverseWord]) (by simp [Gate.inverseWord])
    (derives_B_H_nonzero_zero g a ha (0 : Fin 2) 1 (by decide))

/-- Restricted replay of `symplecticDerives_B_H_nonzero_nonzero_source` on the canonical pair. -/
theorem adjacentSymplecticDerives_B_H_nonzero_nonzero_source (a b : ZMod d) (ha : a ≠ 0) (hb : b ≠ 0) :
    AdjacentSymplecticDerives g (bWord a b (0 : Fin 2) (1 : Fin 2) (by decide) ++ [.H (0 : Fin 2)])
      (Circuit.multiplier (1 : Fin 2) (Units.mk0 (b/a) (div_ne_zero hb ha)) ++ Sexp (1 : Fin 2) (b/a) ++
        bWord b (-a) (0 : Fin 2) (1 : Fin 2) (by decide)) :=
  adjacentSymplecticDerives_of_twoWire g (by simp [Gate.inverseWord]) (by simp [Gate.inverseWord])
    (symplecticDerives_B_H_nonzero_nonzero_source g a b ha hb (0 : Fin 2) 1 (by decide))

/-- Restricted replay of `derives_B_S_left_zero` on the canonical pair. -/
theorem adjacentDerives_B_S_left_zero (b : ZMod d) :
    AdjacentDerives g (bWord 0 b (0 : Fin 2) (1 : Fin 2) (by decide) ++ [.S (0 : Fin 2)]) ([.S (1 : Fin 2)] ++ bWord 0 b (0 : Fin 2) (1 : Fin 2) (by decide)) :=
  adjacentDerives_of_twoWire g (by simp [Gate.inverseWord]) (by simp [Gate.inverseWord])
    (derives_B_S_left_zero g b (0 : Fin 2) 1 (by decide))

/-- Restricted replay of `derives_B_S_left_nonzero` on the canonical pair. -/
theorem adjacentDerives_B_S_left_nonzero (a b : ZMod d) (ha : a ≠ 0) :
    AdjacentDerives g (bWord a b (0 : Fin 2) (1 : Fin 2) (by decide) ++ [.S (0 : Fin 2)]) (bWord a (b-a) (0 : Fin 2) (1 : Fin 2) (by decide)) :=
  adjacentDerives_of_twoWire g (by simp [Gate.inverseWord]) (by simp [Gate.inverseWord])
    (derives_B_S_left_nonzero g a b ha (0 : Fin 2) 1 (by decide))

/-- Restricted replay of `derives_B_S_right_zero_zero` on the canonical pair. -/
theorem adjacentDerives_B_S_right_zero_zero :
    AdjacentDerives g (bWord (0 : ZMod d) 0 (0 : Fin 2) (1 : Fin 2) (by decide) ++ [.S (1 : Fin 2)])
      ([.S (0 : Fin 2)] ++ bWord (0 : ZMod d) 0 (0 : Fin 2) (1 : Fin 2) (by decide)) :=
  adjacentDerives_of_twoWire g (by simp [Gate.inverseWord]) (by simp [Gate.inverseWord])
    (derives_B_S_right_zero_zero g  (0 : Fin 2) 1 (by decide))

/-- Restricted replay of `symplecticDerives_B_S_right_zero` on the canonical pair. -/
theorem adjacentSymplecticDerives_B_S_right_zero (b : ZMod d) :
    AdjacentSymplecticDerives g (bWord 0 b (0 : Fin 2) (1 : Fin 2) (by decide) ++ [.S (1 : Fin 2)])
      ([.S (0 : Fin 2)] ++ Sexp (1 : Fin 2) (b*b) ++ List.replicate (-b).val (.CZ (0 : Fin 2) (1 : Fin 2) (by decide)) ++
        bWord 0 b (0 : Fin 2) (1 : Fin 2) (by decide)) :=
  adjacentSymplecticDerives_of_twoWire g (by simp [Gate.inverseWord]) (by simp [Gate.inverseWord])
    (symplecticDerives_B_S_right_zero g b (0 : Fin 2) 1 (by decide))

/-- Restricted replay of `symplecticDerives_B_S_right_nonzero` on the canonical pair. -/
theorem adjacentSymplecticDerives_B_S_right_nonzero (a b : ZMod d) (ha : a ≠ 0) :
    AdjacentSymplecticDerives g (bWord a b (0 : Fin 2) (1 : Fin 2) (by decide) ++ [.S (1 : Fin 2)])
      ([.S (0 : Fin 2)] ++ Sexp (1 : Fin 2) (a*a) ++ List.replicate (-a).val (.CZ (0 : Fin 2) (1 : Fin 2) (by decide)) ++
        bWord a b (0 : Fin 2) (1 : Fin 2) (by decide)) :=
  adjacentSymplecticDerives_of_twoWire g (by simp [Gate.inverseWord]) (by simp [Gate.inverseWord])
    (symplecticDerives_B_S_right_nonzero g a b ha (0 : Fin 2) 1 (by decide))

/-- Restricted replay of `derives_D_H_zero_zero` on the canonical pair. -/
theorem adjacentDerives_D_H_zero_zero :
    AdjacentDerives g (dWord (0 : ZMod d) 0 (0 : Fin 2) (1 : Fin 2) (by decide) ++ [.H (1 : Fin 2)])
      ([.H (0 : Fin 2)] ++ dWord (0 : ZMod d) 0 (0 : Fin 2) (1 : Fin 2) (by decide)) :=
  adjacentDerives_of_twoWire g (by simp [Gate.inverseWord]) (by simp [Gate.inverseWord])
    (derives_D_H_zero_zero g  (0 : Fin 2) 1 (by decide))

/-- Restricted replay of `derives_D_H_zero_nonzero` on the canonical pair. -/
theorem adjacentDerives_D_H_zero_nonzero (b : ZMod d) (hb : b ≠ 0) :
    AdjacentDerives g (dWord 0 b (0 : Fin 2) (1 : Fin 2) (by decide) ++ [.H (1 : Fin 2)]) (dWord b 0 (0 : Fin 2) (1 : Fin 2) (by decide)) :=
  adjacentDerives_of_twoWire g (by simp [Gate.inverseWord]) (by simp [Gate.inverseWord])
    (derives_D_H_zero_nonzero g b hb (0 : Fin 2) 1 (by decide))

/-- Restricted replay of `derives_D_H_nonzero_zero` on the canonical pair. -/
theorem adjacentDerives_D_H_nonzero_zero (a : ZMod d) (ha : a ≠ 0) :
    AdjacentDerives g (dWord a 0 (0 : Fin 2) (1 : Fin 2) (by decide) ++ [.H (1 : Fin 2)])
      (List.replicate 2 (.H (0 : Fin 2)) ++ dWord 0 (-a) (0 : Fin 2) (1 : Fin 2) (by decide)) :=
  adjacentDerives_of_twoWire g (by simp [Gate.inverseWord]) (by simp [Gate.inverseWord])
    (derives_D_H_nonzero_zero g a ha (0 : Fin 2) 1 (by decide))

/-- Restricted replay of `symplectic_D_H_nonzero_nonzero_source` on the canonical pair. -/
theorem adjacentSymplectic_D_H_nonzero_nonzero_source (a b : ZMod d) (ha : a ≠ 0) (hb : b ≠ 0) :
    AdjacentSymplecticDerives g (dWord a b (0 : Fin 2) (1 : Fin 2) (by decide) ++ [.H (1 : Fin 2)])
      (Circuit.multiplier (0 : Fin 2) (Units.mk0 (b/a) (div_ne_zero hb ha)) ++ Sexp (0 : Fin 2) (b/a) ++
        dWord b (-a) (0 : Fin 2) (1 : Fin 2) (by decide)) :=
  adjacentSymplecticDerives_of_twoWire g (by simp [Gate.inverseWord]) (by simp [Gate.inverseWord])
    (symplectic_D_H_nonzero_nonzero_source g a b ha hb (0 : Fin 2) 1 (by decide))

/-- Restricted replay of `derives_D_S_right_zero` on the canonical pair. -/
theorem adjacentDerives_D_S_right_zero (b : ZMod d) :
    AdjacentDerives g (dWord 0 b (0 : Fin 2) (1 : Fin 2) (by decide) ++ [.S (1 : Fin 2)]) ([.S (0 : Fin 2)] ++ dWord 0 b (0 : Fin 2) (1 : Fin 2) (by decide)) :=
  adjacentDerives_of_twoWire g (by simp [Gate.inverseWord]) (by simp [Gate.inverseWord])
    (derives_D_S_right_zero g b (0 : Fin 2) 1 (by decide))

/-- Restricted replay of `derives_D_S_right_nonzero` on the canonical pair. -/
theorem adjacentDerives_D_S_right_nonzero (a b : ZMod d) (ha : a ≠ 0) :
    AdjacentDerives g (dWord a b (0 : Fin 2) (1 : Fin 2) (by decide) ++ [.S (1 : Fin 2)]) (dWord a (b-a) (0 : Fin 2) (1 : Fin 2) (by decide)) :=
  adjacentDerives_of_twoWire g (by simp [Gate.inverseWord]) (by simp [Gate.inverseWord])
    (derives_D_S_right_nonzero g a b ha (0 : Fin 2) 1 (by decide))

/-- Restricted replay of `derives_D_S_left` on the canonical pair. -/
theorem adjacentDerives_D_S_left (a b : ZMod d) :
    AdjacentDerives g (dWord a b (0 : Fin 2) (1 : Fin 2) (by decide) ++ [.S (0 : Fin 2)]) ([.S (1 : Fin 2)] ++ dWord a b (0 : Fin 2) (1 : Fin 2) (by decide)) :=
  adjacentDerives_of_twoWire g (by simp [Gate.inverseWord]) (by simp [Gate.inverseWord])
    (derives_D_S_left g a b (0 : Fin 2) 1 (by decide))

/-- Restricted replay of `derives_D_CZ_zero` on the canonical pair. -/
theorem adjacentDerives_D_CZ_zero (b : ZMod d) :
    AdjacentDerives g (dWord 0 b (0 : Fin 2) (1 : Fin 2) (by decide) ++ [.CZ (0 : Fin 2) (1 : Fin 2) (by decide)]) (dWord 0 (b-1) (0 : Fin 2) (1 : Fin 2) (by decide)) :=
  adjacentDerives_of_twoWire g (by simp [Gate.inverseWord]) (by simp [Gate.inverseWord])
    (derives_D_CZ_zero g b (0 : Fin 2) 1 (by decide))

/-- Restricted replay of `symplectic_D_CZ_nonzero` on the canonical pair. -/
theorem adjacentSymplectic_D_CZ_nonzero (a b : ZMod d) (ha : a ≠ 0) :
    AdjacentSymplecticDerives g (dWord a b (0 : Fin 2) (1 : Fin 2) (by decide) ++ [.CZ (0 : Fin 2) (1 : Fin 2) (by decide)])
      (Sexp (1 : Fin 2) a ++ [.H (0 : Fin 2)] ++ Sexp (0 : Fin 2) (-a⁻¹) ++ inverseWord d [.H (0 : Fin 2)] ++
        dWord a (b-1) (0 : Fin 2) (1 : Fin 2) (by decide)) :=
  adjacentSymplecticDerives_of_twoWire g (by simp [Gate.inverseWord]) (by simp [Gate.inverseWord])
    (symplectic_D_CZ_nonzero g a b ha (0 : Fin 2) 1 (by decide))

/-- Restricted replay of `symplecticDerives_AB_CZ_zero_zero` on the canonical pair. -/
theorem adjacentSymplecticDerives_AB_CZ_zero_zero (A : ABox (ZMod d)) (ha : A.a = 0)
    (k : ZMod d) :
    AdjacentSymplecticDerives g (bWord 0 k (0 : Fin 2) (1 : Fin 2) (by decide) ++ A.toWord (1 : Fin 2) ++ [.CZ (0 : Fin 2) (1 : Fin 2) (by decide)])
      (Sexp (1 : Fin 2) (-2*k*A.b⁻¹) ++ List.replicate A.b⁻¹.val (.CZ (0 : Fin 2) (1 : Fin 2) (by decide)) ++
        bWord 0 k (0 : Fin 2) (1 : Fin 2) (by decide) ++ A.toWord (1 : Fin 2)) :=
  adjacentSymplecticDerives_of_twoWire g (by simp [Gate.inverseWord]) (by simp [Gate.inverseWord])
    (symplecticDerives_AB_CZ_zero_zero g A ha k (0 : Fin 2) 1 (by decide))

/-- Restricted replay of `symplecticDerives_AB_CZ_zero_distinct` on the canonical pair. -/
theorem adjacentSymplecticDerives_AB_CZ_zero_distinct (A : ABox (ZMod d)) (ha : A.a=0)
    (c k : ZMod d) (hc : c ≠ 0) (hbc : A.b-c ≠ 0) :
    AdjacentSymplecticDerives g (bWord c k (0 : Fin 2) (1 : Fin 2) (by decide) ++ A.toWord (1 : Fin 2) ++ [.CZ (0 : Fin 2) (1 : Fin 2) (by decide)])
      (Circuit.multiplier (1 : Fin 2) ((Units.mk0 (A.b-c) hbc / Units.mk0 A.b (A.b_ne_zero ha))⁻¹) ++
        [.H (1 : Fin 2)] ++ List.replicate A.b⁻¹.val (.CZ (0 : Fin 2) (1 : Fin 2) (by decide)) ++ inverseWord d [.H (1 : Fin 2)] ++
        bWord c k (0 : Fin 2) (1 : Fin 2) (by decide) ++ (A.zeroDifferenceStep c hbc).toWord (1 : Fin 2)) :=
  adjacentSymplecticDerives_of_twoWire g (by simp [Gate.inverseWord]) (by simp [Gate.inverseWord])
    (symplecticDerives_AB_CZ_zero_distinct g A ha c k hc hbc (0 : Fin 2) 1 (by decide))

/-- Restricted replay of `symplecticDerives_AB_CZ_collision` on the canonical pair. -/
theorem adjacentSymplecticDerives_AB_CZ_collision (A : ABox (ZMod d)) (ha : A.a=0)
    (k : ZMod d) :
    AdjacentSymplecticDerives g (bWord A.b k (0 : Fin 2) (1 : Fin 2) (by decide) ++ A.toWord (1 : Fin 2) ++ [.CZ (0 : Fin 2) (1 : Fin 2) (by decide)])
      (inverseWord d ([.H (1 : Fin 2)] ++ List.replicate A.b⁻¹.val (.CZ (0 : Fin 2) (1 : Fin 2) (by decide)) ++
        List.replicate 3 (.H (1 : Fin 2))) ++ [.H (1 : Fin 2), .H (1 : Fin 2)] ++ (A.collisionStep ha k).toWord (0 : Fin 2)) :=
  adjacentSymplecticDerives_of_twoWire g (by simp [Gate.inverseWord]) (by simp [Gate.inverseWord])
    (symplecticDerives_AB_CZ_collision g A ha k (0 : Fin 2) 1 (by decide))

/-- Restricted replay of `symplecticDerives_AB_CZ_zero_nonzero` on the canonical pair. -/
theorem adjacentSymplecticDerives_AB_CZ_zero_nonzero (A : ABox (ZMod d)) (ha : A.a ≠ 0)
    (k : ZMod d) :
    AdjacentSymplecticDerives g (bWord 0 k (0 : Fin 2) (1 : Fin 2) (by decide) ++ A.toWord (1 : Fin 2) ++ [.CZ (0 : Fin 2) (1 : Fin 2) (by decide)])
      (bWord 0 (k-A.a) (0 : Fin 2) (1 : Fin 2) (by decide) ++ A.toWord (1 : Fin 2)) :=
  adjacentSymplecticDerives_of_twoWire g (by simp [Gate.inverseWord]) (by simp [Gate.inverseWord])
    (symplecticDerives_AB_CZ_zero_nonzero g A ha k (0 : Fin 2) 1 (by decide))

/-- Restricted replay of `symplecticDerives_AB_CZ_nonzero` on the canonical pair. -/
theorem adjacentSymplecticDerives_AB_CZ_nonzero (A : ABox (ZMod d)) (ha : A.a ≠ 0)
    (c k : ZMod d) (hc : c ≠ 0) :
    AdjacentSymplecticDerives g (bWord c k (0 : Fin 2) (1 : Fin 2) (by decide) ++ A.toWord (1 : Fin 2) ++ [.CZ (0 : Fin 2) (1 : Fin 2) (by decide)])
      (inverseWord d [.H (1 : Fin 2)] ++ Sexp (1 : Fin 2) (-A.a/c) ++ [.H (1 : Fin 2)] ++
        bWord c (k-A.a) (0 : Fin 2) (1 : Fin 2) (by decide) ++ (A.nonzeroDifferenceStep ha c).toWord (1 : Fin 2)) :=
  adjacentSymplecticDerives_of_twoWire g (by simp [Gate.inverseWord]) (by simp [Gate.inverseWord])
    (symplecticDerives_AB_CZ_nonzero g A ha c k hc (0 : Fin 2) 1 (by decide))

/-- The separate zero-k AB/CZ printed row, with its trivial phase removed. -/
theorem adjacentSymplecticDerives_AB_CZ_zero_zero_zero
    (A : ABox (ZMod d)) (ha : A.a = 0) :
    AdjacentSymplecticDerives g
      (bWord (0 : ZMod d) 0 (0 : Fin 2) 1 (by decide) ++ A.toWord 1 ++ [.CZ 0 1 (by decide)])
      (List.replicate A.b⁻¹.val (.CZ 0 1 (by decide)) ++
        bWord (0 : ZMod d) 0 (0 : Fin 2) 1 (by decide) ++ A.toWord 1) := by
  simpa only [mul_zero, zero_mul, Sexp, ZMod.val_zero, List.replicate_zero,
    List.nil_append] using adjacentSymplecticDerives_AB_CZ_zero_zero g A ha 0

end QuditClifford.NormalBoxes
