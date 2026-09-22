import QuditClifford.AdjacentThreeWireReplay
import QuditClifford.SymplecticThreeWireBB

/-!
# The ten three-wire Appendix F branches in the adjacent presentation

These are the two lower-CZ/B, four DD/CZ and four BB/CZ branches on the
canonical wires 0,1,2. The broad proofs are transported rule by rule by the
proved routing compiler. In the BB templates the output CZ is first given
its canonical orientation before replaying the complete derivation.

Together with AdjacentBoxCases these cover all 42 printed case branches.
This local coverage is separate from recursive circuit normalization.
-/

noncomputable section
namespace QuditClifford.NormalBoxes
open Circuit
variable {d : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

omit [NeZero d] [Fact (Odd d)] in
private theorem b01_adj (a b : ZMod d) :
    IsAdjacentWord (bWord a b (0 : Fin 3) 1 (by decide)) := bWord_isAdjacent a b 0
omit [NeZero d] [Fact (Odd d)] in
private theorem b12_adj (a b : ZMod d) :
    IsAdjacentWord (bWord a b (1 : Fin 3) 2 (by decide)) := bWord_isAdjacent a b 1
omit [NeZero d] [Fact (Odd d)] in
private theorem d01_adj (a b : ZMod d) :
    IsAdjacentWord (dWord a b (0 : Fin 3) 1 (by decide)) := dWord_isAdjacent a b 0
omit [NeZero d] [Fact (Odd d)] in
private theorem d12_adj (a b : ZMod d) :
    IsAdjacentWord (dWord a b (1 : Fin 3) 2 (by decide)) := dWord_isAdjacent a b 1

attribute [local simp] b01_adj b12_adj d01_adj d12_adj
  AdjacentThreeWire.cz01_adj AdjacentThreeWire.cz12_adj AdjacentThreeWire.remote_adj
  IsAdjacentWord.replicate IsAdjacentWord.inverseWord

/-- The lower-CZ/B branch at zero first label, with its routed remote phase. -/
theorem adjacentDerives_B_CZ_lower_zero (b : ZMod d) :
    AdjacentDerives g (bWord 0 b (0 : Fin 3) 1 (by decide) ++ [.CZ 1 2 (by decide)])
      (Circuit.CIZ (d := d) 0 1 2 (by decide) (by decide) (by decide) ++
        List.replicate (-b).val (.CZ 1 2 (by decide)) ++ bWord 0 b (0 : Fin 3) 1 (by decide)) :=
  adjacentDerives_of_threeWire g (by simp [Gate.inverseWord]) (by simp [Gate.inverseWord])
    (derives_B_CZ_lower_zero g b (0 : Fin 3) 1 2 (by decide) (by decide) (by decide))

/-- The lower-CZ/B branch at nonzero first label remains an exact source derivation. -/
theorem adjacentDerives_B_CZ_lower_nonzero (a b : ZMod d) (ha : a ≠ 0) :
    AdjacentDerives g (bWord a b (0 : Fin 3) 1 (by decide) ++ [.CZ 1 2 (by decide)])
      (Circuit.CIZ (d := d) 0 1 2 (by decide) (by decide) (by decide) ++
        List.replicate (-a).val (.CZ 1 2 (by decide)) ++ bWord a b (0 : Fin 3) 1 (by decide)) :=
  adjacentDerives_of_threeWire g (by simp [Gate.inverseWord]) (by simp [Gate.inverseWord])
    (derives_B_CZ_lower_nonzero g a b ha (0 : Fin 3) 1 2 (by decide) (by decide) (by decide))

/-- The exact zero/zero DD/CZ branch on canonical neighboring pairs. -/
theorem adjacentDerives_DD_CZ_zero_zero (b e : ZMod d) :
    AdjacentDerives g
      (dWord 0 b (1 : Fin 3) 2 (by decide) ++ dWord 0 e 0 1 (by decide) ++ [.CZ 1 2 (by decide)])
      ([.CZ 0 1 (by decide)] ++ dWord 0 b (1 : Fin 3) 2 (by decide) ++ dWord 0 e 0 1 (by decide)) :=
  adjacentDerives_of_threeWire g (by simp [Gate.inverseWord]) (by simp [Gate.inverseWord])
    (derives_DD_CZ_zero_zero g b e (0 : Fin 3) 1 2 (by decide) (by decide) (by decide))

/-- The exact zero/nonzero DD/CZ branch and its first-wire Fourier correction. -/
theorem adjacentDerives_DD_CZ_zero_nonzero (b c e : ZMod d) (hc : c ≠ 0) :
    AdjacentDerives g
      (dWord 0 b (1 : Fin 3) 2 (by decide) ++ dWord c e 0 1 (by decide) ++ [.CZ 1 2 (by decide)])
      ([.H 0, .CZ 0 1 (by decide)] ++ inverseWord d [.H 0] ++
        dWord 0 (b-c) (1 : Fin 3) 2 (by decide) ++ dWord c e 0 1 (by decide)) :=
  adjacentDerives_of_threeWire g (by simp [Gate.inverseWord]) (by simp [Gate.inverseWord])
    (derives_DD_CZ_zero_nonzero g b c e hc (0 : Fin 3) 1 2 (by decide) (by decide) (by decide))

/-- The exact nonzero/zero DD/CZ branch and its middle-wire Fourier correction. -/
theorem adjacentDerives_DD_CZ_nonzero_zero (a b e : ZMod d) (ha : a ≠ 0) :
    AdjacentDerives g
      (dWord a b (1 : Fin 3) 2 (by decide) ++ dWord 0 e 0 1 (by decide) ++ [.CZ 1 2 (by decide)])
      ([.H 1, .CZ 0 1 (by decide)] ++ inverseWord d [.H 1] ++
        dWord a b (1 : Fin 3) 2 (by decide) ++ dWord 0 (e-a) 0 1 (by decide)) :=
  adjacentDerives_of_threeWire g (by simp [Gate.inverseWord]) (by simp [Gate.inverseWord])
    (derives_DD_CZ_nonzero_zero g a b e ha (0 : Fin 3) 1 2 (by decide) (by decide) (by decide))

/-- The nonzero/nonzero DD/CZ branch in the explicitly Pauli-erased source presentation. -/
theorem adjacentSymplectic_DD_CZ_nonzero_nonzero (a b c e : ZMod d) (ha : a ≠ 0) (hc : c ≠ 0) :
    AdjacentSymplecticDerives g
      (dWord a b (1 : Fin 3) 2 (by decide) ++ dWord c e 0 1 (by decide) ++ [.CZ 1 2 (by decide)])
      ([.H 1, .H 0, .CZ 0 1 (by decide)] ++ Sexp 1 (-c/a) ++ inverseWord d [.H 1] ++
        Sexp 0 (-a/c) ++ inverseWord d [.H 0] ++
          dWord a (b-c) (1 : Fin 3) 2 (by decide) ++ dWord c (e-a) 0 1 (by decide)) :=
  adjacentSymplecticDerives_of_threeWire g (by simp [Gate.inverseWord]) (by simp [Gate.inverseWord])
    (symplectic_DD_CZ_nonzero_nonzero g a b c e ha hc (0 : Fin 3) 1 2
      (by decide) (by decide) (by decide))

set_option linter.unusedSectionVars false in
private theorem orientCZ12 (l r : Word 3) :
    Derives g (l ++ [.CZ 2 1 (by decide)] ++ r) (l ++ [.CZ 1 2 (by decide)] ++ r) :=
  (Presentation.Derives.rule (R := Rules g)
    (Or.inl (Structural.CZ_symmetry (2 : Fin 3) 1 (by decide)))).context l r

/-- The exact zero/zero BB/CZ branch, with canonical output CZ orientation. -/
theorem adjacentDerives_BB_CZ_zero_zero (b e : ZMod d) :
    AdjacentDerives g
      (bWord 0 b (0 : Fin 3) 1 (by decide) ++ bWord 0 e 1 2 (by decide) ++ [.CZ 0 1 (by decide)])
      ([.CZ 1 2 (by decide)] ++ bWord 0 b (0 : Fin 3) 1 (by decide) ++ bWord 0 e 1 2 (by decide)) := by
  apply adjacentDerives_of_threeWire g (by simp [Gate.inverseWord]) (by simp [Gate.inverseWord])
  apply (derives_BB_CZ_zero_zero g b e (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)).trans
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using
    orientCZ12 g [] (bWord 0 b (0 : Fin 3) 1 (by decide) ++ bWord 0 e 1 2 (by decide))

/-- The exact zero/nonzero BB/CZ branch, retaining the final-wire Fourier correction. -/
theorem adjacentDerives_BB_CZ_zero_nonzero (b c e : ZMod d) (hc : c ≠ 0) :
    AdjacentDerives g
      (bWord 0 b (0 : Fin 3) 1 (by decide) ++ bWord c e 1 2 (by decide) ++ [.CZ 0 1 (by decide)])
      ([.H 2, .CZ 1 2 (by decide)] ++ inverseWord d [.H 2] ++
        bWord 0 (b-c) (0 : Fin 3) 1 (by decide) ++ bWord c e 1 2 (by decide)) := by
  apply adjacentDerives_of_threeWire g (by simp [Gate.inverseWord]) (by simp [Gate.inverseWord])
  apply (derives_BB_CZ_zero_nonzero g b c e hc (0 : Fin 3) 1 2
    (by decide) (by decide) (by decide)).trans
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using
    orientCZ12 g [.H 2] (inverseWord d [.H 2] ++
      bWord 0 (b-c) (0 : Fin 3) 1 (by decide) ++ bWord c e 1 2 (by decide))

/-- The exact nonzero/zero BB/CZ branch, retaining the middle-wire Fourier correction. -/
theorem adjacentDerives_BB_CZ_nonzero_zero (a b e : ZMod d) (ha : a ≠ 0) :
    AdjacentDerives g
      (bWord a b (0 : Fin 3) 1 (by decide) ++ bWord 0 e 1 2 (by decide) ++ [.CZ 0 1 (by decide)])
      ([.H 1, .CZ 1 2 (by decide)] ++ inverseWord d [.H 1] ++
        bWord a b (0 : Fin 3) 1 (by decide) ++ bWord 0 (e-a) 1 2 (by decide)) := by
  apply adjacentDerives_of_threeWire g (by simp [Gate.inverseWord]) (by simp [Gate.inverseWord])
  apply (derives_BB_CZ_nonzero_zero g a b e ha (0 : Fin 3) 1 2
    (by decide) (by decide) (by decide)).trans
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using
    orientCZ12 g [.H 1] (inverseWord d [.H 1] ++
      bWord a b (0 : Fin 3) 1 (by decide) ++ bWord 0 (e-a) 1 2 (by decide))

/-- The nonzero/nonzero BB/CZ branch, with canonical CZ and explicit Pauli erasure. -/
theorem adjacentSymplecticDerives_BB_CZ_nonzero_nonzero
    (a b c e : ZMod d) (ha : a ≠ 0) (hc : c ≠ 0) :
    AdjacentSymplecticDerives g
      (bWord a b (0 : Fin 3) 1 (by decide) ++ bWord c e 1 2 (by decide) ++ [.CZ 0 1 (by decide)])
      ([.H 1, .H 2, .CZ 1 2 (by decide)] ++ Sexp 1 (-c/a) ++ inverseWord d [.H 1] ++
        Sexp 2 (-a/c) ++ inverseWord d [.H 2] ++
          bWord a (b-c) (0 : Fin 3) 1 (by decide) ++ bWord c (e-a) 1 2 (by decide)) := by
  apply adjacentSymplecticDerives_of_threeWire g (by simp [Gate.inverseWord]) (by simp [Gate.inverseWord])
  apply (symplecticDerives_BB_CZ_nonzero_nonzero g a b c e ha hc (0 : Fin 3) 1 2
    (by decide) (by decide) (by decide)).trans
  apply derives_symplectic g
  convert orientCZ12 g [.H 1, .H 2] (Sexp 1 (-c/a) ++ inverseWord d [.H 1] ++
      Sexp 2 (-a/c) ++ inverseWord d [.H 2] ++
        bWord a (b-c) (0 : Fin 3) 1 (by decide) ++ bWord c (e-a) 1 2 (by decide)) using 1

end QuditClifford.NormalBoxes
