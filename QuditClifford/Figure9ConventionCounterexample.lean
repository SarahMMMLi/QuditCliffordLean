import QuditClifford.AdjacentSymplecticRewrites
import QuditClifford.CircuitRelabel

/-!
# Historical inverse-exponent typo in Figure 9 C9

In the earlier PDF, page 24, Figure 9 C9 read temporally
`M_g ; CZ = CZ^(g⁻¹) ; M_g`. The caption uses the same derived multipliers
as Figure 2. The introduction defines these by `M_a |x⟩ = |a*x⟩`.
Thus the printed equation, in this library's matrix-order words, is
`CZ * M_g = M_g * CZ^(g⁻¹)`.

The updated PDF of 22 September 2026 corrects the exponent to `g`, matching
Figure 1 C9 and its exact soundness calculation. `Figure9Syntax` and
`Figure9Completeness` formalize that corrected presentation. The following
`d=5`, `g=2` example is retained only as a regression check for the historical
typo; it does not refute any relation in the updated PDF.

Source locations: `figures/RewriteRules/RewriteRules2.tikz`, node 402;
`scripts/1-introduction.tex`, raw multiplier definition;
`scripts/appendix/sectiontwoproofs.tex`, equation `eq:CZ-Mg-soundness`.
-/
noncomputable section
namespace QuditClifford.Circuit.Figure9ConventionCounterexample
open NormalBoxes

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Two is a unit and a primitive multiplicative generator modulo five. -/
def generator : (ZMod 5)ˣ := Units.mk0 2 (by decide)

@[simp] theorem generator_val : (generator : ZMod 5) = 2 := rfl
@[simp] theorem two_inv : (2 : ZMod 5)⁻¹ = 3 :=
  inv_eq_of_mul_eq_one_left (by decide : (3 : ZMod 5)*2=1)
@[simp] theorem generator_inv_val : (↑generator⁻¹ : ZMod 5) = 3 := by
  rw [Units.val_inv_eq_inv_val, generator_val, two_inv]

theorem generator_order : orderOf generator = 5-1 := by
  apply (orderOf_eq_iff (by decide : 0 < 4)).mpr
  constructor
  · decide
  · intro m hm hpos
    interval_cases m <;> decide

/-- The left circuit shown in Figure 9 C9, translated into matrix order. -/
def printedLeft : Word 2 :=
  [.CZ 0 1 (by decide)] ++ multiplier 0 generator

/-- The right circuit with the printed inverse exponent retained literally. -/
def printedRight : Word 2 :=
  multiplier 0 generator ++ List.replicate (↑generator⁻¹ : ZMod 5).val (.CZ 0 1 (by decide))

/-- X on the first wire, with all other Pauli exponents zero. -/
def witness : Wires (ZMod 5) 2 := fun i => if i=0 then (0,1) else (0,0)

/-- The left side creates exponent two on the second-wire Z coordinate. -/
theorem printedLeft_witness : (wireAction 5 printedLeft witness 1).1 = 2 := by
  simp [printedLeft, wireAction_append, wireAction_cons, wireAction_nil,
    Gate.wireAction_CZ, wireAction_multiplier, witness]

/-- The right side creates exponent three on that same coordinate. -/
theorem printedRight_witness : (wireAction 5 printedRight witness 1).1 = 3 := by
  simp only [printedRight, wireAction_append, wireAction_multiplier,
    show (1 : Fin 2) ≠ 0 from by decide, if_false]
  rw [wireAction_replicate_CZ]
  simp [witness]

/-- Figure 9 C9 fails on an explicit exponent vector, before any scalar issue. -/
theorem printedC9_not_wireAction_eq :
    wireAction 5 printedLeft witness ≠ wireAction 5 printedRight witness := by
  intro h
  have he := congrArg (fun v : Wires (ZMod 5) 2 => (v 1).1) h
  dsimp only at he
  rw [printedLeft_witness, printedRight_witness] at he
  exact (by decide : (2 : ZMod 5) ≠ 3) he

/-- The printed relation is not symplectically sound for the raw multiplier. -/
theorem printedC9_not_symplectically_sound :
    ¬ ∀ p : PhaseSpace 5 2,
      symplecticAction 5 printedLeft p = symplecticAction 5 printedRight p := by
  intro h
  apply printedC9_not_wireAction_eq
  exact congrArg (wiresCoordinates 5 2).symm (h (wiresCoordinates 5 2 witness))

/-- In particular the printed C9 does not follow from the sound Figure 1
presentation even after explicit scalar and Pauli erasure. -/
theorem not_symplecticDerives_printedC9 :
    ¬ SymplecticDerives generator printedLeft printedRight := by
  intro h
  exact printedC9_not_symplectically_sound (symplecticDerives_sound (by decide) generator h)

/-- Restricting to the source's adjacent alphabet does not change the failure. -/
theorem not_adjacentSymplecticDerives_printedC9 :
    ¬ AdjacentSymplecticDerives generator printedLeft printedRight := by
  intro h
  exact not_symplecticDerives_printedC9 (h.toSymplecticDerives generator)

/-- Exact denotations also differ; no matrix completeness theorem is used. -/
theorem printedC9_denote_ne : denote 5 printedLeft ≠ denote 5 printedRight := by
  intro h
  have hu : generatedWord (d := 5) printedLeft = generatedWord printedRight :=
    Subtype.ext (Subtype.ext h)
  have hf := congrArg (generatedSymplecticHom (by decide : Odd 5)) hu
  apply printedC9_not_symplectically_sound
  intro p
  simpa only [generatedSymplecticHom_word] using
    congrArg (fun F : symplecticGroup 5 2 => F.val p) hf

end QuditClifford.Circuit.Figure9ConventionCounterexample
