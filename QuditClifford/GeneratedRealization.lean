import QuditClifford.GeneratedQuotients
import QuditClifford.NormalCircuit

/-! # Surjectivity for actual Clifford matrix groups

The concrete normal-form compiler realizes every symplectic transformation by
an actual primitive circuit. Pauli corrections then realize every scalar-fixing
Pauli automorphism. All quotient maps below are between genuine matrix groups;
no rewriting-completeness hypothesis is used.
-/
noncomputable section
namespace QuditClifford.Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]

/-- Every symplectic map is realized by an actual generated Clifford matrix. -/
theorem generatedSymplecticHom_surjective (hd : Odd d) :
    Function.Surjective (generatedSymplecticHom (d := d) (n := n) hd) := by
  intro F
  obtain ⟨w, hw⟩ := NormalBoxes.exists_word_symplecticAction F
  refine ⟨generatedWord w, ?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  rw [generatedSymplecticHom_word]
  exact hw v

/-- Primitive Clifford circuits realize every scalar-fixing Pauli automorphism. -/
theorem generatedPauliAutHom_surjective (hd : Odd d) :
    Function.Surjective (generatedPauliAutHom (d := d) (n := n) hd) :=
  generatedPauliAutHom_surjective_of_symplectic hd (generatedSymplecticHom_surjective hd)

/-- Surjectivity also holds for the full unitary Pauli normalizer. -/
theorem normalizerConjugationHom_surjective (hd : Odd d) :
    Function.Surjective (normalizerConjugationHom (d := d) (n := n)) := by
  intro φ
  obtain ⟨U, hU⟩ := generatedPauliAutHom_surjective (n := n) hd φ
  exact ⟨generatedToNormalizer hd U, hU⟩

theorem cliffordSymplecticHom_surjective (hd : Odd d) :
    Function.Surjective (cliffordSymplecticHom (d := d) (n := n)) := by
  intro F
  obtain ⟨U, hU⟩ := generatedSymplecticHom_surjective (n := n) hd F
  exact ⟨generatedToNormalizer hd U, hU⟩

/-- Generated Cliffords modulo their actual scalar kernel are exactly the
scalar-fixing Pauli automorphisms (the projective Clifford description). -/
def generatedQuotientScalarsEquiv (hd : Odd d) :
    generatedCliffordGroup d n ⧸ (generatedPauliAutHom hd).ker ≃* Pauli.scalarFixingAut d n :=
  QuotientGroup.quotientKerEquivOfSurjective _ (generatedPauliAutHom_surjective hd)

/-- The quotient by the symplectic kernel is the symplectic group. The separate
scalar-kernel theorem identifies this kernel with the enlarged signed Paulis. -/
def generatedQuotientKernelEquivSymplectic (hd : Odd d) :
    generatedCliffordGroup d n ⧸ (generatedSymplecticHom hd).ker ≃* symplecticGroup d n :=
  QuotientGroup.quotientKerEquivOfSurjective _ (generatedSymplecticHom_surjective hd)

/-- The corresponding quotient theorem for the full unitary matrix normalizer. -/
def normalizerQuotientKernelEquivSymplectic (hd : Odd d) :
    cliffordMatrixGroup d n ⧸ (cliffordSymplecticHom (d := d) (n := n)).ker ≃* symplecticGroup d n :=
  QuotientGroup.quotientKerEquivOfSurjective _ (cliffordSymplecticHom_surjective hd)

end QuditClifford.Circuit
