import QuditClifford.GeneratedClifford

/-! # Kernels and lifting for the actual generated Clifford group

These statements concern generated complex matrices. They identify the exact
scalar kernel of the full Pauli action and lift symplectic surjectivity using
actual Pauli circuit corrections. Rewriting completeness is not assumed.
-/
noncomputable section
namespace QuditClifford.Circuit
open Matrix
variable {d n : ℕ} [NeZero d]

@[simp] theorem actionHom_generatedPauliAutHom (hd : Odd d) (U : generatedCliffordGroup d n) :
    Pauli.actionHom (generatedPauliAutHom hd U) = generatedSymplecticHom hd U := rfl

/-- The kernel of the complete Pauli action consists exactly of scalar matrices. -/
theorem mem_generatedPauliAutHom_ker_iff_scalar (hd : Odd d) (U : generatedCliffordGroup d n) :
    U ∈ (generatedPauliAutHom hd).ker ↔ ∃ c : ℂ, U.val.val = c • (1 : QuditOperator d n) := by
  change generatedPauliAutHom hd U = 1 ↔ _
  constructor
  · intro h
    apply (pauli_centralizer U.val.val).mp
    intro p
    have hp := generatedPauliAutHom_matrix hd U p
    rw [h] at hp
    change Pauli.repr p = U.val.val * Pauli.repr p * U.val.valᴴ at hp
    calc
      _ = (U.val.val * Pauli.repr p * U.val.valᴴ) * U.val.val := by
        rw [mul_assoc, mul_assoc, show U.val.valᴴ * U.val.val = 1 from U.val.property.1, mul_one]
      _ = _ := congrArg (fun A => A * U.val.val) hp.symm
  · rintro ⟨c, hc⟩
    apply Subtype.ext
    apply MulEquiv.ext
    intro p
    apply Pauli.repr_injective
    change Pauli.repr ((generatedPauliAutHom hd U).val p) = Pauli.repr p
    rw [generatedPauliAutHom_matrix]
    have hcomm : U.val.val * Pauli.repr p = Pauli.repr p * U.val.val := by
      rw [hc]
      simp
    rw [hcomm, mul_assoc, show U.val.val * U.val.valᴴ = 1 from U.val.property.2, mul_one]

/-- Pauli circuit corrections lift a surjective symplectic action to a
surjective full Pauli-automorphism action. The hypothesis is instantiated by
the concrete normal-form compiler, not taken as a Clifford axiom. -/
theorem generatedPauliAutHom_surjective_of_symplectic (hd : Odd d)
    (hs : Function.Surjective (generatedSymplecticHom (d := d) (n := n) hd)) :
    Function.Surjective (generatedPauliAutHom (d := d) (n := n) hd) := by
  intro φ
  obtain ⟨U, hU⟩ := hs (Pauli.actionHom φ)
  let ψ := φ * (generatedPauliAutHom hd U)⁻¹
  have hψ : ψ ∈ (Pauli.actionHom : Pauli.scalarFixingAut d n →* symplecticGroup d n).ker := by
    change Pauli.actionHom ψ = 1
    simp [ψ, hU]
  obtain ⟨v, hv⟩ := (Pauli.mem_actionHom_ker_iff ψ).mp hψ
  refine ⟨pauliToGenerated hd (Pauli.representative v.toAdd) * U, ?_⟩
  rw [map_mul, generatedPauliAutHom_pauli]
  change Pauli.innerHom v * generatedPauliAutHom hd U = φ
  rw [hv]
  simp [ψ, mul_assoc]

end QuditClifford.Circuit
