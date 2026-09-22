import QuditClifford.NormalInduction

/-! # The normal-form symplectic maps are the existing symplectic group

Conjugating by `wiresCoordinates` changes only coordinate layout. These maps
preserve the actual alternating form already used by the Pauli action.
-/
noncomputable section
namespace QuditClifford.NormalBoxes
variable {d n : ℕ} [Fact d.Prime]

/-- Convert a wirewise symplectic equivalence to the existing phase-space group. -/
def toPhaseSymplectic (F : WireSymplectic (K := ZMod d) n) : symplecticGroup d n :=
  ⟨(wiresCoordinates d n).symm.trans (F.toLinearEquiv.trans (wiresCoordinates d n)), by
    intro v w
    change symplectic (wiresCoordinates d n (F ((wiresCoordinates d n).symm v)))
      (wiresCoordinates d n (F ((wiresCoordinates d n).symm w))) = symplectic v w
    rw [wiresCoordinates_symplectic, F.preserves]
    exact (wiresCoordinates_symplectic ((wiresCoordinates d n).symm v)
      ((wiresCoordinates d n).symm w)).symm⟩

/-- Convert the established phase-space group to wirewise coordinates. -/
def fromPhaseSymplectic (F : symplecticGroup d n) : WireSymplectic (K := ZMod d) n where
  toLinearEquiv := (wiresCoordinates d n).trans (F.val.trans (wiresCoordinates d n).symm)
  preserves v w := by
    change wiresBracket ((wiresCoordinates d n).symm (F.val (wiresCoordinates d n v)))
      ((wiresCoordinates d n).symm (F.val (wiresCoordinates d n w))) = wiresBracket v w
    rw [← wiresCoordinates_symplectic]
    simp only [LinearEquiv.apply_symm_apply]
    rw [F.property]
    exact wiresCoordinates_symplectic v w

/-- No new symplectic group is substituted for the Pauli exponent group: the
wirewise normal-form model is equivalent by the explicit coordinate change. -/
def wireSymplecticEquiv : WireSymplectic (K := ZMod d) n ≃ symplecticGroup d n where
  toFun := toPhaseSymplectic
  invFun := fromPhaseSymplectic
  left_inv F := by
    apply WireSymplectic.ext
    intro v
    change (wiresCoordinates d n).symm
      (wiresCoordinates d n (F ((wiresCoordinates d n).symm (wiresCoordinates d n v)))) = F v
    simp
  right_inv F := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change wiresCoordinates d n
      ((wiresCoordinates d n).symm (F.val (wiresCoordinates d n ((wiresCoordinates d n).symm v)))) = F.val v
    simp

end QuditClifford.NormalBoxes
