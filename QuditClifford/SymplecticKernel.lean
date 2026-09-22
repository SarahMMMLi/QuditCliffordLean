import QuditClifford.PresentedPauliNormality
import QuditClifford.SymplecticRewrites

/-!
# The kernel of syntactic Pauli erasure

Deleting scalar, X, and Z words gives exactly the quotient by the concrete
Pauli subgroup of the Figure 1 presentation. This identifies the kernel using
rewrites and quotient groups, independently of semantic completeness.
-/

noncomputable section
namespace QuditClifford.Circuit

variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

/-- Every concrete Pauli generator is deleted by syntactic symplectic erasure. -/
theorem presentedPauliSubgroup_le_symplectic_ker :
    presentedPauliSubgroup (n := n) g ≤ (presentedToSymplectic g).ker := by
  apply (Subgroup.closure_le _).mpr
  intro p hp
  rcases hp with rfl | ⟨i, rfl | rfl⟩
  · change symplecticClassWord g [.scalar] = 1
    simpa only [scalar, List.replicate_one] using symplecticClassWord_scalar (n := n) g 1
  · change symplecticClassWord g (X (d := d) i) = 1
    exact symplecticClassWord_X g i
  · change symplecticClassWord g (Z (d := d) i) = 1
    exact symplecticClassWord_Z g i

private theorem symplecticDerives_pauliQuotient_eq {u v : Word n}
    (h : SymplecticDerives g u v) :
    QuotientGroup.mk' (presentedPauliSubgroup g) (classWord g u) =
      QuotientGroup.mk' (presentedPauliSubgroup g) (classWord g v) := by
  induction h with
  | refl w => rfl
  | @rule u v hr =>
      rcases hr with (hr | ⟨rfl, rfl⟩) | ⟨i, (rfl | rfl), rfl⟩
      · exact congrArg (QuotientGroup.mk' (presentedPauliSubgroup g))
          ((classWord_eq_iff_derives g u v).mpr (.rule hr))
      · simpa only [classWord_nil, map_one] using
          (QuotientGroup.eq_one_iff (classWord (n := n) g [.scalar])).mpr
            (scalar_mem_presentedPauliSubgroup g)
      · simpa only [classWord_nil, map_one] using
          (QuotientGroup.eq_one_iff (classWord g (X (d := d) i))).mpr
            (X_mem_presentedPauliSubgroup g i)
      · simpa only [classWord_nil, map_one] using
          (QuotientGroup.eq_one_iff (classWord g (Z (d := d) i))).mpr
            (Z_mem_presentedPauliSubgroup g i)
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | context l r h ih => simp only [classWord_append, map_mul, ih]

/-- The erased presentation maps back to the quotient by the actual Pauli words. -/
def symplecticToPauliQuotient :
    PresentedSymplectic g n →* PresentedCircuit g n ⧸ presentedPauliSubgroup g where
  toFun := Quotient.lift
    (fun w => QuotientGroup.mk' (presentedPauliSubgroup g) (classWord g w))
    (fun _ _ h => symplecticDerives_pauliQuotient_eq g h)
  map_one' := rfl
  map_mul' := by
    intro a b
    obtain ⟨u, rfl⟩ := symplecticClassWord_surjective g a
    obtain ⟨v, rfl⟩ := symplecticClassWord_surjective g b
    change QuotientGroup.mk' (presentedPauliSubgroup g) (classWord g u * classWord g v) =
      QuotientGroup.mk' (presentedPauliSubgroup g) (classWord g u) *
        QuotientGroup.mk' (presentedPauliSubgroup g) (classWord g v)
    exact (QuotientGroup.mk' (presentedPauliSubgroup g)).map_mul _ _

@[simp] theorem symplecticToPauliQuotient_classWord (w : Word n) :
    symplecticToPauliQuotient g (symplecticClassWord g w) =
      QuotientGroup.mk' (presentedPauliSubgroup g) (classWord g w) := rfl

@[simp] theorem symplecticToPauliQuotient_presentedToSymplectic (p : PresentedCircuit g n) :
    symplecticToPauliQuotient g (presentedToSymplectic g p) =
      QuotientGroup.mk' (presentedPauliSubgroup g) p := by
  obtain ⟨w, rfl⟩ := classWord_surjective g p
  rfl

/-- The exact kernel of deleting scalar, X, and Z is their concrete subgroup. -/
theorem presentedToSymplectic_ker_eq_presentedPauliSubgroup :
    (presentedToSymplectic (n := n) g).ker = presentedPauliSubgroup g := by
  apply le_antisymm
  · intro p hp
    apply (QuotientGroup.eq_one_iff p).mp
    have h := congrArg (symplecticToPauliQuotient g) (show presentedToSymplectic g p = 1 from hp)
    simpa only [symplecticToPauliQuotient_presentedToSymplectic, map_one] using h
  · exact presentedPauliSubgroup_le_symplectic_ker g

/-- An erased rewrite has precisely a Pauli correction in the original presentation. -/
theorem symplecticDerives_iff_pauli_correction (u v : Word n) :
    SymplecticDerives g u v ↔ ∃ p ∈ presentedPauliSubgroup g,
      classWord g u = p * classWord g v := by
  constructor
  · intro h
    have he := (symplecticClassWord_eq_iff_derives g u v).mpr h
    refine ⟨classWord g u * (classWord g v)⁻¹, ?_, by group⟩
    rw [← presentedToSymplectic_ker_eq_presentedPauliSubgroup]
    change presentedToSymplectic g (classWord g u * (classWord g v)⁻¹) = 1
    simp only [map_mul, map_inv, presentedToSymplectic_classWord, he, mul_inv_cancel]
  · rintro ⟨p, hp, he⟩
    apply (symplecticClassWord_eq_iff_derives g u v).mp
    have hp' : presentedToSymplectic g p = 1 :=
      presentedPauliSubgroup_le_symplectic_ker g hp
    have h := congrArg (presentedToSymplectic g) he
    simpa only [map_mul, hp', one_mul, presentedToSymplectic_classWord] using h

end QuditClifford.Circuit
