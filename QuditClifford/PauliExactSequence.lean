import QuditClifford.SymplecticLift
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The exact sequence for scalar-fixing Pauli automorphisms

This packages the concrete action and kernel proofs as group homomorphisms.
In odd dimension the sequence splits through symmetric Weyl coordinates.
The groups here are automorphisms of the faithful finite Pauli group; proving
that the paper's circuit generators realize every such automorphism is a
separate matrix-generation and rewriting obligation.
-/

namespace QuditClifford.Pauli

variable {d n : ℕ}

/-- Automorphisms fixing every scalar pointwise. -/
def scalarFixingAut (d n : ℕ) : Subgroup (MulAut (Pauli d n)) where
  carrier := {φ | FixesScalars φ}
  one_mem' := by intro c; rfl
  mul_mem' := by
    intro φ ψ hφ hψ c
    change φ (ψ (scalar c)) = scalar c
    rw [hψ, hφ]
  inv_mem' := fun h => h.symm

/-- The induced symplectic action is a group homomorphism. -/
def actionHom : scalarFixingAut d n →* symplecticGroup d n where
  toFun φ := symplecticAction φ.val φ.property
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    rfl
  map_mul' φ ψ := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change (φ.val (ψ.val (representative v))).coords =
      action φ.val (ψ.val (representative v)).coords
    exact (action_coords φ.val φ.property _).symm

@[simp] theorem actionHom_apply (φ : scalarFixingAut d n) (v : PhaseSpace d n) :
    (actionHom φ).val v = action φ.val v := rfl

/-- The symmetric Weyl lift respects composition. -/
theorem liftApply_comp (F G : PhaseSpace d n ≃ₗ[ZMod d] PhaseSpace d n)
    (p : Pauli d n) : liftApply (F*G) p = liftApply F (liftApply G p) := by
  apply Pauli.ext
  · simp only [liftApply, LinearEquiv.mul_apply, coords]
    ring
  · rfl
  · rfl

/-- A splitting of the exponent action, available for odd dimension. -/
def liftHom (hd : Odd d) : symplecticGroup d n →* scalarFixingAut d n where
  toFun F := ⟨liftSymplectic hd F, liftSymplectic_fixesScalars hd F⟩
  map_one' := by
    apply Subtype.ext
    apply MulEquiv.ext
    intro p
    apply Pauli.ext <;> simp [liftSymplectic, liftApply, coords]
  map_mul' F G := by
    apply Subtype.ext
    apply MulEquiv.ext
    intro p
    exact liftApply_comp F.val G.val p

@[simp] theorem actionHom_liftHom (hd : Odd d) (F : symplecticGroup d n) :
    actionHom (liftHom hd F) = F := by
  apply Subtype.ext
  apply LinearEquiv.ext
  exact action_liftSymplectic hd F

theorem actionHom_surjective (hd : Odd d) :
    Function.Surjective (actionHom : scalarFixingAut d n →* symplecticGroup d n) :=
  fun F => ⟨liftHom hd F, actionHom_liftHom hd F⟩

/-- Pauli conjugations fix scalars pointwise. -/
theorem conj_fixesScalars (p : Pauli d n) : FixesScalars (MulAut.conj p) := by
  intro c
  simp [MulAut.conj_apply, conjugation_formula, coords, symplectic]

/-- The injection of exponent vectors as inner automorphisms. -/
def innerHom : Multiplicative (PhaseSpace d n) →* scalarFixingAut d n where
  toFun v := ⟨MulAut.conj (representative v.toAdd), conj_fixesScalars _⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' v w := by
    apply Subtype.ext
    change MulAut.conj (representative (v.toAdd+w.toAdd)) =
      MulAut.conj (representative v.toAdd) * MulAut.conj (representative w.toAdd)
    rw [← map_mul]
    apply (inner_eq_iff_coords_eq _ _).mpr
    simp

theorem innerHom_injective :
    Function.Injective (innerHom : Multiplicative (PhaseSpace d n) →* scalarFixingAut d n) := by
  intro v w h
  have he := (inner_eq_iff_coords_eq (representative v.toAdd)
    (representative w.toAdd)).mp (congrArg Subtype.val h)
  exact he

/-- Exactness: a trivial symplectic action is precisely a Pauli conjugation. -/
theorem mem_actionHom_ker_iff (φ : scalarFixingAut d n) :
    φ ∈ (actionHom : scalarFixingAut d n →* symplecticGroup d n).ker ↔
      ∃ v, innerHom v = φ := by
  have htriv : actionHom φ = 1 ↔ ∀ p, (φ.val p).coords = p.coords := by
    constructor
    · intro h p
      have hv := congrArg (fun F : symplecticGroup d n => F.val p.coords) h
      simpa only [actionHom_apply, action_coords φ.val φ.property] using hv
    · intro h
      apply Subtype.ext
      apply LinearEquiv.ext
      intro v
      exact h (representative v)
  change actionHom φ = 1 ↔ _
  rw [htriv, trivial_action_iff_inner φ.val φ.property]
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨Multiplicative.ofAdd p.coords, ?_⟩
    apply Subtype.ext
    change MulAut.conj (representative p.coords) = φ.val
    rw [hp]
    exact (inner_eq_iff_coords_eq _ _).mpr rfl
  · rintro ⟨v, hv⟩
    exact ⟨representative v.toAdd, (congrArg Subtype.val hv).symm⟩

theorem actionHom_ker_eq_innerHom_range :
    (actionHom : scalarFixingAut d n →* symplecticGroup d n).ker = innerHom.range := by
  ext φ
  exact mem_actionHom_ker_iff φ

@[simp] theorem actionHom_innerHom (v : Multiplicative (PhaseSpace d n)) :
    actionHom (innerHom v) = 1 := by
  change innerHom v ∈ (actionHom : scalarFixingAut d n →* symplecticGroup d n).ker
  exact (mem_actionHom_ker_iff _).mpr ⟨v, rfl⟩

/-- Each scalar-fixing automorphism has a unique Pauli correction followed by
its symmetric Weyl lift. Uniqueness concerns exponents, not scalar Paulis. -/
theorem existsUnique_inner_lift (hd : Odd d) (φ : scalarFixingAut d n) :
    ∃! v : Multiplicative (PhaseSpace d n),
      innerHom v * liftHom hd (actionHom φ) = φ := by
  let ψ := φ * (liftHom hd (actionHom φ))⁻¹
  have hψ : ψ ∈ (actionHom : scalarFixingAut d n →* symplecticGroup d n).ker := by
    change actionHom ψ = 1
    simp [ψ]
  obtain ⟨v, hv⟩ := (mem_actionHom_ker_iff ψ).mp hψ
  have hfact : innerHom v * liftHom hd (actionHom φ) = φ := by
    rw [hv]
    simp [ψ, mul_assoc]
  refine ⟨v, hfact, ?_⟩
  intro w hw
  exact innerHom_injective (mul_right_cancel (hw.trans hfact.symm))

/-- Unique exponent-and-symplectic coordinates for the abstract automorphism
group. This is a set equivalence; the product group law is semidirect. -/
noncomputable def autEquivCoordinates (hd : Odd d) :
    scalarFixingAut d n ≃ (Multiplicative (PhaseSpace d n) × symplecticGroup d n) :=
  (Equiv.ofBijective
    (fun (x : Multiplicative (PhaseSpace d n) × symplecticGroup d n) =>
      innerHom x.1 * liftHom hd x.2)
    (by
      constructor
      · rintro ⟨v, F⟩ ⟨w, G⟩ h
        have hFG : F = G := by
          have hh := congrArg actionHom h
          simpa using hh
        cases hFG
        have hvw := innerHom_injective (mul_right_cancel h)
        cases hvw
        rfl
      · intro φ
        obtain ⟨v, hv, _⟩ := existsUnique_inner_lift hd φ
        exact ⟨(v, actionHom φ), hv⟩)).symm

/-- The quotient theorem for the abstract scalar-fixing automorphism group.
It makes no assertion that the circuit rewriting system is complete. -/
noncomputable def quotientEquivSymplectic (hd : Odd d) :
    scalarFixingAut d n ⧸ (actionHom : scalarFixingAut d n →* symplecticGroup d n).ker
      ≃* symplecticGroup d n :=
  QuotientGroup.quotientKerEquivOfSurjective actionHom (actionHom_surjective hd)

end QuditClifford.Pauli
