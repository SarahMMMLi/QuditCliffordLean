import QuditClifford.GeneratedRealization
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.Group.Equiv.TypeTags

/-! # The projective Clifford semidirect product

The symmetric Weyl lift acts on inner Pauli automorphisms by the ordinary
linear symplectic action. This upgrades the previously established coordinate
bijection to a group isomorphism. The generated matrix group's scalar quotient
therefore has the semidirect product description in Definition 2.28.
-/
noncomputable section
namespace QuditClifford
namespace Pauli
variable {d n : ℕ}

/-- The usual symplectic action on the additive phase space, written
multiplicatively for the semidirect-product construction. -/
def symplecticExponentAction :
    symplecticGroup d n →* MulAut (Multiplicative (PhaseSpace d n)) where
  toFun F := AddEquiv.toMultiplicative F.val.toAddEquiv
  map_one' := by ext v; rfl
  map_mul' F G := by ext v; rfl

@[simp] theorem symplecticExponentAction_apply (F : symplecticGroup d n)
    (v : Multiplicative (PhaseSpace d n)) :
    symplecticExponentAction F v = Multiplicative.ofAdd (F.val v.toAdd) := rfl

/-- Conjugating a Pauli correction by a Weyl lift applies its symplectic map
to the correction's exponents. -/
theorem innerHom_symplecticExponentAction (hd : Odd d) (F : symplecticGroup d n)
    (v : Multiplicative (PhaseSpace d n)) :
    innerHom (symplecticExponentAction F v) =
      liftHom hd F * innerHom v * (liftHom hd F)⁻¹ := by
  apply Subtype.ext
  change MulAut.conj (representative (F.val v.toAdd)) =
    liftSymplectic hd F * MulAut.conj (representative v.toAdd) * (liftSymplectic hd F)⁻¹
  have he : MulAut.conj (representative (F.val v.toAdd)) =
      MulAut.conj (liftSymplectic hd F (representative v.toAdd)) := by
    apply (inner_eq_iff_coords_eq _ _).mpr
    rfl
  rw [he]
  apply MulEquiv.ext
  intro p
  simp [MulAut.conj_apply, MulAut.mul_apply, map_mul]

/-- Affine symplectic coordinates, with their actual semidirect group law. -/
abbrev AffineSymplectic (d n : ℕ) :=
  Multiplicative (PhaseSpace d n) ⋊[symplecticExponentAction] symplecticGroup d n

/-- A translation and a symplectic map act by inner conjugation followed by
the symmetric Weyl lift. -/
def affineToAut (hd : Odd d) : AffineSymplectic d n →* scalarFixingAut d n :=
  SemidirectProduct.lift innerHom (liftHom hd) (by
    intro F
    apply MonoidHom.ext
    intro v
    exact innerHom_symplecticExponentAction hd F v)

@[simp] theorem affineToAut_apply (hd : Odd d) (a : AffineSymplectic d n) :
    affineToAut hd a = innerHom a.left * liftHom hd a.right := rfl

theorem affineToAut_bijective (hd : Odd d) :
    Function.Bijective (affineToAut (d := d) (n := n) hd) := by
  constructor
  · intro a b hab
    have hF : a.right = b.right := by
      have h := congrArg actionHom hab
      simpa only [affineToAut_apply, map_mul, actionHom_innerHom,
        actionHom_liftHom, one_mul] using h
    have hv : a.left = b.left := by
      simp only [affineToAut_apply, hF] at hab
      exact innerHom_injective (mul_right_cancel hab)
    exact SemidirectProduct.ext hv hF
  · intro φ
    obtain ⟨v, hv, _⟩ := existsUnique_inner_lift hd φ
    exact ⟨⟨v, actionHom φ⟩, hv⟩

/-- Scalar-fixing Pauli automorphisms are the affine symplectic group. -/
def autEquivAffineSymplectic (hd : Odd d) : scalarFixingAut d n ≃* AffineSymplectic d n :=
  (MulEquiv.ofBijective (affineToAut hd) (affineToAut_bijective hd)).symm

end Pauli
namespace Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]

/-- Definition 2.28 for the actual generated matrix group modulo its scalar
kernel. The kernel is independently proved to consist of exact scalar matrices. -/
def generatedProjectiveEquivAffineSymplectic (hd : Odd d) :
    generatedCliffordGroup d n ⧸ (generatedPauliAutHom hd).ker ≃*
      Pauli.AffineSymplectic d n :=
  (generatedQuotientScalarsEquiv hd).trans (Pauli.autEquivAffineSymplectic hd)

end Circuit
end QuditClifford
