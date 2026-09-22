import QuditClifford.PauliAutomorphisms
import QuditClifford.Gates

/-!
# Lifting symplectic maps to exact Pauli automorphisms

Oddness permits symmetric Weyl coordinates. The construction below is an
actual center-fixing automorphism of the existing Pauli group, and its induced
symplectic action is the supplied map. This proves algebraic surjectivity; a
realization by generated Clifford matrix circuits is a separate obligation.
-/

namespace QuditClifford
namespace Pauli

variable {d n : ℕ}

/-- Change exponent coordinates by F while preserving the symmetric Weyl phase. -/
def liftApply (F : PhaseSpace d n ≃ₗ[ZMod d] PhaseSpace d n) (p : Pauli d n) : Pauli d n :=
  ⟨p.phase - half d * dot p.z p.x + half d * dot (F p.coords).1 (F p.coords).2,
    (F p.coords).2, (F p.coords).1⟩

@[simp] theorem coords_liftApply (F : PhaseSpace d n ≃ₗ[ZMod d] PhaseSpace d n)
    (p : Pauli d n) : (liftApply F p).coords = F p.coords := rfl

@[simp] theorem liftApply_scalar (F : PhaseSpace d n ≃ₗ[ZMod d] PhaseSpace d n)
    (c : ZMod d) : liftApply F (scalar c) = scalar c := by
  ext <;> simp [liftApply, coords]

/-- The Weyl correction turns symplecticity into exact multiplicativity. -/
theorem liftApply_mul (hd : Odd d) (F : symplecticGroup d n) (p q : Pauli d n) :
    liftApply F (p*q) = liftApply F p * liftApply F q := by
  have hh := two_mul_half d hd
  have hs := F.property p.coords q.coords
  change symplectic (F.val p.coords) (F.val q.coords) = symplectic p.coords q.coords at hs
  simp only [symplectic] at hs
  change dot (F.val p.coords).1 (F.val q.coords).2 -
    dot (F.val p.coords).2 (F.val q.coords).1 = dot p.z q.x - dot p.x q.z at hs
  rw [dot_comm ((F.val p.coords).2) ((F.val q.coords).1), dot_comm p.x q.z] at hs
  apply Pauli.ext
  · simp only [liftApply, mul_phase, mul_x, mul_z, coords_mul, map_add,
      Prod.fst_add, Prod.snd_add, dot_add_left, dot_add_right]
    linear_combination -half d * hs +
      (dot (F.val p.coords).1 (F.val q.coords).2 - dot p.z q.x) * hh
  · simp [liftApply, coords_mul]
  · simp [liftApply, coords_mul]

@[simp] theorem liftApply_inverse (F : PhaseSpace d n ≃ₗ[ZMod d] PhaseSpace d n)
    (p : Pauli d n) : liftApply F.symm (liftApply F p) = p := by
  apply Pauli.ext
  · simp [liftApply, coords]
  · change (F.symm (F p.coords)).2 = p.x
    simp [coords]
  · change (F.symm (F p.coords)).1 = p.z
    simp [coords]

/-- Explicit lift, with no assumed Clifford/symplectic correspondence. -/
def liftSymplectic (hd : Odd d) (F : symplecticGroup d n) : MulAut (Pauli d n) where
  toFun := liftApply F
  invFun := liftApply F.val.symm
  left_inv := liftApply_inverse F.val
  right_inv := liftApply_inverse F.val.symm
  map_mul' := liftApply_mul hd F

theorem liftSymplectic_fixesScalars (hd : Odd d) (F : symplecticGroup d n) :
    FixesScalars (liftSymplectic hd F) := by
  intro c
  exact liftApply_scalar F.val c

/-- The lift has precisely the prescribed exponent action. -/
theorem action_liftSymplectic (hd : Odd d) (F : symplecticGroup d n)
    (v : PhaseSpace d n) : action (liftSymplectic hd F) v = F.val v := by
  change (liftApply F (representative v)).coords = F.val v
  rw [coords_liftApply, coords_representative]

/-- Algebraic symplectic surjectivity for odd dimension. The realization of
these automorphisms by the paper's circuit generators is not assumed here. -/
theorem symplecticAction_surjective (hd : Odd d) (F : symplecticGroup d n) :
    ∃ (φ : MulAut (Pauli d n)) (hφ : FixesScalars φ), symplecticAction φ hφ = F := by
  refine ⟨liftSymplectic hd F, liftSymplectic_fixesScalars hd F, ?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  exact action_liftSymplectic hd F

end Pauli
end QuditClifford
