import QuditClifford.Symplectic
import Mathlib.Algebra.Module.ZMod

/-!
# Center-fixing Pauli automorphisms and their symplectic action

This proves the algebraic part of the Pauli-to-symplectic correspondence in
Section 2.2.4. It acts on the concrete Heisenberg coordinates already proved
faithful in `PauliRepresentation`. It does not define the Clifford matrix group
to be an abstract symplectic group or assume the paper's quotient theorem.
-/

namespace QuditClifford
namespace Pauli

variable {d n : ℕ}

/-- The zero-phase representative of a phase-space vector. -/
def representative (v : PhaseSpace d n) : Pauli d n := ⟨0, v.2, v.1⟩

@[simp] theorem coords_representative (v : PhaseSpace d n) : (representative v).coords = v := rfl
@[simp] theorem representative_zero : representative (0 : PhaseSpace d n) = 1 := rfl

/-- Physical conjugation fixes each scalar, rather than merely preserving the
set of scalar operators. This is the hypothesis needed by the quotient action. -/
def FixesScalars (φ : MulAut (Pauli d n)) : Prop := ∀ c, φ (scalar c) = scalar c

theorem FixesScalars.symm {φ : MulAut (Pauli d n)} (h : FixesScalars φ) :
    FixesScalars φ.symm := by
  intro c
  apply φ.injective
  simpa using (h c).symm

/-- The induced phase-space action, initially just a function. -/
def action (φ : MulAut (Pauli d n)) (v : PhaseSpace d n) : PhaseSpace d n :=
  (φ (representative v)).coords

theorem coords_map_of_coords_eq (φ : MulAut (Pauli d n)) (hφ : FixesScalars φ)
    {p q : Pauli d n} (h : p.coords = q.coords) : (φ p).coords = (φ q).coords := by
  obtain ⟨c, rfl⟩ := (coords_eq_iff p q).mp h
  simp only [map_mul, hφ c, coords_mul]
  change (0 : PhaseSpace d n) + (φ q).coords = (φ q).coords
  exact zero_add _

/-- The action is independent of the chosen Pauli representative. -/
theorem action_coords (φ : MulAut (Pauli d n)) (hφ : FixesScalars φ) (p : Pauli d n) :
    action φ p.coords = (φ p).coords :=
  coords_map_of_coords_eq φ hφ (coords_representative p.coords)

@[simp] theorem action_zero (φ : MulAut (Pauli d n)) : action φ 0 = 0 := by
  simp [action]

theorem action_add (φ : MulAut (Pauli d n)) (hφ : FixesScalars φ)
    (v w : PhaseSpace d n) : action φ (v+w) = action φ v + action φ w := by
  have h := action_coords φ hφ (representative v * representative w)
  simpa [action, map_mul] using h

/-- The quotient action is additive and hence linear over ZMod d. -/
def actionLinear (φ : MulAut (Pauli d n)) (hφ : FixesScalars φ) :
    PhaseSpace d n →ₗ[ZMod d] PhaseSpace d n :=
  ({ toFun := action φ, map_zero' := action_zero φ,
     map_add' := action_add φ hφ } : PhaseSpace d n →+ PhaseSpace d n).toZModLinearMap d

@[simp] theorem actionLinear_apply (φ : MulAut (Pauli d n)) (hφ : FixesScalars φ)
    (v : PhaseSpace d n) : actionLinear φ hφ v = action φ v := rfl

theorem action_symm_action (φ : MulAut (Pauli d n)) (hφ : FixesScalars φ)
    (v : PhaseSpace d n) : action φ.symm (action φ v) = v := by
  change action φ.symm (φ (representative v)).coords = v
  rw [action_coords φ.symm hφ.symm, φ.symm_apply_apply, coords_representative]

/-- A scalar-fixing group automorphism induces an invertible linear map. -/
def actionEquiv (φ : MulAut (Pauli d n)) (hφ : FixesScalars φ) :
    PhaseSpace d n ≃ₗ[ZMod d] PhaseSpace d n where
  toLinearMap := actionLinear φ hφ
  invFun := action φ.symm
  left_inv := action_symm_action φ hφ
  right_inv := by
    intro v
    exact action_symm_action φ.symm hφ.symm v

@[simp] theorem actionEquiv_apply (φ : MulAut (Pauli d n)) (hφ : FixesScalars φ)
    (v : PhaseSpace d n) : actionEquiv φ hφ v = action φ v := rfl

/-- Scalar-fixing automorphisms preserve the exact commutator exponent. -/
theorem commutatorPhase_map (φ : MulAut (Pauli d n)) (hφ : FixesScalars φ)
    (p q : Pauli d n) : commutatorPhase (φ p) (φ q) = commutatorPhase p q := by
  have hp := congrArg φ (commutation p q)
  simp only [map_mul, hφ] at hp
  have he := (commutation (φ p) (φ q)).symm.trans hp
  have hs := mul_right_cancel he
  simpa only [hφ _, scalar_phase] using congrArg Pauli.phase hs

/-- The induced action preserves Definition 2.25's symplectic form. -/
theorem action_preserves (φ : MulAut (Pauli d n)) (hφ : FixesScalars φ) :
    PreservesSymplectic (action φ) := by
  intro v w
  simpa only [commutatorPhase_eq_symplectic, coords_representative, action] using
    commutatorPhase_map φ hφ (representative v) (representative w)

/-- A genuine element of the existing linear symplectic group. -/
def symplecticAction (φ : MulAut (Pauli d n)) (hφ : FixesScalars φ) :
    symplecticGroup d n := ⟨actionEquiv φ hφ, action_preserves φ hφ⟩

/-- The exact phase acquired by an automorphism with trivial exponent action. -/
def phaseDifference (φ : MulAut (Pauli d n)) (p : Pauli d n) : ZMod d :=
  (φ p).phase - p.phase

theorem phaseDifference_mul (φ : MulAut (Pauli d n))
    (h : ∀ p, (φ p).coords = p.coords) (p q : Pauli d n) :
    phaseDifference φ (p*q) = phaseDifference φ p + phaseDifference φ q := by
  have hpx : (φ p).x = p.x := congrArg Prod.snd (h p)
  have hpz : (φ p).z = p.z := congrArg Prod.fst (h p)
  have hqx : (φ q).x = q.x := congrArg Prod.snd (h q)
  simp only [phaseDifference, map_mul, mul_phase, hpz, hqx]
  abel

theorem phaseDifference_scalar_mul (φ : MulAut (Pauli d n)) (hφ : FixesScalars φ)
    (c : ZMod d) (p : Pauli d n) :
    phaseDifference φ (scalar c * p) = phaseDifference φ p := by
  simp [phaseDifference, map_mul, hφ c]

theorem phaseDifference_coords (φ : MulAut (Pauli d n)) (hφ : FixesScalars φ)
    (p : Pauli d n) : phaseDifference φ (representative p.coords) = phaseDifference φ p := by
  have hp : p = scalar p.phase * representative p.coords := by
    ext <;> simp [representative, coords]
  conv_rhs => rw [hp, phaseDifference_scalar_mul φ hφ]

/-- The residual phase is a linear functional on the exponent space. -/
def correctionLinear (φ : MulAut (Pauli d n)) (hφ : FixesScalars φ)
    (h : ∀ p, (φ p).coords = p.coords) : PhaseSpace d n →ₗ[ZMod d] ZMod d :=
  ({ toFun := fun v => phaseDifference φ (representative v)
     map_zero' := by simp [phaseDifference]
     map_add' := by
       intro v w
       have hc := phaseDifference_coords φ hφ (representative v * representative w)
       simpa only [coords_mul, coords_representative, phaseDifference_mul φ h] using hc
    } : PhaseSpace d n →+ ZMod d).toZModLinearMap d

/-- Every linear phase functional is represented uniquely by the nondegenerate
symplectic form, with an explicit coordinate formula. -/
def dualVector (L : PhaseSpace d n →ₗ[ZMod d] ZMod d) : PhaseSpace d n :=
  (fun i => L (0, exponentBasis i), fun i => -L (exponentBasis i, 0))

theorem symplectic_dualVector (L : PhaseSpace d n →ₗ[ZMod d] ZMod d)
    (v : PhaseSpace d n) : symplectic (dualVector L) v = L v := by
  have hv : v = (∑ i : Fin n, v.1 i • (exponentBasis i, (0 : Fin n → ZMod d))) +
      ∑ i : Fin n, v.2 i • ((0 : Fin n → ZMod d), exponentBasis i) := by
    ext k <;> simp [Prod.fst_sum, Prod.snd_sum, exponentBasis, Finset.sum_apply, Pi.smul_apply, mul_ite]
  have hL : L v = (∑ i, v.1 i * L (exponentBasis i, 0)) +
      ∑ i, v.2 i * L (0, exponentBasis i) := by
    conv_lhs => rw [hv]
    simp only [map_add, map_sum, map_smul, smul_eq_mul]
  rw [hL]
  simp [symplectic, dualVector, dot, mul_comm, Finset.sum_neg_distrib]
  abel

/-- Pauli conjugation is exactly a symplectic phase correction. -/
theorem conjugation_formula (p q : Pauli d n) :
    p * q * p⁻¹ = scalar (symplectic p.coords q.coords) * q := by
  rw [← commutatorPhase_eq_symplectic, commutation p q]
  simp [mul_assoc]

/-- The kernel of the action on Pauli exponents consists of inner Pauli
automorphisms. This is an algebraic kernel theorem, not an assumption of the
Clifford-to-symplectic quotient isomorphism. -/
theorem trivial_action_iff_inner (φ : MulAut (Pauli d n)) (hφ : FixesScalars φ) :
    (∀ p, (φ p).coords = p.coords) ↔ ∃ q : Pauli d n, φ = MulAut.conj q := by
  constructor
  · intro h
    let L := correctionLinear φ hφ h
    let q := representative (dualVector L)
    refine ⟨q, ?_⟩
    apply MulEquiv.ext
    intro p
    change φ p = q * p * q⁻¹
    rw [conjugation_formula]
    have hv : symplectic q.coords p.coords = phaseDifference φ p := by
      change symplectic (dualVector L) p.coords = _
      rw [symplectic_dualVector]
      exact phaseDifference_coords φ hφ p
    rw [hv]
    have hx : (φ p).x = p.x := congrArg Prod.snd (h p)
    have hz : (φ p).z = p.z := congrArg Prod.fst (h p)
    apply Pauli.ext
    · simp [phaseDifference]
    · simp [hx]
    · simp [hz]
  · rintro ⟨q, rfl⟩ p
    simp only [MulAut.conj_apply, conjugation_formula, coords_mul]
    change (0 : PhaseSpace d n) + p.coords = p.coords
    exact zero_add _

/-- The exponent of the Pauli correction is unique, although its scalar is
invisible to conjugation (the uniqueness scope used in Lemma 4.5). -/
theorem inner_eq_iff_coords_eq (p q : Pauli d n) :
    MulAut.conj p = MulAut.conj q ↔ p.coords = q.coords := by
  constructor
  · intro h
    apply symplectic_ext
    intro v
    have he := congrArg (fun f : MulAut (Pauli d n) => f (representative v)) h
    simp only [MulAut.conj_apply, conjugation_formula] at he
    have hc := congrArg Pauli.phase he
    simpa using hc
  · intro h
    apply MulEquiv.ext
    intro r
    simp only [MulAut.conj_apply, conjugation_formula, h]

end Pauli
end QuditClifford
