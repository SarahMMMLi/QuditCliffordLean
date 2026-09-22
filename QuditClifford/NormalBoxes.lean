import QuditClifford.Symplectic

/-!
# Concrete one-qudit normal boxes from Figure 6

Coordinates in this file are `(z,x)`, so the label `A_ab` has preimage `(b,a)`
of `Z`. The definitions implement Figure 6 in circuit order: `A_0b = M_b`
and `A_ab = S^(-b/a); H; M_a` when `a ≠ 0`, and `E_b = S^(-b)`.
The resulting Figure 6 action of `A_0b` sends `X` to `X^b`: the extra
`Z^(-1)` printed in Appendix C, Figure 10, is incompatible with Figure 6.

All statements here concern concrete linear exponent actions, not derivations
from the paper's rewriting relations or complex-matrix circuit equalities.
They work over any field; oddness is not needed at this level.
-/

noncomputable section
namespace QuditClifford.NormalBoxes

variable {K : Type*} [Field K]

abbrev Vector (K : Type*) := K × K

def bracket (v w : Vector K) : K := v.1 * w.2 - v.2 * w.1

def zVector : Vector K := (1, 0)
def xVector : Vector K := (0, 1)

@[simp] theorem bracket_z_left (v : Vector K) : bracket zVector v = v.2 := by
  simp [bracket, zVector]

@[simp] theorem bracket_x_right (v : Vector K) : bracket v xVector = v.1 := by
  simp [bracket, xVector]

/-- The two Pauli generators separate one-wire exponent vectors. -/
theorem bracket_ext (v w : Vector K) (h : ∀ u, bracket v u = bracket w u) : v = w := by
  apply Prod.ext
  · simpa using h xVector
  · have hh := h zVector
    simpa [bracket, zVector] using hh

/-- Exponent action of the concrete phase gate power `S^c`. -/
def shear (c : K) : Vector K →ₗ[K] Vector K where
  toFun v := (v.1 + c * v.2, v.2)
  map_add' u v := by ext <;> simp; ring
  map_smul' t v := by ext <;> simp; ring

/-- Exponent action of the concrete Hadamard. -/
def fourier : Vector K →ₗ[K] Vector K where
  toFun v := (v.2, -v.1)
  map_add' u v := by ext <;> simp; ring
  map_smul' t v := by ext <;> simp

/-- Exponent formula of the concrete multiplier, used only at nonzero labels. -/
def multiplier (c : K) : Vector K →ₗ[K] Vector K where
  toFun v := (v.1 / c, c * v.2)
  map_add' u v := by ext <;> simp [add_div]; ring
  map_smul' t v := by ext <;> simp [div_eq_mul_inv] <;> ring

/-- Figure 6's allowed labels, with `a` the X exponent and `b` the Z exponent. -/
structure ABox (K : Type*) [Field K] where
  a : K
  b : K
  nonzero : (b, a) ≠ (0, 0)

namespace ABox

variable (A : ABox K)

/-- The nonzero Pauli vector named by the box label. -/
def input : Vector K := (A.b, A.a)

@[simp] theorem input_ne_zero : A.input ≠ 0 := A.nonzero

theorem b_ne_zero (ha : A.a = 0) : A.b ≠ 0 := by
  intro hb
  exact A.nonzero (by simp [ha, hb])

/-- The actual Figure 6 primitive word, composed in temporal order. -/
def action : Vector K →ₗ[K] Vector K := by
  classical
  exact if A.a = 0 then multiplier A.b
  else (multiplier A.a).comp (fourier.comp (shear (-A.b / A.a)))

@[simp] theorem action_of_a_zero (ha : A.a = 0) (v : Vector K) :
    A.action v = (v.1 / A.b, A.b * v.2) := by
  simp [action, ha, multiplier]

@[simp] theorem action_of_a_ne_zero (ha : A.a ≠ 0) (v : Vector K) :
    A.action v = (v.2 / A.a, A.b * v.2 - A.a * v.1) := by
  simp only [action, if_neg ha, LinearMap.comp_apply, multiplier, fourier, shear,
    LinearMap.coe_mk, AddHom.coe_mk]
  apply Prod.ext
  · rfl
  · field_simp
    ring

/-- The required A-box action in Figure 5, proved from the concrete word. -/
@[simp] theorem action_input : A.action A.input = zVector := by
  by_cases ha : A.a = 0
  · rw [A.action_of_a_zero ha]
    simp [input, zVector, ha, A.b_ne_zero ha]
  · rw [A.action_of_a_ne_zero ha]
    simp [input, zVector, ha, mul_comm]

/-- The symplectic form is preserved by each concrete A box. -/
theorem preserves (v w : Vector K) : bracket (A.action v) (A.action w) = bracket v w := by
  by_cases ha : A.a = 0
  · rw [A.action_of_a_zero ha, A.action_of_a_zero ha]
    dsimp [bracket]
    field_simp [A.b_ne_zero ha]
    ring
  · rw [A.action_of_a_ne_zero ha, A.action_of_a_ne_zero ha]
    dsimp [bracket]
    field_simp
    ring

theorem action_injective : Function.Injective A.action := by
  intro v w h
  apply bracket_ext v w
  intro u
  rw [← A.preserves v u, ← A.preserves w u, h]

/-- A box has no other preimage of `Z`, giving uniqueness of its label. -/
theorem action_eq_z_iff (v : Vector K) : A.action v = zVector ↔ v = A.input := by
  constructor
  · intro h
    have h₂ := A.preserves v xVector
    have hz := A.preserves A.input xVector
    rw [h] at h₂
    rw [A.action_input] at hz
    have he : v.1 = A.input.1 := by
      simpa only [bracket_x_right] using h₂.symm.trans hz
    have h₃ := A.preserves v zVector
    have hi := A.preserves A.input zVector
    rw [h] at h₃
    rw [A.action_input] at hi
    have hx : v.2 = A.input.2 := by
      have := h₃.symm.trans hi
      simpa [bracket, zVector] using this
    exact Prod.ext he hx
  · rintro rfl
    exact A.action_input

@[ext] theorem ext {A B : ABox K} (ha : A.a = B.a) (hb : A.b = B.b) : A = B := by
  cases A
  cases B
  simp_all

/-- For each nonzero vector, exactly one concrete A-box label sends it to `Z`.
This is the one-wire case of Lemma 3.4. -/
theorem existsUnique_normalizer (v : Vector K) (hv : v ≠ 0) :
    ∃! A : ABox K, A.action v = zVector := by
  refine ⟨⟨v.2, v.1, hv⟩, ?_, ?_⟩
  · exact action_input _
  · intro B hB
    have h := (B.action_eq_z_iff v).mp hB
    exact ABox.ext (congrArg Prod.snd h.symm) (congrArg Prod.fst h.symm)

end ABox

/-- The concrete E box `E_b = S^(-b)` from Figure 6. -/
def eAction (b : K) : Vector K →ₗ[K] Vector K := shear (-b)

@[simp] theorem eAction_apply (b : K) (v : Vector K) :
    eAction b v = (v.1 - b * v.2, v.2) := by
  simp [eAction, shear, sub_eq_add_neg]

@[simp] theorem eAction_input (b : K) : eAction b (b, 1) = xVector := by
  simp [xVector]

@[simp] theorem eAction_z (b : K) : eAction b zVector = zVector := by
  simp [zVector]

theorem eAction_preserves (b : K) (v w : Vector K) :
    bracket (eAction b v) (eAction b w) = bracket v w := by
  simp only [eAction_apply, bracket]
  ring

/-- The one-wire case of Lemma 3.5. -/
theorem eAction_eq_x_iff (b : K) (v : Vector K) :
    eAction b v = xVector ↔ v = (b, 1) := by
  rw [eAction_apply]
  constructor
  · intro h
    have hx : v.2 = 1 := congrArg Prod.snd h
    have hz : v.1 = b := by
      have hz := congrArg Prod.fst h
      simpa [xVector, hx, sub_eq_zero] using hz
    exact Prod.ext hz hx
  · rintro rfl
    simp [xVector]

@[simp] theorem eAction_eq_z_iff (b : K) (v : Vector K) :
    eAction b v = zVector ↔ v = zVector := by
  rw [eAction_apply]
  constructor
  · intro h
    have hx : v.2 = 0 := congrArg Prod.snd h
    have hz : v.1 = 1 := by
      have hz := congrArg Prod.fst h
      simpa [zVector, hx] using hz
    exact Prod.ext hz hx
  · rintro rfl
    simp [zVector]

/-- The literal one-qudit normal form of Remark 3.3: an A box followed by an E box. -/
structure OneQuditNormal (K : Type*) [Field K] where
  first : ABox K
  last : K

namespace OneQuditNormal

variable (N : OneQuditNormal K)

/-- The linear action of the concrete A;E circuit. -/
def action : Vector K →ₗ[K] Vector K := (eAction N.last).comp N.first.action

@[simp] theorem action_apply (v : Vector K) :
    N.action v = eAction N.last (N.first.action v) := rfl

@[simp] theorem action_first_input : N.action N.first.input = zVector := by
  rw [action_apply, ABox.action_input, eAction_z]

@[simp] theorem action_eq_z_iff (v : Vector K) :
    N.action v = zVector ↔ v = N.first.input := by
  rw [action_apply, eAction_eq_z_iff, N.first.action_eq_z_iff]

theorem preserves (v w : Vector K) : bracket (N.action v) (N.action w) = bracket v w := by
  rw [action_apply, action_apply, eAction_preserves, N.first.preserves]

@[ext] theorem ext {N M : OneQuditNormal K}
    (hfirst : N.first = M.first) (hlast : N.last = M.last) : N = M := by
  cases N
  cases M
  simp_all

/-- The one-qudit case of Lemma 3.7, with concrete boxes and both uniqueness claims. -/
theorem existsUnique_pair_normalizer (v w : Vector K) (hvw : bracket v w = 1) :
    ∃! N : OneQuditNormal K, N.action v = zVector ∧ N.action w = xVector := by
  have hv : v ≠ 0 := by
    rintro rfl
    simp [bracket] at hvw
  let A : ABox K := ⟨v.2, v.1, hv⟩
  have hinput : A.input = v := rfl
  have hAv : A.action v = zVector := hinput ▸ A.action_input
  have hx : (A.action w).2 = 1 := by
    have h := A.preserves v w
    rw [hAv, bracket_z_left, hvw] at h
    exact h
  refine ⟨⟨A, (A.action w).1⟩, ⟨?_, ?_⟩, ?_⟩
  · change eAction _ (A.action v) = zVector
    rw [hAv, eAction_z]
  · change eAction _ (A.action w) = xVector
    rw [eAction_eq_x_iff]
    exact Prod.ext rfl hx
  · intro M hM
    have hm := (M.action_eq_z_iff v).mp hM.1
    have hA : M.first = A :=
      ABox.ext (congrArg Prod.snd hm.symm) (congrArg Prod.fst hm.symm)
    apply OneQuditNormal.ext hA
    have he := (eAction_eq_x_iff M.last (M.first.action w)).mp hM.2
    have hez := congrArg Prod.fst he
    simpa only [hA] using hez.symm

end OneQuditNormal

/-- A one-wire exponent vector is the corresponding combination of the Pauli basis. -/
theorem vector_decomposition (v : Vector K) : v = v.1 • zVector + v.2 • xVector := by
  ext <;> simp [zVector, xVector]

/-- Values on Z and X determine a one-wire linear map. -/
theorem linearMap_ext (f g : Vector K →ₗ[K] Vector K)
    (hz : f zVector = g zVector) (hx : f xVector = g xVector) : f = g := by
  apply LinearMap.ext
  intro v
  conv_lhs => rw [vector_decomposition v, map_add, map_smul, map_smul, hz, hx]
  conv_rhs => rw [vector_decomposition v, map_add, map_smul, map_smul]

/-- Remark 3.3 and the one-qudit instance of Proposition 3.8: every symplectic
linear equivalence has exactly one concrete A;E exponent action. This is not a
matrix-level or a rewrite-derivability claim. -/
theorem existsUnique_oneQuditNormal
    (f : Vector K ≃ₗ[K] Vector K)
    (hf : ∀ v w, bracket (f v) (f w) = bracket v w) :
    ∃! N : OneQuditNormal K, N.action = f.toLinearMap := by
  have hp : bracket (f.symm zVector) (f.symm xVector) = 1 := by
    have h := hf (f.symm zVector) (f.symm xVector)
    simpa [bracket, zVector, xVector] using h.symm
  obtain ⟨N, hN, huniq⟩ :=
    OneQuditNormal.existsUnique_pair_normalizer (f.symm zVector) (f.symm xVector) hp
  refine ⟨N, ?_, ?_⟩
  · have hcomp : N.action.comp f.symm.toLinearMap = LinearMap.id := by
      apply linearMap_ext
      · exact hN.1
      · exact hN.2
    apply LinearMap.ext
    intro v
    have h := LinearMap.congr_fun hcomp (f v)
    simpa using h
  · intro M hM
    apply huniq
    constructor <;> simp [hM]

end QuditClifford.NormalBoxes
