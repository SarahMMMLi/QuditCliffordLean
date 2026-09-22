import QuditClifford.NormalBoxes

/-!
# Concrete two-wire B and D boxes

Figure 6 defines B as an optional `S;H` on the top wire, controlled addition,
and SWAP; D as an optional `S;H` on the bottom wire, controlled phase, and SWAP.
This file proves their exponent actions directly from those primitive words.
All pairs of wire coordinates are ordered top to bottom, and each wire is `(z,x)`.
These are semantic linear-action statements over a field, without rewrite claims.
-/

noncomputable section
namespace QuditClifford.NormalBoxes
variable {K : Type*} [Field K]

abbrev TwoWire (K : Type*) := Vector K × Vector K

def twoBracket (v w : TwoWire K) : K := bracket v.1 w.1 + bracket v.2 w.2

def onFirst (f : Vector K →ₗ[K] Vector K) : TwoWire K →ₗ[K] TwoWire K :=
  f.prodMap LinearMap.id

def onSecond (f : Vector K →ₗ[K] Vector K) : TwoWire K →ₗ[K] TwoWire K :=
  LinearMap.id.prodMap f

def wireSwap : TwoWire K →ₗ[K] TwoWire K where
  toFun v := (v.2, v.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Exponent action of controlled addition to the lower wire. -/
def cxAction (c : K) : TwoWire K →ₗ[K] TwoWire K where
  toFun v := ((v.1.1 - c * v.2.1, v.1.2), (v.2.1, v.2.2 + c * v.1.2))
  map_add' u v := by ext <;> simp <;> ring
  map_smul' t v := by ext <;> simp <;> ring

/-- Exponent action of controlled phase. -/
def czAction (c : K) : TwoWire K →ₗ[K] TwoWire K where
  toFun v := ((v.1.1 + c * v.2.2, v.1.2), (v.2.1 + c * v.1.2, v.2.2))
  map_add' u v := by ext <;> simp <;> ring
  map_smul' t v := by ext <;> simp <;> ring

theorem wireSwap_preserves (v w : TwoWire K) :
    twoBracket (wireSwap v) (wireSwap w) = twoBracket v w := by
  simp [twoBracket, wireSwap, add_comm]

theorem cxAction_preserves (c : K) (v w : TwoWire K) :
    twoBracket (cxAction c v) (cxAction c w) = twoBracket v w := by
  simp [twoBracket, bracket, cxAction]
  ring

theorem czAction_preserves (c : K) (v w : TwoWire K) :
    twoBracket (czAction c v) (czAction c w) = twoBracket v w := by
  simp [twoBracket, bracket, czAction]
  ring

/-- The concrete Figure 6 B box, including its two branches. -/
def bAction (a b : K) : TwoWire K →ₗ[K] TwoWire K := by
  classical
  exact if a = 0 then wireSwap.comp (cxAction b)
    else wireSwap.comp ((cxAction a).comp (onFirst (fourier.comp (shear (-b / a)))))

/-- The concrete Figure 6 D box, including its two branches. -/
def dAction (a b : K) : TwoWire K →ₗ[K] TwoWire K := by
  classical
  exact if a = 0 then wireSwap.comp (czAction (-b))
    else wireSwap.comp ((czAction (-a)).comp (onSecond (fourier.comp (shear (-b / a)))))

theorem bAction_zero (b : K) (v : TwoWire K) :
    bAction 0 b v = ((v.2.1, v.2.2 + b * v.1.2), (v.1.1 - b * v.2.1, v.1.2)) := by
  simp [bAction, wireSwap, cxAction]

theorem bAction_nonzero (a b : K) (ha : a ≠ 0) (v : TwoWire K) :
    bAction a b v =
      ((v.2.1, v.2.2 + b * v.1.2 - a * v.1.1),
        (v.1.2 - a * v.2.1, -v.1.1 + b / a * v.1.2)) := by
  simp only [bAction, if_neg ha, LinearMap.comp_apply, onFirst,
    LinearMap.prodMap_apply, LinearMap.id_apply, fourier, shear, cxAction, wireSwap,
    LinearMap.coe_mk, AddHom.coe_mk]
  ext <;> dsimp <;> field_simp <;> ring

theorem dAction_zero (b : K) (v : TwoWire K) :
    dAction 0 b v = ((v.2.1 - b * v.1.2, v.2.2), (v.1.1 - b * v.2.2, v.1.2)) := by
  simp [dAction, wireSwap, czAction, sub_eq_add_neg]

theorem dAction_nonzero (a b : K) (ha : a ≠ 0) (v : TwoWire K) :
    dAction a b v =
      ((v.2.2 - a * v.1.2, -v.2.1 + b / a * v.2.2),
        (v.1.1 + a * v.2.1 - b * v.2.2, v.1.2)) := by
  simp only [dAction, if_neg ha, LinearMap.comp_apply, onSecond,
    LinearMap.prodMap_apply, LinearMap.id_apply, fourier, shear, czAction, wireSwap,
    LinearMap.coe_mk, AddHom.coe_mk]
  ext <;> dsimp <;> field_simp <;> ring

/-- The required B-box action in Figure 5. -/
@[simp] theorem bAction_input (a b : K) :
    bAction a b ((b, a), zVector) = (zVector, 0) := by
  by_cases ha : a = 0
  · subst a
    simp [bAction_zero, zVector]
  · rw [bAction_nonzero a b ha]
    ext <;> simp [zVector, ha, div_eq_mul_inv]; ring

/-- The additional B-box action in Figure 5. -/
@[simp] theorem bAction_lower_x (a b : K) :
    bAction a b (0, xVector) = (xVector, 0) := by
  by_cases ha : a = 0
  · subst a
    simp [bAction_zero, xVector]
  · simp [bAction_nonzero a b ha, xVector]

/-- The required D-box action in Figure 5, uniformly for every exponent `j`. -/
@[simp] theorem dAction_input (a b j : K) :
    dAction a b ((j, 1), (b, a)) = (0, (j, 1)) := by
  by_cases ha : a = 0
  · subst a
    simp [dAction_zero]
  · rw [dAction_nonzero a b ha]
    ext <;> simp [ha, div_eq_mul_inv]; ring

/-- The additional D-box action in Figure 5. -/
@[simp] theorem dAction_upper_z (a b : K) :
    dAction a b (zVector, 0) = (0, zVector) := by
  by_cases ha : a = 0
  · subst a
    simp [dAction_zero, zVector]
  · simp [dAction_nonzero a b ha, zVector]

theorem bAction_preserves (a b : K) (v w : TwoWire K) :
    twoBracket (bAction a b v) (bAction a b w) = twoBracket v w := by
  by_cases ha : a = 0
  · subst a
    rw [bAction_zero, bAction_zero]
    dsimp [twoBracket, bracket]
    ring
  · rw [bAction_nonzero a b ha, bAction_nonzero a b ha]
    dsimp [twoBracket, bracket]
    field_simp
    ring

theorem dAction_preserves (a b : K) (v w : TwoWire K) :
    twoBracket (dAction a b v) (dAction a b w) = twoBracket v w := by
  by_cases ha : a = 0
  · subst a
    rw [dAction_zero, dAction_zero]
    dsimp [twoBracket, bracket]
    ring
  · rw [dAction_nonzero a b ha, dAction_nonzero a b ha]
    dsimp [twoBracket, bracket]
    field_simp
    ring

/-- The two-wire symplectic form is nondegenerate. -/
theorem twoBracket_ext (v w : TwoWire K)
    (h : ∀ u, twoBracket v u = twoBracket w u) : v = w := by
  apply Prod.ext
  · apply bracket_ext
    intro u
    simpa [twoBracket, bracket] using h (u, 0)
  · apply bracket_ext
    intro u
    simpa [twoBracket, bracket] using h (0, u)

theorem bAction_injective (a b : K) : Function.Injective (bAction a b) := by
  intro v w h
  apply twoBracket_ext v w
  intro u
  rw [← bAction_preserves a b v u, ← bAction_preserves a b w u, h]

theorem dAction_injective (a b : K) : Function.Injective (dAction a b) := by
  intro v w h
  apply twoBracket_ext v w
  intro u
  rw [← dAction_preserves a b v u, ← dAction_preserves a b w u, h]

end QuditClifford.NormalBoxes
