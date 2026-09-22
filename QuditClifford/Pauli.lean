import Mathlib

/-!
# Abstract Pauli coordinates

This file formalizes the finite Heisenberg group underlying Definition 2.9 and
Equation (7) of *A Complete and Natural Rule Set for Multi-Qudit Clifford Circuits
in All Odd Prime Dimensions*. An element `(c,x,z)` represents the expression
`ω^c X^x Z^z`. This is an abstract algebraic model: identification with the paper's
complex matrices requires a separate faithful representation theorem.

The central phase here is `ω`, as in Definition 2.9; this group does not
include the additional `-ω` scalar of Figure 1 and is not a definition of the
full exact Clifford scalar group.

The group laws below work for every modulus, without an odd-prime hypothesis.
-/

namespace QuditClifford

/-- Dot product of exponent vectors. -/
def dot {d n : ℕ} (u v : Fin n → ZMod d) : ZMod d :=
  ∑ i, u i * v i

@[simp] theorem dot_zero_left {d n : ℕ} (v : Fin n → ZMod d) : dot 0 v = 0 := by
  simp [dot]

@[simp] theorem dot_zero_right {d n : ℕ} (u : Fin n → ZMod d) : dot u 0 = 0 := by
  simp [dot]

theorem dot_add_left {d n : ℕ} (u v w : Fin n → ZMod d) :
    dot (u + v) w = dot u w + dot v w := by
  simp [dot, add_mul, Finset.sum_add_distrib]

theorem dot_add_right {d n : ℕ} (u v w : Fin n → ZMod d) :
    dot u (v + w) = dot u v + dot u w := by
  simp [dot, mul_add, Finset.sum_add_distrib]

@[simp] theorem dot_neg_left {d n : ℕ} (u v : Fin n → ZMod d) :
    dot (-u) v = -dot u v := by simp [dot]

@[simp] theorem dot_neg_right {d n : ℕ} (u v : Fin n → ZMod d) :
    dot u (-v) = -dot u v := by simp [dot]

theorem dot_comm {d n : ℕ} (u v : Fin n → ZMod d) : dot u v = dot v u := by
  simp [dot, mul_comm]

/-- Coordinates for `ω^phase X^x Z^z`, with the `X` factor before `Z`. -/
@[ext] structure Pauli (d n : ℕ) where
  phase : ZMod d
  x : Fin n → ZMod d
  z : Fin n → ZMod d
  deriving DecidableEq

namespace Pauli

variable {d n : ℕ}

instance : One (Pauli d n) := ⟨⟨0, 0, 0⟩⟩

/-- The cocycle `dot p.z q.x` comes from `ZX = ωXZ`, Equation (7). -/
instance : Mul (Pauli d n) :=
  ⟨fun p q => ⟨p.phase + q.phase + dot p.z q.x, p.x + q.x, p.z + q.z⟩⟩

instance : Inv (Pauli d n) :=
  ⟨fun p => ⟨-p.phase + dot p.z p.x, -p.x, -p.z⟩⟩

@[simp] theorem one_phase : (1 : Pauli d n).phase = 0 := rfl
@[simp] theorem one_x : (1 : Pauli d n).x = 0 := rfl
@[simp] theorem one_z : (1 : Pauli d n).z = 0 := rfl
@[simp] theorem mul_phase (p q : Pauli d n) :
    (p * q).phase = p.phase + q.phase + dot p.z q.x := rfl
@[simp] theorem mul_x (p q : Pauli d n) : (p * q).x = p.x + q.x := rfl
@[simp] theorem mul_z (p q : Pauli d n) : (p * q).z = p.z + q.z := rfl
@[simp] theorem inv_phase (p : Pauli d n) : p⁻¹.phase = -p.phase + dot p.z p.x := rfl
@[simp] theorem inv_x (p : Pauli d n) : p⁻¹.x = -p.x := rfl
@[simp] theorem inv_z (p : Pauli d n) : p⁻¹.z = -p.z := rfl

instance : Group (Pauli d n) where
  mul_assoc p q r := by
    ext <;> simp only [mul_phase, mul_x, mul_z, dot_add_left, dot_add_right, Pi.add_apply] <;> abel
  one_mul p := by ext <;> simp
  mul_one p := by ext <;> simp
  inv_mul_cancel p := by ext <;> simp

/-- Central phase with exponent `c`. -/
def scalar (c : ZMod d) : Pauli d n := ⟨c, 0, 0⟩

/-- Tensor product of `X` powers. -/
def X (x : Fin n → ZMod d) : Pauli d n := ⟨0, x, 0⟩

/-- Tensor product of `Z` powers. -/
def Z (z : Fin n → ZMod d) : Pauli d n := ⟨0, 0, z⟩

@[simp] theorem scalar_phase (c : ZMod d) : (scalar c : Pauli d n).phase = c := rfl
@[simp] theorem scalar_x (c : ZMod d) : (scalar c : Pauli d n).x = 0 := rfl
@[simp] theorem scalar_z (c : ZMod d) : (scalar c : Pauli d n).z = 0 := rfl
@[simp] theorem X_phase (x : Fin n → ZMod d) : (X x).phase = 0 := rfl
@[simp] theorem X_x (x : Fin n → ZMod d) : (X x).x = x := rfl
@[simp] theorem X_z (x : Fin n → ZMod d) : (X x).z = 0 := rfl
@[simp] theorem Z_phase (z : Fin n → ZMod d) : (Z z).phase = 0 := rfl
@[simp] theorem Z_x (z : Fin n → ZMod d) : (Z z).x = 0 := rfl
@[simp] theorem Z_z (z : Fin n → ZMod d) : (Z z).z = z := rfl

@[simp] theorem scalar_add (a b : ZMod d) :
    (scalar (a + b) : Pauli d n) = scalar a * scalar b := by ext <;> simp

@[simp] theorem scalar_zero : (scalar 0 : Pauli d n) = 1 := rfl

@[simp] theorem X_add (u v : Fin n → ZMod d) : X (u + v) = X u * X v := by
  ext <;> simp

@[simp] theorem Z_add (u v : Fin n → ZMod d) : Z (u + v) = Z u * Z v := by
  ext <;> simp

theorem scalar_commutes (c : ZMod d) (p : Pauli d n) : scalar c * p = p * scalar c := by
  ext <;> simp [add_comm]

/-- The ordered-coordinate decomposition in the abstract model (cf. §3.2).
This does not by itself prove uniqueness for the paper's matrix operators. -/
theorem normal_form (p : Pauli d n) : p = scalar p.phase * X p.x * Z p.z := by
  ext <;> simp

/-- Uniqueness of ordered coordinates in the abstract model. -/
theorem normal_form_unique (c c' : ZMod d) (x x' z z' : Fin n → ZMod d) :
    scalar c * X x * Z z = scalar c' * X x' * Z z' ↔
      c = c' ∧ x = x' ∧ z = z' := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg phase h,
      by simpa using congrArg Pauli.x h, by simpa using congrArg Pauli.z h⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

/-- Generalized Weyl commutation, Equation (7). -/
theorem Z_mul_X (z x : Fin n → ZMod d) :
    Z z * X x = scalar (dot z x) * X x * Z z := by
  ext <;> simp

/-- Commutator phase of two ordered Pauli expressions. -/
def commutatorPhase (p q : Pauli d n) : ZMod d := dot p.z q.x - dot q.z p.x

theorem commutation (p q : Pauli d n) :
    p * q = scalar (commutatorPhase p q) * (q * p) := by
  ext <;> simp [commutatorPhase] <;> abel

theorem commute_iff (p q : Pauli d n) :
    p * q = q * p ↔ commutatorPhase p q = 0 := by
  constructor
  · intro h
    have hphase := congrArg phase h
    simp only [mul_phase] at hphase
    dsimp [commutatorPhase]
    linear_combination hphase
  · intro h
    simpa [h] using commutation p q

/-- Two tuples differ only by a central phase exactly when their exponent vectors agree. -/
theorem same_exponents_iff (p q : Pauli d n) :
    p.x = q.x ∧ p.z = q.z ↔ ∃ c : ZMod d, p = scalar c * q := by
  constructor
  · rintro ⟨hx, hz⟩
    refine ⟨p.phase - q.phase, ?_⟩
    ext <;> simp [hx, hz]
  · rintro ⟨c, rfl⟩
    simp

end Pauli
end QuditClifford
