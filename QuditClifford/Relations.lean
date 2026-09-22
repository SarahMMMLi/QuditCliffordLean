import QuditClifford.Gates
import Mathlib.Data.Matrix.Kronecker

/-!
# Exact soundness of elementary Figure 1 identities

This module checks identities of complex matrices, retaining all scalars. The
raw permutation matrices used for SWAP and CX still need to be identified with
the derived circuit words in Figure 2; the identities here do not constitute a
proof of soundness or completeness of that syntactic presentation by themselves.
-/

noncomputable section
namespace QuditClifford

open Matrix
open scoped Kronecker

/-- A diagonal matrix can be pushed through any computational-basis map. -/
theorem diagonal_basisMap {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → α) (w v : α → ℂ) (h : ∀ j, w (f j) = v j) :
    Matrix.diagonal w * basisMap f = basisMap f * Matrix.diagonal v := by
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, basisMap]
  split_ifs with hij
  · subst i
    simp [h]
  · simp

/-- Exact conjugation of a diagonal by a permutation of basis states. -/
theorem basisMap_diagonal_conjugate {α : Type*} [Fintype α] [DecidableEq α]
    (e : α ≃ α) (w : α → ℂ) :
    basisMap e.symm * Matrix.diagonal w * basisMap e = Matrix.diagonal (w ∘ e) := by
  rw [mul_assoc, diagonal_basisMap e w (w ∘ e) (fun _ => rfl), ← mul_assoc, basisMap_mul]
  have hid : e.symm ∘ e = id := by funext j; simp
  rw [hid, basisMap_id, one_mul]

variable (d : ℕ) [NeZero d]

/-- Parameterized powers of the quadratic phase, with a `ZMod d` exponent. -/
def phasePower (a : ZMod d) : QuditMatrix d :=
  Matrix.diagonal (fun j => phase d (a * quadratic d j))

@[simp] theorem phasePower_one : phasePower d 1 = S d := by simp [phasePower, S]
@[simp] theorem phasePower_zero : phasePower d 0 = 1 := by simp [phasePower]

theorem phasePower_add (a b : ZMod d) :
    phasePower d (a + b) = phasePower d a * phasePower d b := by
  simp [phasePower, ← Matrix.diagonal_mul_diagonal, add_mul]

theorem phasePower_nat (k : ℕ) : phasePower d (k : ZMod d) = S d ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.cast_add, Nat.cast_one, phasePower_add, phasePower_one, ih, pow_succ]

@[simp] theorem phasePower_neg_mul (a : ZMod d) : phasePower d (-a) * phasePower d a = 1 := by
  rw [← phasePower_add]
  simp

@[simp] theorem phasePower_mul_neg (a : ZMod d) : phasePower d a * phasePower d (-a) = 1 := by
  rw [← phasePower_add]
  simp

/-- C4, with its linear phase correction retained. -/
theorem C4_multiplier_phase (a : (ZMod d)ˣ) :
    multiplier d a * S d =
      clock d ((1 - (a : ZMod d)) * half d * (↑a⁻¹ : ZMod d) ^ 2) *
      phasePower d ((↑a⁻¹ : ZMod d) ^ 2) * multiplier d a := by
  ext i j
  simp only [multiplier, S, clock, phasePower, Matrix.mul_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul, basisMap]
  split_ifs with h
  · subst i
    simp only [mul_one, one_mul, Pi.mul_apply, ← phase_add]
    congr 1
    dsimp [quadratic]
    have ha : (↑a⁻¹ : ZMod d) * (a : ZMod d) = 1 := by simp
    linear_combination (-j * (j - 1) * half d * ((↑a⁻¹ : ZMod d) * (a : ZMod d) + 1)) * ha
  · simp

/-- An operator on the first of two wires. -/
def firstWire (A : QuditMatrix d) : TwoQuditMatrix d := A ⊗ₖ (1 : QuditMatrix d)
/-- An operator on the second of two wires. -/
def secondWire (A : QuditMatrix d) : TwoQuditMatrix d := (1 : QuditMatrix d) ⊗ₖ A

omit [NeZero d] in
@[simp] theorem firstWire_one : firstWire d 1 = 1 := Matrix.one_kronecker_one
omit [NeZero d] in
@[simp] theorem secondWire_one : secondWire d 1 = 1 := Matrix.one_kronecker_one

theorem firstWire_mul (A B : QuditMatrix d) :
    firstWire d (A * B) = firstWire d A * firstWire d B := by
  simpa [firstWire] using Matrix.mul_kronecker_mul A B (1 : QuditMatrix d) (1 : QuditMatrix d)

theorem secondWire_mul (A B : QuditMatrix d) :
    secondWire d (A * B) = secondWire d A * secondWire d B := by
  simpa [secondWire] using Matrix.mul_kronecker_mul (1 : QuditMatrix d) (1 : QuditMatrix d) A B

/-- Operators on distinct wires compose to their tensor product. -/
theorem firstWire_mul_secondWire (A B : QuditMatrix d) :
    firstWire d A * secondWire d B = A ⊗ₖ B := by
  simp only [firstWire, secondWire, ← Matrix.mul_kronecker_mul, mul_one, one_mul]

theorem secondWire_mul_firstWire (A B : QuditMatrix d) :
    secondWire d B * firstWire d A = A ⊗ₖ B := by
  simp only [firstWire, secondWire, ← Matrix.mul_kronecker_mul, mul_one, one_mul]

omit [NeZero d] in
@[simp] theorem firstWire_diagonal (f : ZMod d → ℂ) :
    firstWire d (Matrix.diagonal f) = Matrix.diagonal (fun j => f j.1) := by
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
    simp [firstWire, Matrix.kronecker_apply, Matrix.diagonal_apply, Matrix.one_apply, h₁, h₂]

omit [NeZero d] in
@[simp] theorem secondWire_diagonal (f : ZMod d → ℂ) :
    secondWire d (Matrix.diagonal f) = Matrix.diagonal (fun j => f j.2) := by
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
    simp [secondWire, Matrix.kronecker_apply, Matrix.diagonal_apply, Matrix.one_apply, h₁, h₂]

/-- Exact SWAP, without a global sign. -/
def SWAP : TwoQuditMatrix d := basisMap Prod.swap

/-- C7. -/
theorem C7_swap_sq : SWAP d * SWAP d = 1 := by
  rw [SWAP, basisMap_mul]
  have hs : (Prod.swap ∘ Prod.swap : ZMod d × ZMod d → _) = id := by funext j; simp
  rw [hs, basisMap_id]

/-- SWAP transports any one-wire operator, retaining its exact scalar. -/
theorem swap_firstWire (A : QuditMatrix d) :
    SWAP d * firstWire d A = secondWire d A * SWAP d := by
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  simp [SWAP, firstWire, secondWire, Matrix.mul_apply, basisMap,
    Matrix.kronecker_apply, Matrix.one_apply, Fintype.sum_prod_type, mul_ite, ite_mul]
  by_cases h : i₁ = j₂ <;> simp [h, eq_comm]

/-- C8. -/
theorem C8_controlled_phase_commutes : CZ d * firstWire d (S d) = firstWire d (S d) * CZ d := by
  simp only [CZ, S, firstWire_diagonal, Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext j
  exact mul_comm _ _

/-- C10. -/
theorem C10_swap_phase : SWAP d * firstWire d (S d) = secondWire d (S d) * SWAP d :=
  swap_firstWire d (S d)

/-- A controlled phase with its exponent interpreted modulo d. -/
def CZPower (a : ZMod d) : TwoQuditMatrix d :=
  Matrix.diagonal (fun j => phase d (a * (j.1 * j.2)))

@[simp] theorem CZPower_one : CZPower d 1 = CZ d := by simp [CZPower, CZ]

theorem CZPower_nat (k : ℕ) : CZPower d (k : ZMod d) = CZ d ^ k := by
  ext i j
  simp only [CZPower, CZ, Matrix.diagonal_pow, Matrix.diagonal_apply, Pi.pow_apply]
  split_ifs <;> simp [← phase_nsmul, nsmul_eq_mul]

/-- C9. -/
theorem C9_controlled_multiplier (a : (ZMod d)ˣ) :
    CZ d * firstWire d (multiplier d a) = firstWire d (multiplier d a) * CZPower d (a : ZMod d) := by
  have hfirst : firstWire d (multiplier d a) = basisMap (fun j : ZMod d × ZMod d =>
      ((a : ZMod d) * j.1, j.2)) := by
    ext i j
    rcases i with ⟨i₁, i₂⟩
    rcases j with ⟨j₁, j₂⟩
    by_cases h₁ : i₁ = (a : ZMod d) * j₁ <;> by_cases h₂ : i₂ = j₂ <;>
      simp [firstWire, multiplier, basisMap, Matrix.kronecker_apply, Matrix.one_apply, h₁, h₂]
  rw [hfirst, CZ, CZPower]
  apply diagonal_basisMap
  intro j
  congr 1
  ring

/-- Computational-basis controlled addition. -/
def controlledAddEquiv : (ZMod d × ZMod d) ≃ (ZMod d × ZMod d) where
  toFun j := (j.1, j.2 + j.1)
  invFun j := (j.1, j.2 - j.1)
  left_inv j := by ext <;> simp
  right_inv j := by ext <;> simp

/-- Raw CX action; its Fourier circuit implementation is a separate obligation. -/
def CX : TwoQuditMatrix d := basisMap (controlledAddEquiv d)
/-- Inverse raw CX action. -/
def CXinv : TwoQuditMatrix d := basisMap (controlledAddEquiv d).symm

@[simp] theorem CXinv_mul_CX : CXinv d * CX d = 1 := by
  rw [CXinv, CX, basisMap_mul]
  have h : (controlledAddEquiv d).symm ∘ controlledAddEquiv d = id := by funext j; simp
  rw [h, basisMap_id]

@[simp] theorem CX_mul_CXinv : CX d * CXinv d = 1 := by
  rw [CXinv, CX, basisMap_mul]
  have h : controlledAddEquiv d ∘ (controlledAddEquiv d).symm = id := by funext j; simp
  rw [h, basisMap_id]

omit [NeZero d] in
/-- The quadratic exponent identity underlying C12. -/
theorem quadratic_add (hd : Odd d) (x y : ZMod d) :
    quadratic d (x + y) = quadratic d x + quadratic d y + x * y := by
  have hh := two_mul_half d hd
  dsimp [quadratic]
  linear_combination x * y * hh

/-- C12 with negative powers represented explicitly by phase exponents. -/
theorem C12_controlled_add_phase (hd : Odd d) :
    (firstWire d (phasePower d (-1)) * secondWire d (phasePower d (-1))) *
      CXinv d * secondWire d (S d) * CX d = CZ d := by
  simp only [phasePower, S, firstWire_diagonal, secondWire_diagonal]
  rw [mul_assoc, mul_assoc, ← mul_assoc (CXinv d), CXinv, CX,
    basisMap_diagonal_conjugate]
  simp only [Matrix.diagonal_mul_diagonal]
  ext i j
  simp only [Matrix.diagonal_apply, CZ]
  split_ifs
  · simp only [Pi.mul_apply, Function.comp_apply, controlledAddEquiv, Equiv.coe_fn_mk, neg_one_mul,
      ← phase_add, quadratic_add d hd]
    congr 1
    ring
  · rfl

/-- C0 for the exact Figure 1 scalar generator. -/
theorem C0_scalar : scalarGenerator d ^ (2 * d) = 1 := scalarGenerator_pow_twice_dimension d

/-- C1. -/
theorem C1_phase_order : S d ^ d = 1 := S_pow_dimension d

/-- C2 with the raw multiplier and its explicit sign. -/
theorem C2_hadamard_square (hd : Odd d) :
    H d * H d = (-1 : ℂ) ^ ((d - 1) / 2) • multiplier d (-1) := by
  simpa [multiplier] using H_sq_exact d hd

/-- C3; restricting `k` to the representatives in `Fin d` gives the displayed family. -/
theorem C3_multiplier_power (a : (ZMod d)ˣ) (k : ℕ) :
    multiplier d a ^ k = multiplier d (a ^ k) := multiplier_pow d a k

/-- C6. -/
theorem C6_controlled_phase_order : CZ d ^ d = 1 := CZ_pow_dimension d

/-- C11 follows from the scalar-exact transport identity for every matrix. -/
theorem C11_swap_hadamard : SWAP d * firstWire d (H d) = secondWire d (H d) * SWAP d :=
  swap_firstWire d (H d)

/-- Reflection of one computational-basis coordinate. -/
def negationEquiv : ZMod d ≃ ZMod d where
  toFun j := -j
  invFun j := -j
  left_inv _ := neg_neg _
  right_inv _ := neg_neg _

/-- C5. -/
theorem C5_hadamard_phase (hd : Odd d) :
    S d * (H d * H d) * S d * (H d * H d) =
      (H d * H d) * S d * (H d * H d) * S d := by
  rw [H_sq_exact d hd]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  congr 1
  have hc : basisMap (fun j : ZMod d => -j) * S d * basisMap (fun j : ZMod d => -j) =
      Matrix.diagonal (fun j => phase d (quadratic d (-j))) := by
    simpa [S, negationEquiv] using
      basisMap_diagonal_conjugate (negationEquiv d) (fun j => phase d (quadratic d j))
  rw [mul_assoc (S d), mul_assoc (S d), hc]
  rw [S, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext j
  exact mul_comm _ _

abbrev ThreeQuditMatrix := Matrix (ZMod d × (ZMod d × ZMod d)) (ZMod d × (ZMod d × ZMod d)) ℂ

/-- Exact permutation of the first and second wires. -/
def SWAP12 : ThreeQuditMatrix d := basisMap (fun j => (j.2.1, (j.1, j.2.2)))
/-- Exact permutation of the second and third wires. -/
def SWAP23 : ThreeQuditMatrix d := basisMap (fun j => (j.1, (j.2.2, j.2.1)))
/-- Controlled phase on the first and second wires. -/
def CZ12 : ThreeQuditMatrix d := Matrix.diagonal (fun j => phase d (j.1 * j.2.1))
/-- Controlled phase on the second and third wires. -/
def CZ23 : ThreeQuditMatrix d := Matrix.diagonal (fun j => phase d (j.2.1 * j.2.2))
/-- Controlled phase on the first and third wires. -/
def CZ13 : ThreeQuditMatrix d := Matrix.diagonal (fun j => phase d (j.1 * j.2.2))
/-- Controlled addition from the first wire to the second. -/
def CX12 : ThreeQuditMatrix d := basisMap (fun j => (j.1, (j.2.1 + j.1, j.2.2)))

/-- C13, exact wire-swap braid identity. -/
theorem C13_swap_braid : SWAP12 d * SWAP23 d * SWAP12 d = SWAP23 d * SWAP12 d * SWAP23 d := by
  simp only [SWAP12, SWAP23, basisMap_mul]
  rfl

/-- C14. -/
theorem C14_swap_controlled_phase :
    SWAP23 d * SWAP12 d * CZ23 d = CZ12 d * SWAP23 d * SWAP12 d := by
  rw [mul_assoc (CZ12 d)]
  simp only [SWAP23, SWAP12, CZ12, CZ23, basisMap_mul]
  symm
  apply diagonal_basisMap
  intro j
  rfl

/-- C15, the three-wire controlled-phase/controlled-addition interaction. -/
theorem C15_controlled_interaction :
    CZ23 d * CX12 d = CZ13 d * CX12 d * CZ23 d := by
  ext i j
  simp only [CZ23, CZ13, CX12, Matrix.diagonal_mul, Matrix.mul_diagonal, basisMap]
  split_ifs with h
  · subst i
    simp [add_mul, mul_add, mul_comm]
  · simp

/-- The raw remote controlled phase agrees with its SWAP-conjugation definition. -/
theorem remote_controlled_phase : SWAP23 d * CZ12 d * SWAP23 d = CZ13 d := by
  let e : (ZMod d × (ZMod d × ZMod d)) ≃ (ZMod d × (ZMod d × ZMod d)) :=
    { toFun := fun j => (j.1, (j.2.2, j.2.1))
      invFun := fun j => (j.1, (j.2.2, j.2.1))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa [e, SWAP23, CZ12, CZ13] using
    basisMap_diagonal_conjugate e (fun j => phase d (j.1 * j.2.1))

end QuditClifford
