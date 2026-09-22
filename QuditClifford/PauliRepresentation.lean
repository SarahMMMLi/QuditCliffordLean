import QuditClifford.Pauli
import QuditClifford.RootOfUnity

/-!
# Faithful complex matrix representation of Pauli coordinates

An abstract tuple `(c,x,z)` acts on a computational basis state `|j⟩` as
`ω^(c + z·j) |j+x⟩`. This file proves that this interpretation preserves
multiplication and is injective. Thus the abstract coordinate normal form is
also a unique normal form for the actual complex matrices, including phases.
-/

noncomputable section
namespace QuditClifford
namespace Pauli

variable {d n : ℕ} [NeZero d]

/-- Computational basis labels for `n` qudits of dimension `d`. -/
abbrev Basis (d n : ℕ) := Fin n → ZMod d

/-- Exact complex matrix of the ordered Pauli expression `ω^c X^x Z^z`. -/
def repr (p : Pauli d n) : Matrix (Basis d n) (Basis d n) ℂ :=
  fun row col => if row = col + p.x then QuditClifford.phase d (p.phase + dot p.z col) else 0

@[simp] theorem repr_one : repr (1 : Pauli d n) = 1 := by
  classical
  ext row col
  simp [repr, Matrix.one_apply]

@[simp] theorem repr_mul (p q : Pauli d n) : repr (p * q) = repr p * repr q := by
  classical
  ext row col
  simp only [Matrix.mul_apply, repr, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true, mul_phase, mul_z, mul_x]
  have hrow : col + (p.x + q.x) = col + q.x + p.x := by abel
  rw [hrow]
  split_ifs with h
  · rw [← phase_add]
    congr 1
    rw [dot_add_left, dot_add_right]
    abel
  · simp

/-- The representation is a monoid homomorphism into complex matrices. -/
def reprHom : Pauli d n →* Matrix (Basis d n) (Basis d n) ℂ where
  toFun := repr
  map_one' := repr_one
  map_mul' := repr_mul

/-- A nonzero shifted diagonal entry records a Pauli's phase polynomial. -/
@[simp] theorem repr_shift (p : Pauli d n) (col : Basis d n) :
    repr p (col + p.x) col = QuditClifford.phase d (p.phase + dot p.z col) := by
  simp [repr]

/-- Distinct Pauli coordinates denote distinct complex matrices. -/
theorem repr_injective : Function.Injective (repr : Pauli d n → _) := by
  classical
  intro p q h
  have hx : p.x = q.x := by
    by_contra hne
    have he := congrFun (congrFun h p.x) 0
    simp [repr, hne] at he
  have hc : p.phase = q.phase := by
    apply phase_injective d
    have he := congrFun (congrFun h p.x) 0
    simpa [repr, hx] using he
  have hdots (col : Basis d n) : dot p.z col = dot q.z col := by
    have he := congrFun (congrFun h (col + p.x)) col
    have hargs : p.phase + dot p.z col = q.phase + dot q.z col :=
      phase_injective d (by simpa [repr, hx] using he)
    rw [hc] at hargs
    exact add_left_cancel hargs
  have hz : p.z = q.z := by
    funext i
    have hi := hdots (Pi.single i 1)
    simpa [dot, Pi.single_apply] using hi
  exact Pauli.ext hc hx hz

/-- Matrix equality is exactly equality of the three ordered Pauli coordinates. -/
theorem repr_eq_iff (p q : Pauli d n) :
    repr p = repr q ↔ p.phase = q.phase ∧ p.x = q.x ∧ p.z = q.z := by
  constructor
  · intro h
    have hpq := repr_injective h
    exact ⟨congrArg Pauli.phase hpq, congrArg Pauli.x hpq, congrArg Pauli.z hpq⟩
  · rintro ⟨hc, hx, hz⟩
    exact congrArg repr (Pauli.ext hc hx hz)

/-- Uniqueness of the ordered Pauli normal form for actual complex matrices. -/
theorem matrix_normal_form_unique
    (c c' : ZMod d) (x x' z z' : Basis d n) :
    repr (scalar c) * repr (X x) * repr (Z z) =
      repr (scalar c') * repr (X x') * repr (Z z') ↔
      c = c' ∧ x = x' ∧ z = z' := by
  rw [← repr_mul, ← repr_mul, ← repr_mul, ← repr_mul]
  rw [repr_injective.eq_iff]
  exact normal_form_unique c c' x x' z z'

/-- Pauli coordinates are exactly a phase and two exponent vectors. -/
def equivCoordinates : Pauli d n ≃ ZMod d × Basis d n × Basis d n where
  toFun p := (p.phase, p.x, p.z)
  invFun c := ⟨c.1, c.2.1, c.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype (Pauli d n) :=
  Fintype.ofEquiv (ZMod d × Basis d n × Basis d n) equivCoordinates.symm

/-- The abstract ordinary Pauli group has the cardinality in Definition 2.9. -/
theorem card : Fintype.card (Pauli d n) = d ^ (2 * n + 1) := by
  calc
    _ = d * (d ^ n * d ^ n) := by rw [Fintype.card_congr equivCoordinates]; simp
    _ = d ^ (n + n + 1) := by rw [← pow_add, pow_succ]; ring
    _ = d ^ (2 * n + 1) := by congr 1; omega

/-- The actual complex Pauli matrices have the same cardinality, by faithfulness. -/
theorem card_matrix_range :
    Nat.card (Set.range (repr : Pauli d n → _)) = d ^ (2 * n + 1) := by
  rw [← Nat.card_congr (Equiv.ofInjective repr repr_injective), Nat.card_eq_fintype_card, card]

end Pauli
end QuditClifford

namespace QuditClifford

/-- The exact Pauli group for Figure 1: a central sign times an ordinary Pauli. -/
abbrev SignedPauli (d n : ℕ) := Multiplicative (ZMod 2) × Pauli d n

namespace SignedPauli

variable {d n : ℕ} [NeZero d]

/-- Exact complex matrix, with the sign represented by the standard character of `ZMod 2`. -/
def repr (p : SignedPauli d n) :
    Matrix (Pauli.Basis d n) (Pauli.Basis d n) ℂ :=
  phase 2 (Multiplicative.toAdd p.1) • Pauli.repr p.2

@[simp] theorem repr_one : repr (1 : SignedPauli d n) = 1 := by
  simp [repr]

@[simp] theorem repr_mul (p q : SignedPauli d n) : repr (p * q) = repr p * repr q := by
  simp only [repr, Prod.fst_mul, Prod.snd_mul, Pauli.repr_mul]
  rw [smul_mul_smul_comm, ← phase_add]
  rfl

/-- The exact signed representation as a monoid homomorphism. -/
def reprHom : SignedPauli d n →* Matrix (Pauli.Basis d n) (Pauli.Basis d n) ℂ where
  toFun := repr
  map_one' := repr_one
  map_mul' := repr_mul

omit [NeZero d] in
/-- Signs are unchanged by an odd power. -/
theorem sign_odd_pow (hd : Odd d) (s : ZMod 2) : phase 2 s ^ d = phase 2 s := by
  obtain ⟨k, hk⟩ := hd
  rw [hk, pow_add, pow_mul, phase_pow_dimension]
  simp

/-- A sign and an odd-order phase have unique coordinates. -/
theorem scalar_coordinates_injective (hd : Odd d) :
    Function.Injective (fun p : ZMod 2 × ZMod d => phase 2 p.1 * phase d p.2) := by
  rintro ⟨s, c⟩ ⟨t, e⟩ h
  have hs : s = t := by
    apply phase_injective 2
    have hp := congrArg (fun z : ℂ => z ^ d) h
    simpa only [mul_pow, phase_pow_dimension, mul_one, sign_odd_pow hd] using hp
  have hc : c = e := by
    apply phase_injective d
    exact mul_left_cancel₀ (phase_ne_zero 2 s) (hs ▸ h)
  exact Prod.ext hs hc

/-- Figure 1's enlarged Pauli coordinates are faithful when the dimension is odd. -/
theorem repr_injective (hd : Odd d) :
    Function.Injective (repr : SignedPauli d n → _) := by
  classical
  intro p q h
  have hx : p.2.x = q.2.x := by
    by_contra hne
    have he := congrFun (congrFun h p.2.x) 0
    simp [repr, Pauli.repr, hne] at he
  have hsc : (Multiplicative.toAdd p.1, p.2.phase) =
      (Multiplicative.toAdd q.1, q.2.phase) := by
    apply scalar_coordinates_injective hd
    have he := congrFun (congrFun h p.2.x) 0
    simpa [repr, Pauli.repr, hx] using he
  have hs : p.1 = q.1 := by
    change Multiplicative.toAdd p.1 = Multiplicative.toAdd q.1
    exact congrArg (fun r : ZMod 2 × ZMod d => r.1) hsc
  have hp : Pauli.repr p.2 = Pauli.repr q.2 := by
    ext row col
    have he := congrFun (congrFun h row) col
    simp only [repr, Matrix.smul_apply, smul_eq_mul, hs] at he
    exact mul_left_cancel₀ (phase_ne_zero _ _) he
  exact Prod.ext hs (Pauli.repr_injective hp)

/-- The nontrivial standard character value of `ZMod 2` is the usual complex sign. -/
theorem phase_two_one : phase 2 1 = (-1 : ℂ) := by
  have hsq : phase 2 1 ^ 2 = 1 := phase_pow_dimension 2 1
  have hne : phase 2 1 ≠ 1 := by simp
  exact (sq_eq_one_iff.mp hsq).resolve_left hne

/-- Figure 1's `-ω` scalar, represented intrinsically in the enlarged group. -/
def scalarGenerator : SignedPauli d n :=
  (Multiplicative.ofAdd 1, Pauli.scalar 1)

/-- The abstract enlarged scalar denotes precisely the paper's complex `-ω`. -/
theorem repr_scalarGenerator : repr (scalarGenerator : SignedPauli d n) =
    QuditClifford.scalarGenerator d • (1 : Matrix (Pauli.Basis d n) (Pauli.Basis d n) ℂ) := by
  classical
  ext row col
  simp only [repr, scalarGenerator, Matrix.smul_apply, smul_eq_mul]
  change phase 2 1 * Pauli.repr (Pauli.scalar 1) row col = _
  rw [phase_two_one]
  simp only [Pauli.repr, Pauli.scalar_x, add_zero, Pauli.scalar_phase,
    Pauli.scalar_z, dot_zero_left, Matrix.one_apply, QuditClifford.scalarGenerator,
    omega]
  split_ifs <;> ring

/-- An exact signed Pauli matrix is the identity precisely at the group identity. -/
theorem repr_eq_one_iff (hd : Odd d) (p : SignedPauli d n) :
    repr p = 1 ↔ p = 1 := by
  rw [← repr_one, (repr_injective hd).eq_iff]

/-- The enlarged abstract group has one independent sign coordinate. -/
theorem card : Fintype.card (SignedPauli d n) = 2 * d ^ (2 * n + 1) := by
  simp [SignedPauli, Pauli.card]

/-- Cardinality of the exact signed Pauli matrices in odd dimension. -/
theorem card_matrix_range (hd : Odd d) :
    Nat.card (Set.range (repr : SignedPauli d n → _)) = 2 * d ^ (2 * n + 1) := by
  rw [← Nat.card_congr (Equiv.ofInjective repr (repr_injective hd)),
    Nat.card_eq_fintype_card, card]

end SignedPauli
end QuditClifford
