import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Tactic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! # The paper's exact scalar convention

The character used below is the standard complex character of `ZMod d`,
not an abstract root supplied as a hypothesis.  `scalarGenerator` is the
Figure 1 scalar `-ω`; the ordinary Pauli scalar is `omega`.
-/

noncomputable section
namespace QuditClifford

variable (d : ℕ) [NeZero d]

/-- `ω^x`, with the exponent interpreted modulo `d`. -/
def phase (x : ZMod d) : ℂ := ZMod.stdAddChar x

/-- The paper's primitive `d`th root of unity `exp (2πi/d)`. -/
def omega : ℂ := phase d 1

/-- The scalar generator of Figure 1, as distinct from the Pauli scalar. -/
def scalarGenerator : ℂ := -omega d

@[simp] theorem phase_zero : phase d 0 = 1 := (ZMod.stdAddChar (N := d)).map_zero_eq_one

@[simp] theorem phase_add (x y : ZMod d) :
    phase d (x + y) = phase d x * phase d y :=
  (ZMod.stdAddChar (N := d)).map_add_eq_mul x y

@[simp] theorem phase_neg (x : ZMod d) : phase d (-x) = (phase d x)⁻¹ :=
  (ZMod.stdAddChar (N := d)).map_neg_eq_inv x

@[simp] theorem phase_star (x : ZMod d) : star (phase d x) = phase d (-x) := by
  rw [phase_neg]
  exact (Circle.coe_inv_eq_conj (ZMod.toCircle x)).symm

theorem phase_injective : Function.Injective (phase d) := ZMod.injective_stdAddChar

@[simp] theorem phase_eq_one_iff (x : ZMod d) : phase d x = 1 ↔ x = 0 := by
  rw [← phase_zero d]
  exact (phase_injective d).eq_iff

@[simp] theorem phase_ne_zero (x : ZMod d) : phase d x ≠ 0 := by
  intro h
  have hmul := phase_add d x (-x)
  simp [h] at hmul

theorem phase_nsmul (n : ℕ) (x : ZMod d) : phase d (n • x) = phase d x ^ n :=
  (ZMod.stdAddChar (N := d)).map_nsmul_eq_pow n x

@[simp] theorem phase_pow_dimension (x : ZMod d) : phase d x ^ d = 1 := by
  rw [← phase_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, phase_zero]

@[simp] theorem omega_pow_dimension : omega d ^ d = 1 := phase_pow_dimension d 1

theorem omega_exp : omega d = Complex.exp (2 * Real.pi * Complex.I / d) := by
  simpa [omega, phase] using (ZMod.stdAddChar_coe (N := d) (1 : ℤ))

theorem omega_ne_one (hd : 1 < d) : omega d ≠ 1 := by
  haveI : Fact (1 < d) := ⟨hd⟩
  exact fun h ↦ one_ne_zero ((phase_eq_one_iff d 1).mp h)

/-- Character orthogonality, valid for any nonzero dimension, including composite ones. -/
theorem phase_sum (a : ZMod d) :
    ∑ x : ZMod d, phase d (a * x) = if a = 0 then (d : ℂ) else 0 := by
  split_ifs with h
  · simp [h]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar d h)

@[simp] theorem scalarGenerator_pow_twice_dimension : scalarGenerator d ^ (2 * d) = 1 := by
  rw [scalarGenerator, pow_mul, neg_sq, ← pow_mul, mul_comm 2 d, pow_mul, omega_pow_dimension]
  simp

theorem scalarGenerator_pow_dimension (hd : Odd d) : scalarGenerator d ^ d = -1 := by
  rw [scalarGenerator, hd.neg_pow, omega_pow_dimension]

theorem scalarGenerator_pow_dimension_add_one (hd : Odd d) :
    scalarGenerator d ^ (d + 1) = omega d := by
  rw [pow_succ, scalarGenerator_pow_dimension d hd, scalarGenerator]
  ring

/-- Integer representatives agree with powers of the paper's primitive root. -/
theorem phase_natCast (n : ℕ) : phase d (n : ZMod d) = omega d ^ n := by
  simpa [omega, nsmul_eq_mul] using phase_nsmul d n 1

theorem omega_pow_eq_one_iff (n : ℕ) : omega d ^ n = 1 ↔ d ∣ n := by
  rw [← phase_natCast, phase_eq_one_iff, ZMod.natCast_zmod_eq_zero_iff_dvd]

/-- The order is exactly d, not just a divisor of d. -/
theorem omega_primitive : IsPrimitiveRoot (omega d) d where
  pow_eq_one := omega_pow_dimension d
  dvd_of_pow_eq_one n hn := (omega_pow_eq_one_iff d n).mp hn

/-- The Figure 1 scalar generator has exact order 2d for odd d. -/
theorem scalarGenerator_primitive (hd : Odd d) : IsPrimitiveRoot (scalarGenerator d) (2 * d) where
  pow_eq_one := scalarGenerator_pow_twice_dimension d
  dvd_of_pow_eq_one n hn := by
    have htwo : 2 ∣ n := by
      apply (IsPrimitiveRoot.neg_one (R := ℂ) 0 (by decide)).dvd_of_pow_eq_one n
      calc
        (-1 : ℂ) ^ n = (scalarGenerator d ^ d) ^ n := by rw [scalarGenerator_pow_dimension d hd]
        _ = (scalarGenerator d ^ n) ^ d := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
        _ = 1 := by rw [hn, one_pow]
    have hdvd : d ∣ n := by
      apply (omega_pow_eq_one_iff d n).mp
      simpa only [scalarGenerator, (even_iff_two_dvd.mpr htwo).neg_pow] using hn
    exact (Nat.coprime_two_left.mpr hd).mul_dvd_of_dvd_of_dvd htwo hdvd

/-- In odd dimension, the Pauli phases do not contain the additional sign. -/
theorem neg_one_not_phase (hd : Odd d) (x : ZMod d) : phase d x ≠ -1 := by
  intro hx
  have heq := congrArg (fun z : ℂ ↦ z ^ d) hx
  dsimp only at heq
  rw [phase_pow_dimension, hd.neg_one_pow] at heq
  norm_num at heq

end QuditClifford
