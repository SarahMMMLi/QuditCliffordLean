import QuditClifford.MultiplierDerivation
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# Quadratic Gauss sums and the exact multiplier scalar

The elementary finite sums are connected to mathlib's multiplicative-character
Gauss sums. This proves Legendre-relative scaling, exact magnitude, and
nonvanishing, and reduces the multiplier's closed-form scalar to one explicitly
defined sign `baseGaussSign d`. Its square is proved to be one here. The subsequent
module `GaussSign` proves the classical signed evaluation `baseGaussSign d = 1`
from the exact normalized Fourier determinant, removing the explicit hypothesis
of this module's conditional Lemma 2.14 theorem.
-/

noncomputable section
namespace QuditClifford

variable (d : ℕ) [Fact d.Prime]

/-- The standard quadratic exponential sum; its exact complex sign remains explicit. -/
def squareGaussSum (a : ZMod d) : ℂ := ∑ x : ZMod d, phase d (a * x ^ 2)

/-- The quadratic character with complex values, matching the paper's Legendre symbol. -/
def complexQuadraticChar : MulChar (ZMod d) ℂ :=
  (quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)

@[simp] theorem complexQuadraticChar_apply (a : ZMod d) :
    complexQuadraticChar d a = (quadraticChar (ZMod d) a : ℂ) := rfl

/-- The Legendre character is exactly the sign encoded by the primitive scalar word. -/
theorem complexQuadraticChar_eq_sign (a : (ZMod d)ˣ) :
    complexQuadraticChar d (a : ZMod d) =
      (-1 : ℂ) ^ (if IsSquare (a : ZMod d) then 0 else 1) := by
  simp only [complexQuadraticChar_apply, quadraticChar_apply, quadraticCharFun,
    a.ne_zero, ↓reduceIte]
  split_ifs <;> norm_num

/-- On integer representatives this is the standard Legendre symbol. -/
theorem complexQuadraticChar_eq_legendreSym (a : ZMod d) :
    complexQuadraticChar d a = (legendreSym d (a.val : ℤ) : ℂ) := by
  simp only [complexQuadraticChar_apply, legendreSym, Int.cast_natCast, ZMod.natCast_zmod_val]

/-- Counting square roots identifies the elementary quadratic sum with a character Gauss sum. -/
theorem squareGaussSum_eq_gaussSum (hd : Odd d) (a : ZMod d) (ha : a ≠ 0) :
    squareGaussSum d a =
      gaussSum (complexQuadraticChar d) (ZMod.stdAddChar.mulShift a) := by
  have hc : ringChar (ZMod d) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact fun h => (by decide : ¬Odd 2) (h ▸ hd)
  have hcard (y : ZMod d) :
      ((Finset.univ.filter (fun x : ZMod d => x ^ 2 = y)).card : ℂ) =
        complexQuadraticChar d y + 1 := by
    have h := quadraticChar_card_sqrts hc y
    simpa only [complexQuadraticChar_apply, Set.toFinset_setOf, Int.cast_natCast, Int.cast_add, Int.cast_one] using
      congrArg (fun z : ℤ => (z : ℂ)) h
  calc
    squareGaussSum d a =
        ∑ y : ZMod d, ∑ x ∈ Finset.univ.filter (fun x : ZMod d => x ^ 2 = y),
          phase d (a * x ^ 2) :=
      (Finset.sum_fiberwise Finset.univ (fun x : ZMod d => x ^ 2)
        (fun x => phase d (a * x ^ 2))).symm
    _ = ∑ y : ZMod d, (complexQuadraticChar d y + 1) * phase d (a * y) := by
      apply Finset.sum_congr rfl
      intro y _
      calc
        _ = ∑ _x ∈ Finset.univ.filter (fun x : ZMod d => x ^ 2 = y),
              phase d (a * y) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [(Finset.mem_filter.mp hx).2]
        _ = _ := by simp [hcard]
    _ = _ := by
      simp only [add_mul, one_mul, Finset.sum_add_distrib]
      rw [phase_sum, if_neg ha, add_zero]
      rfl

/-- Scaling the quadratic coefficient multiplies the Gauss sum by its Legendre symbol. -/
theorem squareGaussSum_mul (hd : Odd d) (a : (ZMod d)ˣ) (b : ZMod d) (hb : b ≠ 0) :
    squareGaussSum d ((a : ZMod d) * b) =
      complexQuadraticChar d (a : ZMod d) * squareGaussSum d b := by
  rw [squareGaussSum_eq_gaussSum d hd _ (mul_ne_zero a.ne_zero hb),
    squareGaussSum_eq_gaussSum d hd b hb]
  have h := gaussSum_mulShift (complexQuadraticChar d) (ZMod.stdAddChar.mulShift b) a
  have hshift : (ZMod.stdAddChar.mulShift b).mulShift (a : ZMod d) =
      ZMod.stdAddChar.mulShift ((a : ZMod d) * b) := by
    ext x
    simp only [AddChar.mulShift_apply]
    congr 1
    ring
  rw [hshift] at h
  have hs : complexQuadraticChar d (a : ZMod d) ^ 2 = 1 := by
    change (↑(quadraticChar (ZMod d) (a : ZMod d)) : ℂ) ^ 2 = 1
    exact_mod_cast quadraticChar_sq_one a.ne_zero
  calc
    _ = (complexQuadraticChar d (a : ZMod d)) ^ 2 *
          gaussSum (complexQuadraticChar d) (ZMod.stdAddChar.mulShift ((a : ZMod d) * b)) := by
      rw [hs, one_mul]
    _ = _ := by rw [pow_two, mul_assoc, h]

/-- Completing the square connects the paper's phase convention with the homogeneous sum. -/
theorem quadraticGaussSum_eq_squareGaussSum (hd : Odd d) (a : ZMod d) :
    quadraticGaussSum d a = phase d (-a * half d ^ 3) * squareGaussSum d (a * half d) := by
  have hh := two_mul_half d hd
  have hexp (x : ZMod d) : a * quadratic d x =
      -a * half d ^ 3 + (a * half d) * (x - half d) ^ 2 := by
    dsimp [quadratic]
    linear_combination a * half d * x * hh
  simp only [quadraticGaussSum, hexp, phase_add]
  rw [← Finset.mul_sum]
  congr 1
  exact Equiv.sum_comp (Equiv.subRight (half d)) (fun x => phase d ((a * half d) * x ^ 2))

/-- All nonzero coefficients reduce to one base sum and the explicit Legendre sign. -/
theorem quadraticGaussSum_relative (hd : Odd d) (a : (ZMod d)ˣ) :
    quadraticGaussSum d (a : ZMod d) =
      phase d ((1 - (a : ZMod d)) * half d ^ 3) *
        complexQuadraticChar d (a : ZMod d) * quadraticGaussSum d 1 := by
  have hh : half d ≠ 0 := by
    intro h
    simpa [h] using two_mul_half d hd
  rw [quadraticGaussSum_eq_squareGaussSum d hd,
    quadraticGaussSum_eq_squareGaussSum d hd, one_mul,
    squareGaussSum_mul d hd a _ hh]
  have hp : phase d (-(a : ZMod d) * half d ^ 3) =
      phase d ((1 - (a : ZMod d)) * half d ^ 3) * phase d (-1 * half d ^ 3) := by
    rw [← phase_add]
    congr 1
    ring
  rw [hp]
  ring

/-- Nontriviality of the complex Legendre character in odd prime dimension. -/
theorem complexQuadraticChar_ne_one (hd : Odd d) : complexQuadraticChar d ≠ 1 := by
  apply (MulChar.ringHomComp_ne_one_iff (show Function.Injective (Int.castRingHom ℂ) from Int.cast_injective)).mpr
  apply quadraticChar_ne_one
  rw [ZMod.ringChar_zmod_n]
  exact fun h => (by decide : ¬Odd 2) (h ▸ hd)

/-- The squared homogeneous Gauss sum has no remaining analytic sign ambiguity. -/
theorem squareGaussSum_sq (hd : Odd d) (a : ZMod d) (ha : a ≠ 0) :
    squareGaussSum d a ^ 2 = complexQuadraticChar d (-1) * (d : ℂ) := by
  rw [squareGaussSum_eq_gaussSum d hd a ha]
  simpa only [ZMod.card] using gaussSum_sq (complexQuadraticChar_ne_one d hd)
    ((quadraticChar_isQuadratic (ZMod d)).comp (Int.castRingHom ℂ))
    (AddChar.IsPrimitive.of_ne_one (ZMod.isPrimitive_stdAddChar d ha))

/-- In particular the homogeneous Gauss sum never vanishes at a nonzero coefficient. -/
theorem squareGaussSum_ne_zero (hd : Odd d) (a : ZMod d) (ha : a ≠ 0) :
    squareGaussSum d a ≠ 0 := by
  intro h
  have hs := squareGaussSum_sq d hd a ha
  rw [h, zero_pow (by decide : 2 ≠ 0)] at hs
  have hc : complexQuadraticChar d (-1) ≠ 0 := by
    simp only [complexQuadraticChar_apply, ne_eq, Int.cast_eq_zero, quadraticChar_eq_zero_iff,
      neg_eq_zero, one_ne_zero, not_false_eq_true]
  exact (mul_ne_zero hc (Nat.cast_ne_zero.mpr (NeZero.ne d))) hs.symm

/-- The phase-gate Gauss sum is nonzero for every invertible coefficient. -/
theorem quadraticGaussSum_ne_zero (hd : Odd d) (a : (ZMod d)ˣ) :
    quadraticGaussSum d (a : ZMod d) ≠ 0 := by
  rw [quadraticGaussSum_eq_squareGaussSum d hd]
  apply mul_ne_zero (phase_ne_zero d _)
  apply squareGaussSum_ne_zero d hd
  apply mul_ne_zero a.ne_zero
  intro h
  simpa [h] using two_mul_half d hd

/-- Complex conjugation acts on a homogeneous quadratic sum by the Legendre sign of -1. -/
theorem squareGaussSum_star (hd : Odd d) (a : ZMod d) (ha : a ≠ 0) :
    star (squareGaussSum d a) = complexQuadraticChar d (-1) * squareGaussSum d a := by
  calc
    star (squareGaussSum d a) = squareGaussSum d (-a) := by
      simp only [squareGaussSum, star_sum, phase_star, neg_mul]
    _ = _ := by simpa using squareGaussSum_mul d hd (-1) a ha

/-- The squared absolute value of the homogeneous quadratic Gauss sum is exactly d. -/
theorem squareGaussSum_star_mul (hd : Odd d) (a : ZMod d) (ha : a ≠ 0) :
    star (squareGaussSum d a) * squareGaussSum d a = (d : ℂ) := by
  rw [squareGaussSum_star d hd a ha, mul_assoc, ← pow_two, squareGaussSum_sq d hd a ha,
    ← mul_assoc, ← pow_two]
  have hs : complexQuadraticChar d (-1) ^ 2 = 1 := by
    simp only [complexQuadraticChar_apply]
    exact_mod_cast quadraticChar_sq_one (neg_ne_zero.mpr (one_ne_zero : (1 : ZMod d) ≠ 0))
  rw [hs, one_mul]

/-- The squared absolute value is unchanged by completing the square. -/
theorem quadraticGaussSum_star_mul (hd : Odd d) (a : (ZMod d)ˣ) :
    star (quadraticGaussSum d (a : ZMod d)) * quadraticGaussSum d (a : ZMod d) = (d : ℂ) := by
  rw [quadraticGaussSum_eq_squareGaussSum d hd]
  have hh : half d ≠ 0 := by
    intro h
    simpa [h] using two_mul_half d hd
  have hc : star (phase d (-(a : ZMod d) * half d ^ 3)) *
      phase d (-(a : ZMod d) * half d ^ 3) = 1 := by
    rw [phase_star, ← phase_add, neg_add_cancel, phase_zero]
  calc
    _ = (star (phase d (-(a : ZMod d) * half d ^ 3)) *
          phase d (-(a : ZMod d) * half d ^ 3)) *
        (star (squareGaussSum d ((a : ZMod d) * half d)) *
          squareGaussSum d ((a : ZMod d) * half d)) := by
      rw [star_mul]
      ring
    _ = _ := by rw [hc, one_mul, squareGaussSum_star_mul d hd _ (mul_ne_zero a.ne_zero hh)]

/-- The exact magnitude of the phase-gate Gauss sum. -/
theorem norm_quadraticGaussSum (hd : Odd d) (a : (ZMod d)ˣ) :
    ‖quadraticGaussSum d (a : ZMod d)‖ = Real.sqrt d := by
  rw [Complex.norm_def]
  congr 1
  apply Complex.ofReal_injective
  rw [Complex.normSq_eq_conj_mul_self]
  exact quadraticGaussSum_star_mul d hd a

/-- The square of the paper's Fourier normalization equals the Legendre sign of -1. -/
theorem lambda_sq_eq_complexQuadraticChar (hd : Odd d) :
    lambda d ^ 2 = complexQuadraticChar d (-1) := by
  have hc : ringChar (ZMod d) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact fun h => (by decide : ¬Odd 2) (h ▸ hd)
  rw [complexQuadraticChar_apply, quadraticChar_neg_one hc, ZMod.card,
    ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp hd), lambda_sq d hd]
  push_cast
  congr 1
  have hm := Nat.odd_iff.mp hd
  omega

/-- The sole remaining sign in the classical quadratic Gauss evaluation.
Its positive value is proved in the subsequent module `GaussSign`. -/
def baseGaussSign : ℂ := lambda d * squareGaussSum d (half d) / (Real.sqrt d : ℂ)

/-- The remaining base Gauss factor is a sign, not an arbitrary phase. -/
theorem baseGaussSign_sq (hd : Odd d) : baseGaussSign d ^ 2 = 1 := by
  have hh : half d ≠ 0 := by
    intro h
    simpa [h] using two_mul_half d hd
  have hs : (Real.sqrt d : ℂ) ^ 2 = (d : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg d)
  have hc : complexQuadraticChar d (-1) ^ 2 = 1 := by
    simp only [complexQuadraticChar_apply]
    exact_mod_cast quadraticChar_sq_one (neg_ne_zero.mpr (one_ne_zero : (1 : ZMod d) ≠ 0))
  rw [baseGaussSign, div_pow, mul_pow, lambda_sq_eq_complexQuadraticChar d hd,
    squareGaussSum_sq d hd _ hh, hs, ← mul_assoc, ← pow_two, hc, one_mul]
  exact div_self (Nat.cast_ne_zero.mpr (NeZero.ne d))

/-- Only a global sign remains in the base Gauss sum. This does not choose that sign. -/
theorem baseGaussSign_eq_one_or_neg_one (hd : Odd d) :
    baseGaussSign d = 1 ∨ baseGaussSign d = -1 :=
  sq_eq_one_iff.mp (baseGaussSign_sq d hd)

/-- The multiplier's exact finite-sum scalar is invertible. -/
theorem multiplierWordScalar_ne_zero (hd : Odd d) (a : (ZMod d)ˣ) :
    multiplierWordScalar d a ≠ 0 := by
  have hdim : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hsqrt : (Real.sqrt d : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (NeZero.pos d)))
  exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero (mul_ne_zero (lambda_ne_zero d) hsqrt)))
    (mul_ne_zero (mul_ne_zero (phase_ne_zero d _) (quadraticGaussSum_ne_zero d hd a)) hdim)

/-- An unconditional exact construction of the raw multiplier from the word and its
explicit finite-sum scalar. This is not yet the paper's closed-form scalar evaluation. -/
theorem multiplier_eq_correctedWord (hd : Odd d) (a : (ZMod d)ˣ) :
    multiplier d a = (multiplierWordScalar d a)⁻¹ • multiplierWord d a := by
  rw [multiplierWord_eq d hd, smul_smul, inv_mul_cancel₀ (multiplierWordScalar_ne_zero d hd a),
    one_smul]

/-- The three Fourier normalizations reduce the homogeneous base sum to the single sign. -/
theorem normalized_baseGaussSum (hd : Odd d) :
    ((lambda d * (Real.sqrt d : ℂ))⁻¹) ^ 3 *
      squareGaussSum d (half d) * (d : ℂ) = baseGaussSign d := by
  have hsqrt : (Real.sqrt d : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (NeZero.pos d)))
  have hs : (Real.sqrt d : ℂ) ^ 2 = (d : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg d)
  have hl : lambda d ^ 4 = 1 := by
    calc
      _ = (lambda d ^ 2) ^ 2 := by ring
      _ = 1 := by rw [lambda_sq d hd, ← pow_mul, Nat.mul_comm, pow_mul]; norm_num
  rw [baseGaussSign]
  field_simp [lambda_ne_zero d, hsqrt]
  linear_combination -(Real.sqrt d : ℂ) * squareGaussSum d (half d) * hs -
    (Real.sqrt d : ℂ) ^ 3 * squareGaussSum d (half d) * hl

/-- The exponent inverse to the explicit correction displayed in Lemma 2.14. -/
def multiplierResidualExponent (a : (ZMod d)ˣ) : ZMod d :=
  ((a : ZMod d) ^ 2 - 4 * (a : ZMod d) + 2) * (↑a⁻¹ : ZMod d) * half d ^ 3

/-- All coefficient dependence in the exact multiplier scalar is now evaluated.
The only remaining term here is the single dimension-dependent base Gauss sign,
which is evaluated in the subsequent module `GaussSign`. -/
theorem multiplierWordScalar_eq_baseGaussSign (hd : Odd d) (a : (ZMod d)ˣ) :
    multiplierWordScalar d a = baseGaussSign d * complexQuadraticChar d (a : ZMod d) *
      phase d (multiplierResidualExponent d a) := by
  have hh : half d ≠ 0 := by
    intro h
    simpa [h] using two_mul_half d hd
  have hexp : -((1 - (↑a⁻¹ : ZMod d)) * half d * multiplierXCorrection d a) +
      -(a : ZMod d) * half d ^ 3 = multiplierResidualExponent d a := by
    have hhalf := two_mul_half d hd
    have ha : (a : ZMod d) * (↑a⁻¹ : ZMod d) = 1 := a.val_inv
    dsimp [multiplierResidualExponent, multiplierXCorrection]
    linear_combination
      -((a : ZMod d) + (↑a⁻¹ : ZMod d) - 2) * half d ^ 2 * hhalf -
      (half d ^ 2 + ((a : ZMod d) - 4) * half d ^ 3) * ha
  rw [multiplierWordScalar, unnormalizedMultiplierScalar,
    quadraticGaussSum_eq_squareGaussSum d hd, squareGaussSum_mul d hd a _ hh]
  calc
    _ = (phase d (-((1 - (↑a⁻¹ : ZMod d)) * half d * multiplierXCorrection d a)) *
        phase d (-(a : ZMod d) * half d ^ 3)) * complexQuadraticChar d (a : ZMod d) *
        (((lambda d * (Real.sqrt d : ℂ))⁻¹) ^ 3 * squareGaussSum d (half d) * (d : ℂ)) := by
      ring
    _ = _ := by rw [← phase_add, hexp, normalized_baseGaussSum d hd]; ring

/-- Lemma 2.14 reduced to the classical choice of the base Gauss sign.
The hypothesis is proved in `GaussSign`, rather than assumed as an axiom. -/
theorem multiplierWord_eq_of_baseGaussSign (hd : Odd d) (hGauss : baseGaussSign d = 1)
    (a : (ZMod d)ˣ) :
    multiplierWord d a =
      (complexQuadraticChar d (a : ZMod d) * phase d (multiplierResidualExponent d a)) •
        multiplier d a := by
  rw [multiplierWord_eq d hd, multiplierWordScalar_eq_baseGaussSign d hd, hGauss, one_mul]

/-- The negative residual exponent is exactly the scalar exponent printed in Lemma 2.14. -/
theorem neg_multiplierResidualExponent (a : (ZMod d)ˣ) :
    -multiplierResidualExponent d a =
      (-(a : ZMod d)^2 + 4*(a : ZMod d) - 2) * (8*(a : ZMod d))⁻¹ := by
  have h8 : (8 : ZMod d)⁻¹ = half d ^ 3 := by
    rw [half, inv_pow]
    norm_num
  rw [mul_inv_rev, h8, ← Units.val_inv_eq_inv_val]
  dsimp [multiplierResidualExponent]
  ring

/-- The paper's scalar-corrected multiplier circuit has only the universal Gauss sign left. -/
theorem multiplier_derived_eq_baseGaussSign (hd : Odd d) (a : (ZMod d)ˣ) :
    (complexQuadraticChar d (a : ZMod d) *
      phase d ((-(a : ZMod d)^2 + 4*(a : ZMod d) - 2) * (8*(a : ZMod d))⁻¹)) •
        multiplierWord d a = baseGaussSign d • multiplier d a := by
  rw [multiplierWord_eq d hd, multiplierWordScalar_eq_baseGaussSign d hd, smul_smul,
    ← neg_multiplierResidualExponent]
  have hc : complexQuadraticChar d (a : ZMod d) ^ 2 = 1 := by
    simp only [complexQuadraticChar_apply]
    exact_mod_cast quadraticChar_sq_one a.ne_zero
  have hp : phase d (-multiplierResidualExponent d a) *
      phase d (multiplierResidualExponent d a) = 1 := by
    rw [← phase_add, neg_add_cancel, phase_zero]
  congr 1
  calc
    _ = baseGaussSign d * complexQuadraticChar d (a : ZMod d) ^ 2 *
        (phase d (-multiplierResidualExponent d a) * phase d (multiplierResidualExponent d a)) := by
      ring
    _ = _ := by rw [hc, hp]; ring

/-- Exact Lemma 2.14 under the sole remaining base Gauss-sign evaluation. -/
theorem multiplier_derived_of_baseGaussSign (hd : Odd d) (hGauss : baseGaussSign d = 1)
    (a : (ZMod d)ˣ) :
    (complexQuadraticChar d (a : ZMod d) *
      phase d ((-(a : ZMod d)^2 + 4*(a : ZMod d) - 2) * (8*(a : ZMod d))⁻¹)) •
        multiplierWord d a = multiplier d a := by
  rw [multiplier_derived_eq_baseGaussSign d hd, hGauss, one_smul]

end QuditClifford
