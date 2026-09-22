import QuditClifford.Relations

/-!
# The multiplier circuit and its finite Gaussian scalar

These proofs keep the finite Gauss sum explicit. Its evaluation with the exact
Legendre-symbol sign is a separate number-theoretic obligation for Lemma 2.14;
no unevaluated sum is identified with that claimed sign by definition.
-/

noncomputable section
namespace QuditClifford

open Matrix

variable (d : ℕ) [NeZero d]

/-- The quadratic Gauss sum for the paper's phase-gate convention. -/
def quadraticGaussSum (a : ZMod d) : ℂ := ∑ x : ZMod d, phase d (a * quadratic d x)

/-- Completion of the square, keeping the finite sum's value unevaluated. -/
theorem quadraticGaussSum_linear (hd : Odd d) (a : (ZMod d)ˣ) (b : ZMod d) :
    (∑ x : ZMod d, phase d ((a : ZMod d) * quadratic d x + b * x)) =
      phase d (-((a : ZMod d) * quadratic d ((↑a⁻¹ : ZMod d) * b))) *
        quadraticGaussSum d (a : ZMod d) := by
  have ha : (a : ZMod d) * (↑a⁻¹ : ZMod d) = 1 := by simp
  have hexp (x : ZMod d) :
      (a : ZMod d) * quadratic d x + b * x =
        -((a : ZMod d) * quadratic d ((↑a⁻¹ : ZMod d) * b)) +
          (a : ZMod d) * quadratic d (x + (↑a⁻¹ : ZMod d) * b) := by
    rw [quadratic_add d hd]
    linear_combination -b * x * ha
  simp_rw [hexp, phase_add]
  rw [← Finset.mul_sum]
  congr 1
  exact Equiv.sum_comp (Equiv.addRight ((↑a⁻¹ : ZMod d) * b)) (fun x => phase d ((a : ZMod d) * quadratic d x))

/-- The exact matrix kernel of a Fourier/phase/Fourier sandwich. -/
theorem fourier_phase_fourier_apply (hd : Odd d) (a : (ZMod d)ˣ) (i j : ZMod d) :
    (fourierMatrix d * phasePower d (a : ZMod d) * fourierMatrix d) i j =
      phase d (-((a : ZMod d) * quadratic d ((↑a⁻¹ : ZMod d) * (i + j)))) *
        quadraticGaussSum d (a : ZMod d) := by
  rw [Matrix.mul_apply]
  simp only [phasePower, Matrix.mul_diagonal, fourierMatrix]
  have hexp (k : ZMod d) :
      phase d (i * k) * phase d ((a : ZMod d) * quadratic d k) * phase d (k * j) =
        phase d ((a : ZMod d) * quadratic d k + (i + j) * k) := by
    rw [← phase_add, ← phase_add]
    congr 1
    ring
  simp only [hexp]
  exact quadraticGaussSum_linear d hd a (i + j)

theorem phasePower_mul_apply (a : ZMod d) (M : QuditMatrix d) (i j : ZMod d) :
    (phasePower d a * M) i j = phase d (a * quadratic d i) * M i j := by
  simp [phasePower, Matrix.diagonal_mul]

theorem mul_phasePower_apply (M : QuditMatrix d) (a : ZMod d) (i j : ZMod d) :
    (M * phasePower d a) i j = M i j * phase d (a * quadratic d j) := by
  simp [phasePower, Matrix.mul_diagonal]

/-- The three-Fourier word before the final Pauli correction and normalization. -/
def unnormalizedMultiplierWord (a : (ZMod d)ˣ) : QuditMatrix d :=
  phasePower d (↑a⁻¹ : ZMod d) *
    (fourierMatrix d * phasePower d (a : ZMod d) * fourierMatrix d) *
      phasePower d (↑a⁻¹ : ZMod d) * fourierMatrix d

/-- The rank-one quadratic path sum reduces to one character-orthogonality test. -/
theorem unnormalizedMultiplierWord_apply (hd : Odd d) (a : (ZMod d)ˣ) (i j : ZMod d) :
    unnormalizedMultiplierWord d a i j =
      phase d ((1 - (↑a⁻¹ : ZMod d)) * half d * i) * quadraticGaussSum d (a : ZMod d) *
        (if j - (↑a⁻¹ : ZMod d) * i + (1 - (↑a⁻¹ : ZMod d)) * half d = 0
          then (d : ℂ) else 0) := by
  rw [unnormalizedMultiplierWord, Matrix.mul_apply]
  simp only [mul_phasePower_apply, phasePower_mul_apply,
    fourier_phase_fourier_apply d hd, fourierMatrix]
  have hh := two_mul_half d hd
  have ha : (a : ZMod d) * (↑a⁻¹ : ZMod d) = 1 := by simp
  have hexp (k : ZMod d) :
      (↑a⁻¹ : ZMod d) * quadratic d i -
          (a : ZMod d) * quadratic d ((↑a⁻¹ : ZMod d) * (i + k)) +
          (↑a⁻¹ : ZMod d) * quadratic d k + k * j =
        (1 - (↑a⁻¹ : ZMod d)) * half d * i +
          (j - (↑a⁻¹ : ZMod d) * i + (1 - (↑a⁻¹ : ZMod d)) * half d) * k := by
    dsimp [quadratic]
    linear_combination
      (-(↑a⁻¹ : ZMod d) * half d * (i + k) ^ 2 + half d * (i + k)) * ha +
        (-(↑a⁻¹ : ZMod d) * i * k) * hh
  have hterm (k : ZMod d) :
      phase d ((↑a⁻¹ : ZMod d) * quadratic d i) *
          (phase d (-((a : ZMod d) * quadratic d ((↑a⁻¹ : ZMod d) * (i + k)))) *
            quadraticGaussSum d (a : ZMod d)) *
          phase d ((↑a⁻¹ : ZMod d) * quadratic d k) * phase d (k * j) =
        (phase d ((1 - (↑a⁻¹ : ZMod d)) * half d * i) * quadraticGaussSum d (a : ZMod d)) *
          phase d ((j - (↑a⁻¹ : ZMod d) * i + (1 - (↑a⁻¹ : ZMod d)) * half d) * k) := by
    calc
      _ = phase d ((↑a⁻¹ : ZMod d) * quadratic d i -
          (a : ZMod d) * quadratic d ((↑a⁻¹ : ZMod d) * (i + k)) +
          (↑a⁻¹ : ZMod d) * quadratic d k + k * j) * quadraticGaussSum d (a : ZMod d) := by
        simp only [sub_eq_add_neg, phase_add]
        ring
      _ = _ := by rw [hexp, phase_add]; ring
  simp only [hterm]
  rw [← Finset.mul_sum, phase_sum]

/-- The X correction in the multiplier circuit of Lemma 2.14. -/
def multiplierXCorrection (a : (ZMod d)ˣ) : ZMod d := (1 - (a : ZMod d)) * half d

/-- The Z correction in the multiplier circuit of Lemma 2.14. -/
def multiplierZCorrection (a : (ZMod d)ˣ) : ZMod d :=
  (1 - (a : ZMod d)) * half d * (↑a⁻¹ : ZMod d)

/-- Corrected word with each H replaced by its unnormalized Fourier kernel. -/
def correctedUnnormalizedMultiplierWord (a : (ZMod d)ˣ) : QuditMatrix d :=
  clock d (multiplierZCorrection d a) *
    (shift d (multiplierXCorrection d a) * unnormalizedMultiplierWord d a)

/-- The exact scalar remaining after the Pauli correction, before H normalization. -/
def unnormalizedMultiplierScalar (a : (ZMod d)ˣ) : ℂ :=
  phase d (-((1 - (↑a⁻¹ : ZMod d)) * half d * multiplierXCorrection d a)) *
    quadraticGaussSum d (a : ZMod d) * (d : ℂ)

/-- The corrected Fourier word is exactly a scalar times the raw multiplier. -/
theorem correctedUnnormalizedMultiplierWord_eq (hd : Odd d) (a : (ZMod d)ˣ) :
    correctedUnnormalizedMultiplierWord d a = unnormalizedMultiplierScalar d a • multiplier d a := by
  ext i j
  rw [correctedUnnormalizedMultiplierWord, clock, Matrix.diagonal_mul, shift_mul_apply,
    unnormalizedMultiplierWord_apply d hd]
  simp only [unnormalizedMultiplierScalar, Matrix.smul_apply, smul_eq_mul, multiplier, basisMap]
  have ha : (a : ZMod d) * (↑a⁻¹ : ZMod d) = 1 := by simp
  have hcancel : (↑a⁻¹ : ZMod d) * multiplierXCorrection d a +
      (1 - (↑a⁻¹ : ZMod d)) * half d = 0 := by
    dsimp [multiplierXCorrection]
    linear_combination -half d * ha
  have hexp : j - (↑a⁻¹ : ZMod d) * (i - multiplierXCorrection d a) +
      (1 - (↑a⁻¹ : ZMod d)) * half d = j - (↑a⁻¹ : ZMod d) * i := by
    linear_combination hcancel
  have hiff : j - (↑a⁻¹ : ZMod d) * i = 0 ↔ i = (a : ZMod d) * j := by
    rw [sub_eq_zero]
    constructor
    · intro h
      rw [h, ← mul_assoc, ha, one_mul]
    · intro h
      simp [h, ← mul_assoc]
  simp only [hexp, hiff]
  split_ifs
  · simp only [mul_one]
    have hphase : multiplierZCorrection d a * i +
        (1 - (↑a⁻¹ : ZMod d)) * half d * (i - multiplierXCorrection d a) =
        -((1 - (↑a⁻¹ : ZMod d)) * half d * multiplierXCorrection d a) := by
      dsimp [multiplierZCorrection]
      linear_combination -half d * i * ha
    calc
      _ = (phase d (multiplierZCorrection d a * i) *
          phase d ((1 - (↑a⁻¹ : ZMod d)) * half d * (i - multiplierXCorrection d a))) *
          quadraticGaussSum d (a : ZMod d) * (d : ℂ) := by ring
      _ = _ := by rw [← phase_add, hphase]
  · simp

/-- The multiplier word of Lemma 2.14 before its displayed scalar correction.
All factors are exact complex matrices; no projectivization is used. -/
def multiplierWord (a : (ZMod d)ˣ) : QuditMatrix d :=
  clock d (multiplierZCorrection d a) *
    (shift d (multiplierXCorrection d a) *
      (phasePower d (↑a⁻¹ : ZMod d) *
        (H d * phasePower d (a : ZMod d) * H d) *
          phasePower d (↑a⁻¹ : ZMod d) * H d))

/-- The finite Gauss-sum expression for the exact remaining scalar. -/
def multiplierWordScalar (a : (ZMod d)ˣ) : ℂ :=
  ((lambda d * (Real.sqrt d : ℂ))⁻¹) ^ 3 * unnormalizedMultiplierScalar d a

/-- Complete matrix evaluation of the multiplier circuit, with its scalar expressed
as a finite Gauss sum. Evaluating that sum with its signed Legendre factor is
still required to recover the paper's closed-form scalar in Lemma 2.14. -/
theorem multiplierWord_eq (hd : Odd d) (a : (ZMod d)ˣ) :
    multiplierWord d a = multiplierWordScalar d a • multiplier d a := by
  have hword : multiplierWord d a = ((lambda d * (Real.sqrt d : ℂ))⁻¹) ^ 3 •
      correctedUnnormalizedMultiplierWord d a := by
    simp only [multiplierWord, H, correctedUnnormalizedMultiplierWord, unnormalizedMultiplierWord,
      Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    congr 1
    ring
  rw [hword, correctedUnnormalizedMultiplierWord_eq d hd, smul_smul]
  rfl

end QuditClifford
