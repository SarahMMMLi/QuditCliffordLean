import QuditClifford.GaussEvaluation
import QuditClifford.FinitePhaseSums
import Mathlib.LinearAlgebra.Vandermonde

/-!
# The exact quadratic Gauss sign and Lemma 2.14

The determinant of the multiplier word at coefficient one reduces its universal
Gauss sign to the cube of the normalized Fourier determinant. We prove the latter
is exactly one via the Vandermonde determinant: each root difference splits into
an explicit exponential phase and a positive sine factor. The finite phase sums
cancel the paper's normalization in odd dimension, and unitarity fixes the
remaining positive amplitude to one. Thus the sign evaluation and the multiplier
construction are unconditional; no Gauss evaluation is introduced as an axiom.
-/

noncomputable section
namespace QuditClifford

open Matrix

variable (d : ℕ) [Fact d.Prime]

/-- At unit multiplier one, the multiplier word is the cubic Fourier/phase word. -/
theorem multiplierWord_one : multiplierWord d 1 = (S d * H d) ^ 3 := by
  simp only [multiplierWord, multiplierZCorrection, multiplierXCorrection,
    Units.val_one, inv_one, sub_self, zero_mul, clock_zero, shift_zero,
    Matrix.one_mul, phasePower_one]
  noncomm_ring

/-- Determinants isolate the universal Gauss sign without choosing it. -/
theorem baseGaussSign_eq_det_cubic (hd : Odd d) :
    baseGaussSign d = (Matrix.det (S d)) ^ 3 * (Matrix.det (H d)) ^ 3 := by
  have hs : baseGaussSign d ^ d = baseGaussSign d := by
    have hsquare := baseGaussSign_sq d hd
    obtain ⟨k, hk⟩ := hd
    calc
      _ = baseGaussSign d ^ (2 * k + 1) := congrArg (fun n => baseGaussSign d ^ n) hk
      _ = _ := by rw [pow_add, pow_mul, hsquare]; simp
  have h := congrArg Matrix.det (multiplierWord_eq d hd (1 : (ZMod d)ˣ))
  rw [multiplierWord_one, Matrix.det_pow, Matrix.det_mul, mul_pow,
    multiplierWordScalar_eq_baseGaussSign d hd, multiplier_one, Matrix.det_smul,
    Matrix.det_one, mul_one, ZMod.card, mul_pow, mul_pow, phase_pow_dimension,
    mul_one, hs] at h
  simpa [complexQuadraticChar] using h.symm

/-- Additive character evaluation of a finite sum. -/
theorem phase_finset_sum {α : Type*} (s : Finset α) (f : α → ZMod d) :
    phase d (∑ x ∈ s, f x) = ∏ x ∈ s, phase d (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

/-- The sum of all residues vanishes in an odd prime field. -/
theorem sum_residues_eq_zero (hd : Odd d) : ∑ x : ZMod d, x = 0 := by
  have hd2 : 2 < d := by
    have hp := (Fact.out : d.Prime).two_le
    have ho := Nat.odd_iff.mp hd
    omega
  simpa only [pow_one] using FiniteField.sum_pow_lt_card_sub_one (ZMod d) 1
    (by simpa only [ZMod.card] using (show 1 < d - 1 by omega))

/-- Cubing the phase-gate determinant removes the exceptional denominator three. -/
theorem det_S_cube (hd : Odd d) : Matrix.det (S d) ^ 3 = 1 := by
  have htwo : (2 : ZMod d) ≠ 0 := by
    intro h
    simpa [h] using two_mul_half d hd
  have hdouble (x : ZMod d) : quadratic d (2 * x) = 4 * quadratic d x + x := by
    have hh := two_mul_half d hd
    dsimp [quadratic]
    linear_combination x * hh
  have hsum := Equiv.sum_comp (Equiv.mulLeft₀ (2 : ZMod d) htwo) (quadratic d)
  change (∑ x : ZMod d, quadratic d (2 * x)) = ∑ x : ZMod d, quadratic d x at hsum
  simp only [hdouble, Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_residues_eq_zero d hd, add_zero] at hsum
  have hthree : 3 * ∑ x : ZMod d, quadratic d x = 0 := by linear_combination hsum
  rw [S, Matrix.det_diagonal, ← phase_finset_sum, ← phase_nsmul, nsmul_eq_mul]
  norm_num only [Nat.cast_ofNat]
  rw [hthree, phase_zero]

/-- Computing det(H) suffices to determine the classical Gauss sign. -/
theorem baseGaussSign_eq_det_H_cube (hd : Odd d) :
    baseGaussSign d = Matrix.det (H d) ^ 3 := by
  rw [baseGaussSign_eq_det_cubic d hd, det_S_cube d hd, one_mul]

/-- The remaining signed Gauss evaluation follows from the Fourier determinant. -/
theorem baseGaussSign_eq_one_of_det_H (hd : Odd d) (hdet : Matrix.det (H d) = 1) :
    baseGaussSign d = 1 := by
  rw [baseGaussSign_eq_det_H_cube d hd, hdet, one_pow]

/-- The residue equivalence agrees with the natural representative. -/
theorem finEquiv_eq_natCast (i : Fin d) : ZMod.finEquiv d i = (i.val : ZMod d) := by
  cases d with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    change i = (i.val : Fin (n + 1))
    apply Fin.ext
    simp [Nat.mod_eq_of_lt i.isLt]

/-- The unnormalized Fourier determinant is a Vandermonde product. -/
theorem det_fourierMatrix_vandermonde :
    Matrix.det (fourierMatrix d) =
      ∏ i : Fin d, ∏ j ∈ Finset.Ioi i, (phase d (j.val : ZMod d) - phase d (i.val : ZMod d)) := by
  rw [← Matrix.det_submatrix_equiv_self (ZMod.finEquiv d).toEquiv]
  have hm : (fourierMatrix d).submatrix (ZMod.finEquiv d) (ZMod.finEquiv d) =
      Matrix.vandermonde (fun i : Fin d => phase d (i.val : ZMod d)) := by
    ext i j
    simp only [Matrix.submatrix_apply, fourierMatrix, Matrix.vandermonde_apply,
      finEquiv_eq_natCast, ← phase_nsmul, nsmul_eq_mul]
    congr 1
    ring
  change Matrix.det ((fourierMatrix d).submatrix (ZMod.finEquiv d) (ZMod.finEquiv d)) = _
  rw [hm, Matrix.det_vandermonde]

/-- Difference of two points on the unit circle, with its positive sine factor exposed. -/
theorem exp_difference_sine (x y : ℝ) :
    Complex.exp (2 * y * Complex.I) - Complex.exp (2 * x * Complex.I) =
      Complex.exp (((x : ℂ) + y + Real.pi / 2) * Complex.I) *
        (2 * Real.sin (y - x) : ℝ) := by
  rw [show (((x : ℂ) + y + Real.pi / 2) * Complex.I) =
    ((x : ℂ) + y) * Complex.I + Real.pi / 2 * Complex.I by ring,
    Complex.exp_add, Complex.exp_pi_div_two_mul_I]
  push_cast
  rw [Complex.sin]
  have he₁ : ((x : ℂ) + y) * Complex.I + -((y : ℂ) - x) * Complex.I =
      2 * x * Complex.I := by ring
  have he₂ : ((x : ℂ) + y) * Complex.I + ((y : ℂ) - x) * Complex.I =
      2 * y * Complex.I := by ring
  calc
    _ = Complex.exp (((x : ℂ) + y) * Complex.I + ((y : ℂ) - x) * Complex.I) -
        Complex.exp (((x : ℂ) + y) * Complex.I + -((y : ℂ) - x) * Complex.I) := by
      rw [he₁, he₂]
    _ = _ := by
      rw [Complex.exp_add, Complex.exp_add]
      ring_nf
      simp [Complex.I_sq]
      ring

/-- Positive factors in the Vandermonde determinant, before Fourier normalization. -/
def fourierSineProduct : ℝ :=
  ∏ i : Fin d, ∏ j ∈ Finset.Ioi i, 2 * Real.sin (Real.pi / d * ((j.val : ℝ) - i.val))

/-- Each root difference has an explicit exponential phase and a positive real amplitude. -/
theorem phase_difference_sine (i j : Fin d) :
    phase d (j.val : ZMod d) - phase d (i.val : ZMod d) =
      Complex.exp (((Real.pi / d * ((i.val : ℝ) + j.val) + Real.pi / 2 : ℝ) : ℂ) * Complex.I) *
        ((2 * Real.sin (Real.pi / d * ((j.val : ℝ) - i.val)) : ℝ) : ℂ) := by
  have hp (k : Fin d) : phase d (k.val : ZMod d) =
      Complex.exp (2 * (Real.pi * k.val / d : ℝ) * Complex.I) := by
    have h := ZMod.stdAddChar_coe (N := d) (k.val : ℤ)
    simp only [Int.cast_natCast] at h
    rw [phase, h]
    congr 1
    push_cast
    ring
  rw [hp j, hp i, exp_difference_sine]
  congr 1
  · congr 1
    push_cast
    ring
  · congr 2
    ring_nf

/-- The sine amplitude of the Fourier determinant is strictly positive. -/
theorem fourierSineProduct_pos : 0 < fourierSineProduct d := by
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j hj
  have hij : (i.val : ℝ) < j.val := by exact_mod_cast Finset.mem_Ioi.mp hj
  have hjd : (j.val : ℝ) < d := by exact_mod_cast j.isLt
  have hi : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  apply mul_pos (by norm_num)
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact mul_pos (div_pos Real.pi_pos hd) (sub_pos.mpr hij)
  · have hdiff : (j.val : ℝ) - i.val < d := by linarith
    calc
      _ < Real.pi / d * d := mul_lt_mul_of_pos_left hdiff (div_pos Real.pi_pos hd)
      _ = Real.pi := div_mul_cancel₀ _ hd.ne'

/-- The complete determinant with phase and positive amplitude separated. -/
theorem det_fourierMatrix_phase_amplitude :
    Matrix.det (fourierMatrix d) =
      Complex.exp (((∑ i : Fin d, ∑ j ∈ Finset.Ioi i,
        (Real.pi / d * ((i.val : ℝ) + j.val) + Real.pi / 2)) : ℝ) * Complex.I) *
      (fourierSineProduct d : ℂ) := by
  rw [det_fourierMatrix_vandermonde]
  simp_rw [phase_difference_sine, Finset.prod_mul_distrib]
  congr 1
  · simp_rw [← Complex.exp_sum]
    congr 1
    push_cast
    simp only [Finset.sum_mul]
  · simp only [fourierSineProduct, Complex.ofReal_prod]

/-- Exact finite phase sum in the Fourier Vandermonde determinant. -/
theorem fourierVandermonde_phase_sum :
    (∑ i : Fin d, ∑ j ∈ Finset.Ioi i,
      (Real.pi / d * ((i.val : ℝ) + j.val) + Real.pi / 2)) =
      Real.pi * ((d : ℝ) - 1)^2 / 2 + Real.pi * d * ((d : ℝ) - 1) / 4 := by
  have hfactor : (∑ i : Fin d, ∑ j ∈ Finset.Ioi i,
      (Real.pi / d * ((i.val : ℝ) + j.val) + Real.pi / 2)) =
      Real.pi / d * (∑ i : Fin d, ∑ j ∈ Finset.Ioi i, ((i.val : ℝ) + j.val)) +
      Real.pi / 2 * (∑ i : Fin d, ∑ j ∈ Finset.Ioi i, (1 : ℝ)) := by
    simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_one, mul_add]
  rw [hfactor, sum_Ioi_one_real, sum_Ioi_indices_real]
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  field_simp [hd0]
  ring

/-- Fourier normalization leaves a positive real amplitude and a single explicit phase. -/
theorem det_H_phase_amplitude :
    Matrix.det (H d) =
      Complex.exp (((Real.pi * ((d : ℝ) - 1)^2 / 2 : ℝ) : ℂ) * Complex.I) *
        ((fourierSineProduct d / (Real.sqrt d)^d : ℝ) : ℂ) := by
  rw [H, Matrix.det_smul, ZMod.card, det_fourierMatrix_phase_amplitude,
    fourierVandermonde_phase_sum]
  simp only [_root_.mul_inv_rev, mul_pow]
  calc
    _ = ((lambda d)⁻¹)^d *
        Complex.exp (((Real.pi * ((d : ℝ) - 1)^2 / 2 +
          Real.pi * d * ((d : ℝ) - 1) / 4 : ℝ) : ℂ) * Complex.I) *
        (((Real.sqrt d : ℂ)⁻¹)^d * (fourierSineProduct d : ℂ)) := by ring
    _ = _ := by
      rw [lambda, ← Complex.exp_neg, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      · congr 1
        push_cast
        ring
      · push_cast
        simp only [div_eq_mul_inv, inv_pow]
        ring

omit [Fact d.Prime] in
/-- In odd dimension the residual Vandermonde phase is exactly one. -/
theorem fourierVandermonde_phase_eq_one (hd : Odd d) :
    Complex.exp (((Real.pi * ((d : ℝ) - 1)^2 / 2 : ℝ) : ℂ) * Complex.I) = 1 := by
  obtain ⟨k, hk⟩ := hd
  have he : (((Real.pi * ((d : ℝ) - 1)^2 / 2 : ℝ) : ℂ) * Complex.I) =
      (k^2 : ℕ) * (2 * Real.pi * Complex.I) := by
    rw [hk]
    push_cast
    ring
  rw [he, Complex.exp_nat_mul_two_pi_mul_I]

/-- The normalized Fourier determinant is strictly positive real in odd dimension. -/
theorem det_H_eq_positive_amplitude (hd : Odd d) :
    Matrix.det (H d) = ((fourierSineProduct d / (Real.sqrt d)^d : ℝ) : ℂ) := by
  rw [det_H_phase_amplitude, fourierVandermonde_phase_eq_one d hd, one_mul]

/-- Lemma A.9: the paper's normalized Fourier gate has determinant exactly one. -/
theorem det_H_eq_one (hd : Odd d) : Matrix.det (H d) = 1 := by
  let r : ℝ := fourierSineProduct d / (Real.sqrt d)^d
  have hr : 0 < r := div_pos (fourierSineProduct_pos d)
    (pow_pos (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (NeZero.pos d))) _)
  have hu := (Matrix.mem_unitaryGroup_iff').mp (H_unitary d)
  change (H d)ᴴ * H d = 1 at hu
  have hdet := congrArg Matrix.det hu
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one,
    det_H_eq_positive_amplitude d hd] at hdet
  change star (r : ℂ) * (r : ℂ) = 1 at hdet
  simp only [Complex.star_def, Complex.conj_ofReal] at hdet
  have hr2 : r * r = 1 := by exact_mod_cast hdet
  have hr1 : r = 1 := by nlinarith
  rw [det_H_eq_positive_amplitude d hd]
  change (r : ℂ) = 1
  rw [hr1]
  norm_num

/-- The classical Gauss sign has the positive value required by Figure 1. -/
theorem baseGaussSign_eq_one (hd : Odd d) : baseGaussSign d = 1 :=
  baseGaussSign_eq_one_of_det_H d hd (det_H_eq_one d hd)

/-- Exact signed evaluation of the homogeneous base Gauss sum. -/
theorem squareGaussSum_half (hd : Odd d) :
    squareGaussSum d (half d) = (lambda d)⁻¹ * (Real.sqrt d : ℂ) := by
  have h := baseGaussSign_eq_one d hd
  rw [baseGaussSign, div_eq_one_iff_eq] at h
  · rw [← h, ← mul_assoc, inv_mul_cancel₀ (lambda_ne_zero d), one_mul]
  · exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (NeZero.pos d)))

/-- Lemma 2.14, with its exact signed scalar, holds without a Gauss-sum hypothesis. -/
theorem multiplier_derived (hd : Odd d) (a : (ZMod d)ˣ) :
    (complexQuadraticChar d (a : ZMod d) *
      phase d ((-(a : ZMod d)^2 + 4*(a : ZMod d) - 2) * (8*(a : ZMod d))⁻¹)) •
        multiplierWord d a = multiplier d a :=
  multiplier_derived_of_baseGaussSign d hd (baseGaussSign_eq_one d hd) a

/-- The signed closed form of the quadratic sum in the paper's phase convention. -/
theorem quadraticGaussSum_eval (hd : Odd d) (a : (ZMod d)ˣ) :
    quadraticGaussSum d (a : ZMod d) =
      phase d (-(a : ZMod d) * half d ^ 3) * complexQuadraticChar d (a : ZMod d) *
        (lambda d)⁻¹ * (Real.sqrt d : ℂ) := by
  have hh : half d ≠ 0 := by
    intro h
    simpa [h] using two_mul_half d hd
  rw [quadraticGaussSum_eq_squareGaussSum d hd, squareGaussSum_mul d hd a _ hh,
    squareGaussSum_half d hd]
  ring

/-- The exact scalar of the multiplier word, now with the Gauss sign evaluated. -/
theorem multiplierWordScalar_eval (hd : Odd d) (a : (ZMod d)ˣ) :
    multiplierWordScalar d a = complexQuadraticChar d (a : ZMod d) *
      phase d (multiplierResidualExponent d a) := by
  rw [multiplierWordScalar_eq_baseGaussSign d hd, baseGaussSign_eq_one d hd, one_mul]

end QuditClifford
