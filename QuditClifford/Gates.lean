import QuditClifford.RootOfUnity
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.UnitaryGroup

/-! # Exact matrices for qudit gates

Matrices are indexed by `ZMod d`, with output indices first.  Thus `A * B`
means first apply `B`, then `A`, as in Section 2.2 of the paper.
-/

noncomputable section
namespace QuditClifford

open Matrix

/-- Matrix of a map on the computational basis. -/
def basisMap {α : Type*} [DecidableEq α] (f : α → α) : Matrix α α ℂ :=
  fun i j ↦ if i = f j then 1 else 0

@[simp] theorem basisMap_id {α : Type*} [DecidableEq α] :
    basisMap (id : α → α) = 1 := by
  ext i j
  simp [basisMap, Matrix.one_apply]

@[simp] theorem basisMap_mul {α : Type*} [Fintype α] [DecidableEq α]
    (f g : α → α) : basisMap f * basisMap g = basisMap (f ∘ g) := by
  ext i j
  simp [Matrix.mul_apply, basisMap, mul_ite]

variable (d : ℕ) [NeZero d]

abbrev QuditMatrix := Matrix (ZMod d) (ZMod d) ℂ

/-- Translation `|j⟩ ↦ |j+a⟩`. -/
def shift (a : ZMod d) : QuditMatrix d := basisMap (fun j ↦ j + a)

/-- Clock power `|j⟩ ↦ ω^(bj)|j⟩`. -/
def clock (b : ZMod d) : QuditMatrix d := Matrix.diagonal (fun j ↦ phase d (b * j))

/-- The Pauli shift of Definition 2.8. -/
def X : QuditMatrix d := shift d 1

/-- The Pauli clock of Definition 2.8. -/
def Z : QuditMatrix d := clock d 1

omit [NeZero d] in
@[simp] theorem shift_zero : shift d 0 = 1 := by
  simp only [shift, add_zero]
  exact basisMap_id

@[simp] theorem shift_add (a b : ZMod d) : shift d (a + b) = shift d a * shift d b := by
  simp only [shift, basisMap_mul]
  apply congrArg basisMap
  funext j
  change j + (a + b) = (j + b) + a
  ring

@[simp] theorem clock_zero : clock d 0 = 1 := by simp [clock]

@[simp] theorem clock_add (a b : ZMod d) : clock d (a + b) = clock d a * clock d b := by
  simp [clock, ← Matrix.diagonal_mul_diagonal, add_mul]

theorem shift_pow (a : ZMod d) (n : ℕ) : shift d a ^ n = shift d (n • a) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, ← shift_add, succ_nsmul]

theorem clock_pow (a : ZMod d) (n : ℕ) : clock d a ^ n = clock d (n • a) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, ← clock_add, succ_nsmul]

@[simp] theorem X_pow_dimension : X d ^ d = 1 := by simp [X, shift_pow, nsmul_eq_mul]

@[simp] theorem Z_pow_dimension : Z d ^ d = 1 := by simp [Z, clock_pow, nsmul_eq_mul]

/-- Exact Weyl commutation, retaining the phase. -/
theorem clock_shift (a b : ZMod d) :
    clock d b * shift d a = phase d (b * a) • (shift d a * clock d b) := by
  ext i j
  simp only [clock, Matrix.diagonal_mul, Matrix.mul_diagonal, shift, basisMap,
    Matrix.smul_apply, smul_eq_mul]
  split_ifs with h
  · subst i
    simp [mul_add, mul_comm]
  · simp

/-- Equation (7), as exact matrix equality. -/
theorem ZX_eq_omega_XZ : Z d * X d = omega d • (X d * Z d) := by
  simpa [X, Z, omega] using clock_shift d 1 1

/-- X and Z do not commute exactly when the dimension exceeds one. -/
theorem ZX_ne_XZ (hd : 1 < d) : Z d * X d ≠ X d * Z d := by
  intro h
  have hentry := congrArg (fun A : QuditMatrix d ↦ A 1 0) h
  apply omega_ne_one d hd
  simpa [Z, X, clock, shift, basisMap, Matrix.diagonal_mul, Matrix.mul_diagonal, omega] using hentry

/-- The raw multiplier of Definition 2.13: no hidden Legendre-symbol scalar. -/
def multiplier (a : (ZMod d)ˣ) : QuditMatrix d := basisMap (fun j ↦ (a : ZMod d) * j)

omit [NeZero d] in
@[simp] theorem multiplier_one : multiplier d 1 = 1 := by
  simp only [multiplier, Units.val_one, one_mul]
  exact basisMap_id

@[simp] theorem multiplier_mul (a b : (ZMod d)ˣ) :
    multiplier d (a * b) = multiplier d a * multiplier d b := by
  simp only [multiplier, basisMap_mul, Units.val_mul]
  apply congrArg basisMap
  funext j
  simp [Function.comp_apply, mul_assoc]

@[simp] theorem multiplier_mul_inv (a : (ZMod d)ˣ) :
    multiplier d a * multiplier d a⁻¹ = 1 := by rw [← multiplier_mul]; simp

@[simp] theorem multiplier_inv_mul (a : (ZMod d)ˣ) :
    multiplier d a⁻¹ * multiplier d a = 1 := by rw [← multiplier_mul]; simp

theorem multiplier_pow (a : (ZMod d)ˣ) (n : ℕ) :
    multiplier d a ^ n = multiplier d (a ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, ← multiplier_mul, pow_succ]

/-- Multiplier action on X powers, stated as a pushing equation. -/
theorem multiplier_shift (a : (ZMod d)ˣ) (b : ZMod d) :
    multiplier d a * shift d b = shift d ((a : ZMod d) * b) * multiplier d a := by
  simp only [multiplier, shift, basisMap_mul]
  apply congrArg basisMap
  funext j
  change (a : ZMod d) * (j + b) = (a : ZMod d) * j + (a : ZMod d) * b
  ring

/-- Multiplier action on Z powers, stated as a pushing equation. -/
theorem clock_multiplier (a : (ZMod d)ˣ) (b : ZMod d) :
    clock d b * multiplier d a = multiplier d a * clock d (b * (a : ZMod d)) := by
  ext i j
  simp only [clock, Matrix.diagonal_mul, Matrix.mul_diagonal, multiplier, basisMap]
  split_ifs with h
  · subst i; simp [mul_assoc]
  · simp

/-- The inverse of two modulo an odd dimension. -/
def half : ZMod d := (2 : ZMod d)⁻¹

omit [NeZero d] in
theorem two_mul_half (hd : Odd d) : (2 : ZMod d) * half d = 1 := by
  exact ZMod.coe_mul_inv_eq_one 2 (Nat.coprime_two_left.mpr hd)

/-- The quadratic exponent of the paper, `j(j-1)/2`. -/
def quadratic (j : ZMod d) : ZMod d := j * (j - 1) * half d

omit [NeZero d] in
theorem quadratic_add_one (hd : Odd d) (j : ZMod d) :
    quadratic d (j + 1) = quadratic d j + j := by
  have hh := two_mul_half d hd
  dsimp [quadratic]
  calc
    (j + 1) * (j + 1 - 1) * half d = j * (j - 1) * half d + j * (2 * half d) := by ring
    _ = j * (j - 1) * half d + j := by rw [hh, mul_one]

/-- The phase gate of Definition 2.10. Its Clifford relation below requires odd dimension. -/
def S : QuditMatrix d := Matrix.diagonal (fun j ↦ phase d (quadratic d j))

@[simp] theorem S_pow_dimension : S d ^ d = 1 := by
  ext i j
  simp [S, Matrix.diagonal_pow, Matrix.diagonal_apply, Matrix.one_apply, Pi.pow_apply]

/-- The S-X pushing relation in Lemma 2.23. -/
theorem SX_eq_XZS (hd : Odd d) : S d * X d = (X d * Z d) * S d := by
  ext i j
  simp only [S, X, Z, clock, shift, Matrix.diagonal_mul, Matrix.mul_diagonal, basisMap]
  split_ifs with h
  · subst i
    simp [quadratic_add_one d hd, mul_comm]
  · simp

/-- The S-Z pushing relation in Lemma 2.23. -/
theorem SZ_eq_ZS : S d * Z d = Z d * S d := by
  ext i j
  by_cases h : i = j
  · subst i; simp [S, Z, clock, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply, mul_comm]
  · simp [S, Z, clock, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply, h]

abbrev TwoQuditMatrix := Matrix (ZMod d × ZMod d) (ZMod d × ZMod d) ℂ

/-- The controlled-Z gate of Definition 2.10. -/
def CZ : TwoQuditMatrix d := Matrix.diagonal (fun j ↦ phase d (j.1 * j.2))

@[simp] theorem CZ_pow_dimension : CZ d ^ d = 1 := by
  ext i j
  simp [CZ, Matrix.diagonal_pow, Matrix.diagonal_apply, Matrix.one_apply, Pi.pow_apply]

/-- Pauli X on the first wire. -/
def X₁ : TwoQuditMatrix d := basisMap (fun j ↦ (j.1 + 1, j.2))
/-- Pauli X on the second wire. -/
def X₂ : TwoQuditMatrix d := basisMap (fun j ↦ (j.1, j.2 + 1))
/-- Pauli Z on the first wire. -/
def Z₁ : TwoQuditMatrix d := Matrix.diagonal (fun j ↦ phase d j.1)
/-- Pauli Z on the second wire. -/
def Z₂ : TwoQuditMatrix d := Matrix.diagonal (fun j ↦ phase d j.2)

theorem CZ_X₁ : CZ d * X₁ d = (X₁ d * Z₂ d) * CZ d := by
  ext i j
  simp only [CZ, X₁, Z₂, Matrix.diagonal_mul, Matrix.mul_diagonal, basisMap]
  split_ifs with h
  · subst i; simp [add_mul, mul_add, mul_comm]
  · simp

theorem CZ_X₂ : CZ d * X₂ d = (Z₁ d * X₂ d) * CZ d := by
  ext i j
  simp only [CZ, X₂, Z₁, Matrix.diagonal_mul, Matrix.mul_diagonal, basisMap]
  split_ifs with h
  · subst i; simp [mul_add, mul_comm]
  · simp

theorem CZ_Z₁ : CZ d * Z₁ d = Z₁ d * CZ d := by
  ext i j
  by_cases h : i = j
  · subst i; simp [CZ, Z₁, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply, mul_comm]
  · simp [CZ, Z₁, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply, h]

theorem CZ_Z₂ : CZ d * Z₂ d = Z₂ d * CZ d := by
  ext i j
  by_cases h : i = j
  · subst i; simp [CZ, Z₂, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply, mul_comm]
  · simp [CZ, Z₂, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply, h]

/-- The unnormalised Fourier matrix with the paper's positive exponent. -/
def fourierMatrix : QuditMatrix d := fun i j ↦ phase d (i * j)

/-- Exact Fourier inversion; no primality is required. -/
theorem fourierMatrix_sq :
    fourierMatrix d * fourierMatrix d = (d : ℂ) • basisMap (fun j : ZMod d ↦ -j) := by
  ext i j
  simp only [fourierMatrix, Matrix.mul_apply]
  have hexp (k : ZMod d) : phase d (i * k) * phase d (k * j) = phase d ((i + j) * k) := by
    rw [← phase_add]
    congr 1
    ring
  simp only [hexp, phase_sum, Matrix.smul_apply, smul_eq_mul, basisMap]
  simp only [add_eq_zero_iff_eq_neg]
  split_ifs <;> simp

/-- Fourier orthogonality, with the complex adjoint. -/
theorem fourierMatrix_adjoint_mul :
    (fourierMatrix d)ᴴ * fourierMatrix d = (d : ℂ) • (1 : QuditMatrix d) := by
  ext i j
  simp only [fourierMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply, phase_star]
  have hexp (k : ZMod d) : phase d (-(k * i)) * phase d (k * j) = phase d ((j - i) * k) := by
    rw [← phase_add]
    congr 1
    ring
  simp only [hexp, phase_sum, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, sub_eq_zero]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

/-- The phase in Definition 2.4, with the subtraction taken in the complex numbers. -/
def lambda : ℂ := Complex.exp (((d : ℂ) - 1) * Real.pi * Complex.I / 4)

/-- Exactly the Hadamard matrix of Definition 2.10. -/
def H : QuditMatrix d := (lambda d * (Real.sqrt d : ℂ))⁻¹ • fourierMatrix d

/-- Normalisation only changes the scalar in the Fourier-square identity. -/
theorem H_sq :
    H d * H d = (lambda d)⁻¹ ^ 2 • basisMap (fun j : ZMod d ↦ -j) := by
  have hs : (Real.sqrt d : ℂ) ^ 2 = (d : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg d)
  have hdn : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  rw [H, Matrix.smul_mul, Matrix.mul_smul, fourierMatrix_sq, smul_smul, smul_smul]
  congr 1
  rw [← sq, inv_pow, mul_pow, hs, _root_.mul_inv_rev]
  rw [mul_right_comm, inv_mul_cancel₀ hdn, one_mul, inv_pow]

/-- The positive Fourier kernel pushes X to Z. -/
theorem fourierMatrix_X : fourierMatrix d * X d = Z d * fourierMatrix d := by
  ext i j
  simp only [Z, clock, Matrix.diagonal_mul]
  simp [fourierMatrix, X, shift, Matrix.mul_apply, basisMap, mul_ite, mul_add, mul_comm]

theorem HX_eq_ZH : H d * X d = Z d * H d := by
  rw [H, Matrix.smul_mul, Matrix.mul_smul, fourierMatrix_X]

theorem shift_mul_apply (a : ZMod d) (M : QuditMatrix d) (i j : ZMod d) :
    (shift d a * M) i j = M (i - a) j := by
  simp [Matrix.mul_apply, shift, basisMap, ite_mul, ← sub_eq_iff_eq_add]

/-- The positive Fourier kernel pushes Z to the inverse X. -/
theorem fourierMatrix_Z : fourierMatrix d * Z d = shift d (-1) * fourierMatrix d := by
  ext i j
  simp only [Z, clock, Matrix.mul_diagonal, shift_mul_apply, fourierMatrix]
  simp [sub_neg_eq_add, add_mul, mul_add, mul_comm]

theorem HZ_eq_XinvH : H d * Z d = shift d (-1) * H d := by
  rw [H, Matrix.smul_mul, Matrix.mul_smul, fourierMatrix_Z]

/-- Squaring the normalising phase gives the sign appearing in Figure 1 (C2). -/
theorem lambda_sq (hd : Odd d) : lambda d ^ 2 = (-1 : ℂ) ^ ((d - 1) / 2) := by
  obtain ⟨k, rfl⟩ := hd
  simp only [lambda, Nat.add_sub_cancel]
  rw [← Complex.exp_nat_mul, ← Complex.exp_pi_mul_I, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  simp
  ring

theorem lambda_inv_sq (hd : Odd d) : (lambda d)⁻¹ ^ 2 = (-1 : ℂ) ^ ((d - 1) / 2) := by
  rw [inv_pow, lambda_sq d hd, ← inv_pow]
  norm_num

/-- Figure 1 (C2), with its exact sign and the raw negation matrix. -/
theorem H_sq_exact (hd : Odd d) :
    H d * H d = (-1 : ℂ) ^ ((d - 1) / 2) • basisMap (fun j : ZMod d ↦ -j) := by
  rw [H_sq, lambda_inv_sq d hd]

/-- A permutation matrix has the inverse permutation as its adjoint. -/
theorem basisMap_adjoint {α : Type*} [DecidableEq α] (e : α ≃ α) :
    (basisMap e)ᴴ = basisMap e.symm := by
  ext i j
  simp [Matrix.conjTranspose_apply, basisMap, e.eq_symm_apply, eq_comm]

/-- Every permutation matrix is unitary. -/
theorem basisMap_unitary {α : Type*} [Fintype α] [DecidableEq α] (e : α ≃ α) :
    basisMap e ∈ Matrix.unitaryGroup α ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change (basisMap e)ᴴ * basisMap e = 1
  rw [basisMap_adjoint, basisMap_mul]
  have hf : (e.symm ∘ e : α → α) = id := by
    funext a
    exact e.symm_apply_apply a
  rw [hf, basisMap_id]

/-- Every diagonal made from the canonical character is unitary. -/
theorem phase_diagonal_unitary {α : Type*} [Fintype α] [DecidableEq α] (f : α → ZMod d) :
    Matrix.diagonal (fun j ↦ phase d (f j)) ∈ Matrix.unitaryGroup α ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change (Matrix.diagonal _)ᴴ * Matrix.diagonal _ = 1
  ext i j
  by_cases hij : i = j
  · subst i
    simp [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_apply, Matrix.one_apply, phase_star]
  · simp [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_apply, Matrix.one_apply, hij]

theorem X_unitary : X d ∈ Matrix.unitaryGroup (ZMod d) ℂ :=
  basisMap_unitary (Equiv.addRight 1)

theorem Z_unitary : Z d ∈ Matrix.unitaryGroup (ZMod d) ℂ :=
  phase_diagonal_unitary d (fun j ↦ 1 * j)

theorem S_unitary : S d ∈ Matrix.unitaryGroup (ZMod d) ℂ :=
  phase_diagonal_unitary d (quadratic d)

theorem CZ_unitary : CZ d ∈ Matrix.unitaryGroup (ZMod d × ZMod d) ℂ :=
  phase_diagonal_unitary d (fun j : ZMod d × ZMod d ↦ j.1 * j.2)

omit [NeZero d] in
theorem lambda_ne_zero : lambda d ≠ 0 := Complex.exp_ne_zero _

omit [NeZero d] in
theorem lambda_star_mul : star (lambda d) * lambda d = 1 := by
  simp only [lambda, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  convert Complex.exp_zero using 1
  congr 1
  apply Complex.ext
  · simp [Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]
  · simp [Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]
    ring

theorem H_unitary : H d ∈ Matrix.unitaryGroup (ZMod d) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change (H d)ᴴ * H d = 1
  have hs : (Real.sqrt d : ℂ) * (Real.sqrt d : ℂ) = (d : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg d)
  have hdn : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  rw [H, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    fourierMatrix_adjoint_mul, smul_smul, smul_smul]
  have hc : star ((lambda d * (Real.sqrt d : ℂ))⁻¹) *
      (lambda d * (Real.sqrt d : ℂ))⁻¹ * (d : ℂ) = 1 := by
    simp only [star_inv₀, StarMul.star_mul]
    rw [← _root_.mul_inv_rev]
    have ht : lambda d * (Real.sqrt d : ℂ) *
        (star (Real.sqrt d : ℂ) * star (lambda d)) = (d : ℂ) := by
      rw [Complex.star_def, Complex.conj_ofReal]
      calc
        lambda d * ↑√↑d * (↑√↑d * star (lambda d)) =
            (star (lambda d) * lambda d) * (↑√↑d * ↑√↑d) := by ring
        _ = (d : ℂ) := by rw [lambda_star_mul, one_mul, hs]
    rw [ht, inv_mul_cancel₀ hdn]
  rw [hc, one_smul]

theorem multiplier_unitary (a : (ZMod d)ˣ) :
    multiplier d a ∈ Matrix.unitaryGroup (ZMod d) ℂ :=
  basisMap_unitary a.mulLeft

/-- The raw negation permutation is an involution. -/
theorem negation_sq :
    basisMap (fun j : ZMod d ↦ -j) * basisMap (fun j : ZMod d ↦ -j) = 1 := by
  rw [basisMap_mul]
  have hf : ((fun j : ZMod d ↦ -j) ∘ (fun j : ZMod d ↦ -j)) = id := by
    funext j; simp
  rw [hf, basisMap_id]

/-- The normalised Fourier gate has order dividing four in odd dimension. -/
theorem H_pow_four (hd : Odd d) : H d ^ 4 = 1 := by
  have hsign : (-1 : ℂ) ^ ((d - 1) / 2) * (-1 : ℂ) ^ ((d - 1) / 2) = 1 := by
    rw [← sq, ← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  calc
    H d ^ 4 = (H d * H d) * (H d * H d) := by noncomm_ring
    _ = 1 := by
      rw [H_sq_exact d hd, Matrix.smul_mul, Matrix.mul_smul, negation_sq, smul_smul,
        hsign, one_smul]

/-- Lemma 2.23, now explicitly stated with the adjoint. -/
theorem HXH_adjoint : H d * X d * (H d)ᴴ = Z d := by
  rw [HX_eq_ZH, mul_assoc, (show H d * (H d)ᴴ = 1 from (H_unitary d).2), mul_one]

theorem HZH_adjoint : H d * Z d * (H d)ᴴ = shift d (-1) := by
  rw [HZ_eq_XinvH, mul_assoc, (show H d * (H d)ᴴ = 1 from (H_unitary d).2), mul_one]

theorem SXS_adjoint (hd : Odd d) : S d * X d * (S d)ᴴ = X d * Z d := by
  rw [SX_eq_XZS d hd, mul_assoc, (show S d * (S d)ᴴ = 1 from (S_unitary d).2), mul_one]

theorem SZS_adjoint : S d * Z d * (S d)ᴴ = Z d := by
  rw [SZ_eq_ZS, mul_assoc, (show S d * (S d)ᴴ = 1 from (S_unitary d).2), mul_one]

omit [NeZero d] in
/-- Reflection changes the quadratic exponent by precisely the linear exponent. -/
theorem quadratic_neg (hd : Odd d) (j : ZMod d) :
    quadratic d (-j) = quadratic d j + j := by
  have hh := two_mul_half d hd
  dsimp [quadratic]
  calc
    -j * (-j - 1) * half d = j * (j - 1) * half d + j * (2 * half d) := by ring
    _ = j * (j - 1) * half d + j := by rw [hh, mul_one]

/-- Conjugation by the raw negation permutation. -/
theorem negation_S_negation (hd : Odd d) :
    basisMap (fun j : ZMod d ↦ -j) * S d * basisMap (fun j : ZMod d ↦ -j) = Z d * S d := by
  ext i j
  simp only [S, Z, clock]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, basisMap, Matrix.diagonal_apply,
    mul_ite, mul_zero, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true, neg_neg]
  by_cases hij : i = j
  · subst i; simp [quadratic_neg d hd, mul_comm]
  · simp [hij]

/-- Conjugating S by H squared supplies precisely the extra Z factor. -/
theorem H_sq_S_H_sq (hd : Odd d) : H d ^ 2 * S d * H d ^ 2 = Z d * S d := by
  have hsign : (-1 : ℂ) ^ ((d - 1) / 2) * (-1 : ℂ) ^ ((d - 1) / 2) = 1 := by
    rw [← sq, ← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  rw [pow_two, H_sq_exact d hd, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
    negation_S_negation d hd, smul_smul, hsign, one_smul]

theorem S_mul_pow_pred : S d * S d ^ (d - 1) = 1 := by
  rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)), S_pow_dimension]

/-- Figure 2 (T3), interpreted by exact matrix multiplication. -/
theorem Z_derived_word (hd : Odd d) :
    H d ^ 2 * S d * H d ^ 2 * S d ^ (d - 1) = Z d := by
  rw [H_sq_S_H_sq d hd, mul_assoc, S_mul_pow_pred, mul_one]

/-- Figure 2 (T2), interpreted by exact matrix multiplication. -/
theorem X_derived_word (hd : Odd d) :
    H d * S d * H d ^ 2 * S d ^ (d - 1) * H d = X d := by
  have h5 : H d ^ 5 = H d := by rw [show 5 = 4 + 1 from rfl, pow_succ, H_pow_four d hd, one_mul]
  calc
    H d * S d * H d ^ 2 * S d ^ (d - 1) * H d =
        H d ^ 3 * (H d ^ 2 * S d * H d ^ 2 * S d ^ (d - 1)) * H d := by
      simp only [← mul_assoc, ← pow_add]
      rw [h5]
    _ = H d ^ 3 * Z d * H d := by rw [Z_derived_word d hd]
    _ = H d ^ 3 * (H d * X d) := by rw [mul_assoc, ← HX_eq_ZH]
    _ = X d := by rw [← mul_assoc, ← pow_succ, H_pow_four d hd, one_mul]

end QuditClifford
