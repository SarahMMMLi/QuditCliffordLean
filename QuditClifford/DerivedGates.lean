import QuditClifford.Relations

/-!
# Exact Fourier implementations of the derived two-qudit gates

This file identifies the raw computational-basis permutations with their
Hadamard/CZ circuit words. All normalization phases are retained.
-/

noncomputable section
namespace QuditClifford
open Matrix
open scoped Kronecker

/-- Right multiplication by a computational-basis map selects its output column. -/
theorem matrix_mul_basisMap {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℂ) (f : α → α) (i j : α) :
    (M * basisMap f) i j = M i (f j) := by
  simp [Matrix.mul_apply, basisMap, mul_ite]

variable (d : ℕ) [NeZero d]

/-- Fourier conjugation changes computational-basis controlled addition to CZ. -/
theorem secondWire_H_CX :
    secondWire d (H d) * CX d = CZ d * secondWire d (H d) := by
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  simp only [CX, matrix_mul_basisMap, controlledAddEquiv, Equiv.coe_fn_mk,
    CZ, Matrix.diagonal_mul, secondWire, Matrix.kronecker_apply, Matrix.one_apply]
  by_cases h : i₁ = j₁
  · subst i₁
    simp [H, fourierMatrix, mul_add, mul_comm, mul_left_comm, mul_assoc]
  · simp [h]

/-- The unnormalised two-wire Fourier/CZ layer appearing in T4. -/
def swapFourierKernel : TwoQuditMatrix d :=
  CZ d * (fourierMatrix d ⊗ₖ fourierMatrix d)

@[simp] theorem swapFourierKernel_apply (i j : ZMod d × ZMod d) :
    swapFourierKernel d i j = phase d (i.1 * i.2 + i.1 * j.1 + i.2 * j.2) := by
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  simp [swapFourierKernel, CZ, Matrix.diagonal_mul, Matrix.kronecker_apply,
    fourierMatrix, mul_assoc]

/-- Two Fourier/CZ layers collapse one sum by character orthogonality. -/
theorem swapFourierKernel_sq_apply (i j : ZMod d × ZMod d) :
    (swapFourierKernel d * swapFourierKernel d) i j =
      (d : ℂ) * phase d (-i.1 * j.2 - i.2 * j.1 - j.1 * j.2) := by
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, swapFourierKernel_apply]
  have hterm (a b : ZMod d) :
      phase d (i₁ * i₂ + i₁ * a + i₂ * b) * phase d (a * b + a * j₁ + b * j₂) =
      phase d (i₁ * i₂ + a * (i₁ + j₁)) * phase d ((i₂ + a + j₂) * b) := by
    simp only [← phase_add]
    congr 1
    ring
  simp only [hterm, ← Finset.mul_sum, phase_sum]
  have htest (a : ZMod d) : i₂ + a + j₂ = 0 ↔ a = -i₂ - j₂ := by
    constructor <;> intro h <;> linear_combination h
  simp only [htest, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [mul_comm]
  congr 2
  ring

/-- Three unnormalised layers give `d^3` times exact SWAP. -/
theorem swapFourierKernel_cube :
    swapFourierKernel d * swapFourierKernel d * swapFourierKernel d =
      (d : ℂ) ^ 3 • SWAP d := by
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  change (∑ a, ∑ b, (swapFourierKernel d * swapFourierKernel d) (i₁, i₂) (a, b) *
      swapFourierKernel d (a, b) (j₁, j₂)) = _
  simp only [swapFourierKernel_sq_apply, swapFourierKernel_apply]
  have hterm (a b : ZMod d) :
      ((d : ℂ) * phase d (-i₁ * b - i₂ * a - a * b)) *
          phase d (a * b + a * j₁ + b * j₂) =
      (d : ℂ) * (phase d ((j₁ - i₂) * a) * phase d ((j₂ - i₁) * b)) := by
    rw [mul_assoc, ← phase_add, ← phase_add]
    congr 2
    ring
  simp only [hterm, ← Finset.mul_sum, ← Finset.sum_mul, phase_sum]
  simp only [Matrix.smul_apply, smul_eq_mul, SWAP, basisMap, Prod.swap_prod_mk,
    Prod.mk.injEq, sub_eq_zero]
  by_cases h₁ : i₁ = j₂ <;> by_cases h₂ : i₂ = j₁ <;>
    simp [h₁, h₂, Ne.symm, eq_comm, pow_succ]
  ring

/-- T5 / Appendix (38): the derived circuit is exactly controlled addition. -/
theorem CX_derived (hd : Odd d) :
    secondWire d (H d ^ 3) * CZ d * secondWire d (H d) = CX d := by
  calc
    _ = secondWire d (H d ^ 3) * (CZ d * secondWire d (H d)) := mul_assoc _ _ _
    _ = secondWire d (H d ^ 3) * (secondWire d (H d) * CX d) := by rw [secondWire_H_CX]
    _ = secondWire d (H d ^ 3 * H d) * CX d := by rw [← mul_assoc, ← secondWire_mul]
    _ = CX d := by rw [← pow_succ, H_pow_four d hd, secondWire_one, one_mul]

/-- Squared Hadamard normalization times the dimension is the exact sign in C2. -/
theorem hadamard_scale_sq (hd : Odd d) :
    ((lambda d * (Real.sqrt d : ℂ))⁻¹) ^ 2 * (d : ℂ) =
      (-1 : ℂ) ^ ((d - 1) / 2) := by
  have hs : (Real.sqrt d : ℂ) ^ 2 = (d : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg d)
  have hdn : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  rw [inv_pow, mul_pow, hs, _root_.mul_inv_rev, mul_right_comm,
    inv_mul_cancel₀ hdn, one_mul, ← inv_pow, lambda_inv_sq d hd]

/-- The normalized three-layer circuit is SWAP times its exact normalization sign. -/
theorem swap_H_CZ_cube (hd : Odd d) :
    (CZ d * (H d ⊗ₖ H d)) ^ 3 =
      (-1 : ℂ) ^ ((d - 1) / 2) • SWAP d := by
  let c : ℂ := (lambda d * (Real.sqrt d : ℂ))⁻¹
  have hlayer : CZ d * (H d ⊗ₖ H d) = c ^ 2 • swapFourierKernel d := by
    simp only [H, Matrix.smul_kronecker, Matrix.kronecker_smul,
      smul_smul, Matrix.mul_smul, c, pow_two, swapFourierKernel]
  have hcube : swapFourierKernel d ^ 3 = (d : ℂ) ^ 3 • SWAP d := by
    simpa only [pow_succ, pow_zero, one_mul] using swapFourierKernel_cube d
  rw [hlayer, smul_pow, hcube, smul_smul, ← mul_pow]
  change (c ^ 2 * (d : ℂ)) ^ 3 • SWAP d = _
  rw [show c ^ 2 * (d : ℂ) = (-1 : ℂ) ^ ((d - 1) / 2) from hadamard_scale_sq d hd]
  have hsign : ((-1 : ℂ) ^ ((d - 1) / 2)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm _ 2, pow_mul, neg_one_sq, one_pow]
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, hsign, one_mul]

/-- Figure 2 (T4), with the indispensable exact factor `lambda_d^2`. -/
theorem SWAP_derived (hd : Odd d) :
    SWAP d = lambda d ^ 2 • (CZ d * (H d ⊗ₖ H d) * CZ d *
      (H d ⊗ₖ H d) * CZ d * (H d ⊗ₖ H d)) := by
  have hword : CZ d * (H d ⊗ₖ H d) * CZ d * (H d ⊗ₖ H d) * CZ d *
      (H d ⊗ₖ H d) = (CZ d * (H d ⊗ₖ H d)) ^ 3 := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [hword, swap_H_CZ_cube d hd, lambda_sq d hd, smul_smul, ← pow_two]
  have hsign : ((-1 : ℂ) ^ ((d - 1) / 2)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm _ 2, pow_mul, neg_one_sq, one_pow]
  rw [hsign, one_smul]

end QuditClifford
