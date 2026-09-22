import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! # Finite phase sums for the Fourier determinant

These real identities account for the phases of the Vandermonde factors.
They hold even in dimension zero; all subtractions below are in the reals.
-/
namespace QuditClifford
open scoped BigOperators

/-- Sum of the natural representatives of Fin d, in the reals. -/
theorem sum_fin_val_real (d : ℕ) :
    (∑ i : Fin d, (i.val : ℝ)) = (d : ℝ) * ((d : ℝ) - 1) / 2 := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [ih]
    push_cast
    ring

private theorem sum_compl_singleton_real {α : Type*} [Fintype α] [DecidableEq α]
    (i : α) (f : α → ℝ) :
    (∑ j ∈ ({i}ᶜ : Finset α), f j) = (∑ j, f j) - f i := by
  apply eq_sub_iff_add_eq.mpr
  simpa using Finset.sum_compl_add_sum ({i} : Finset α) f

/-- Number of strictly upper triangular pairs, expressed without truncation. -/
theorem sum_Ioi_one_real (d : ℕ) :
    (∑ i : Fin d, ∑ _j ∈ Finset.Ioi i, (1 : ℝ)) =
      (d : ℝ) * ((d : ℝ) - 1) / 2 := by
  have h := Finset.sum_sum_Ioi_add_eq_sum_sum_off_diag
    (fun (_i _j : Fin d) => (1 : ℝ))
  simp only [sum_compl_singleton_real] at h
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  have ht : (∑ i : Fin d, ∑ _j ∈ Finset.Ioi i, (1 : ℝ)) =
      ∑ i : Fin d, ((Finset.Ioi i).card : ℝ) := by simp
  rw [ht]
  linarith

/-- Sum of the two indices of every strictly upper triangular pair. -/
theorem sum_Ioi_indices_real (d : ℕ) :
    (∑ i : Fin d, ∑ j ∈ Finset.Ioi i, ((i.val : ℝ) + (j.val : ℝ))) =
      (d : ℝ) * ((d : ℝ) - 1)^2 / 2 := by
  have h := Finset.sum_sum_Ioi_add_eq_sum_sum_off_diag
    (fun (i j : Fin d) => (i.val : ℝ) + (j.val : ℝ))
  simp only [sum_compl_singleton_real] at h
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.mul_sum, sum_fin_val_real] at h
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  nlinarith

end QuditClifford
