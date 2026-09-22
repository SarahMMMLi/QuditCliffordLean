import QuditClifford.GaussSign

/-! # Exact determinants of the phase and controlled-phase gates -/

noncomputable section
namespace QuditClifford

variable (d : ℕ) [Fact d.Prime]

/-- The determinant of the diagonal phase gate is the character of the total exponent. -/
theorem det_S_eq_phase_sum : Matrix.det (S d) = phase d (∑ x : ZMod d, quadratic d x) := by
  rw [S, Matrix.det_diagonal, phase_finset_sum]

/-- Away from the exceptional prime three, the quadratic exponent sums to zero. -/
theorem sum_quadratic_eq_zero (hd : 3 < d) : ∑ x : ZMod d, quadratic d x = 0 := by
  have hs₁ : ∑ x : ZMod d, x = 0 := by
    simpa only [pow_one] using FiniteField.sum_pow_lt_card_sub_one (ZMod d) 1
      (by simpa only [ZMod.card] using (show 1 < d - 1 by omega))
  have hs₂ : ∑ x : ZMod d, x ^ 2 = 0 :=
    FiniteField.sum_pow_lt_card_sub_one (ZMod d) 2
      (by simpa only [ZMod.card] using (show 2 < d - 1 by omega))
  calc
    _ = ((∑ x : ZMod d, x ^ 2) - ∑ x : ZMod d, x) * half d := by
      rw [← Finset.sum_sub_distrib, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      dsimp [quadratic]
      ring
    _ = 0 := by rw [hs₁, hs₂]; ring

/-- Lemma A.10 for odd primes greater than three. -/
theorem det_S_eq_one (hd : 3 < d) : Matrix.det (S d) = 1 := by
  rw [det_S_eq_phase_sum, sum_quadratic_eq_zero d hd, phase_zero]

/-- The exceptional qutrit phase gate has determinant omega. -/
theorem det_S_three : Matrix.det (S 3) = omega 3 := by
  rw [det_S_eq_phase_sum]
  have hsum : (∑ x : ZMod 3, quadratic 3 x) = 1 := by
    change (∑ x : Fin 3, quadratic 3 x) = 1
    rw [Fin.sum_univ_three]
    norm_num [quadratic, half]
    exact two_mul_half 3 (by decide)
  rw [hsum]
  rfl

/-- Lemma A.10, including the exceptional qutrit determinant. -/
theorem det_S_exact (hd : Odd d) : Matrix.det (S d) = if d = 3 then omega d else 1 := by
  by_cases hthree : d = 3
  · subst d
    simpa using det_S_three
  · rw [if_neg hthree]
    apply det_S_eq_one
    have hp := (Fact.out : d.Prime).two_le
    have ho := Nat.odd_iff.mp hd
    omega

/-- The controlled-phase generator has determinant one in odd prime dimension. -/
theorem det_CZ_eq_one (hd : Odd d) : Matrix.det (CZ d) = 1 := by
  rw [CZ, Matrix.det_diagonal, ← phase_finset_sum, Fintype.sum_prod_type]
  have hs : (∑ x : ZMod d, ∑ y : ZMod d, x * y) = 0 := by
    rw [← Finset.sum_mul_sum, sum_residues_eq_zero d hd, zero_mul]
  rw [hs, phase_zero]

end QuditClifford
