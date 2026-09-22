import QuditClifford.Centralizer

/-!
# Exact and projective equality

The two equivalence relations are intentionally separate. These results concern
actual matrices, not a scalar-free definition of a Clifford circuit. The final
theorem gives the uniqueness-up-to-phase consequence of Proposition 2.21.
-/

noncomputable section
namespace QuditClifford

open Matrix

variable {d n : ℕ} [NeZero d]

/-- Equality up to a nonzero complex scalar; for unitary matrices this scalar
necessarily has modulus one. -/
def ProjectiveEq (U V : QuditOperator d n) : Prop := ∃ c : ℂ, c ≠ 0 ∧ U = c • V

namespace ProjectiveEq

omit [NeZero d] in
 theorem refl (U : QuditOperator d n) : ProjectiveEq U U :=
  ⟨1, one_ne_zero, (one_smul _ _).symm⟩

omit [NeZero d] in
 theorem symm {U V : QuditOperator d n} (h : ProjectiveEq U V) : ProjectiveEq V U := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
  simp [smul_smul, hc]

omit [NeZero d] in
 theorem trans {U V W : QuditOperator d n} (h : ProjectiveEq U V) (h' : ProjectiveEq V W) :
    ProjectiveEq U W := by
  obtain ⟨c, hc, h⟩ := h
  obtain ⟨e, he, h'⟩ := h'
  exact ⟨c*e, mul_ne_zero hc he, by rw [h, h', smul_smul]⟩

 theorem mul {U V U' V' : QuditOperator d n} (h : ProjectiveEq U V) (h' : ProjectiveEq U' V') :
    ProjectiveEq (U*U') (V*V') := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨e, he, rfl⟩ := h'
  exact ⟨c*e, mul_ne_zero hc he, smul_mul_smul_comm _ _ _ _⟩

omit [NeZero d] in
 theorem of_eq {U V : QuditOperator d n} (h : U = V) : ProjectiveEq U V := h ▸ refl U

end ProjectiveEq

/-- Projective equivalence is an actual equivalence relation on matrices. -/
def projectiveSetoid : Setoid (QuditOperator d n) where
  r := ProjectiveEq
  iseqv := ⟨ProjectiveEq.refl, ProjectiveEq.symm, ProjectiveEq.trans⟩

/-- Equal Pauli conjugation actions force equality up to a nonzero scalar.
The supplied inverse equations make the invertibility hypotheses explicit. -/
theorem projectiveEq_of_same_pauli_action (U V Uinv Vinv : QuditOperator d n)
    (hU : Uinv * U = 1) (hU' : U * Uinv = 1)
    (hV : Vinv * V = 1)
    (h : ∀ p : Pauli d n, U * Pauli.repr p * Uinv = V * Pauli.repr p * Vinv) :
    ProjectiveEq V U := by
  obtain ⟨c, hc⟩ := scalar_ratio_of_same_pauli_action U V Uinv Vinv hU hV h
  have hVU : V = c • U := by
    have ht := congrArg (fun A => U*A) hc
    simpa only [← mul_assoc, hU', one_mul, Matrix.mul_smul, mul_one] using ht
  refine ⟨c, ?_, hVU⟩
  intro hz
  have hVzero : V = 0 := by simpa [hz] using hVU
  have h01 : (0 : QuditOperator d n) = 1 := by simp [hVzero] at hV
  have he := congrArg (fun A : QuditOperator d n => A 0 0) h01
  simp at he

/-- Unitary specialization of the same-action uniqueness theorem. -/
theorem unitary_projectiveEq_of_same_pauli_action (U V : QuditOperator d n)
    (hU : U ∈ Matrix.unitaryGroup (Pauli.Basis d n) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Pauli.Basis d n) ℂ)
    (h : ∀ p : Pauli d n, U * Pauli.repr p * Uᴴ = V * Pauli.repr p * Vᴴ) :
    ProjectiveEq V U :=
  projectiveEq_of_same_pauli_action U V Uᴴ Vᴴ hU.1 hU.2 hV.1 h

end QuditClifford
