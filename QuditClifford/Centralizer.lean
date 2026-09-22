import QuditClifford.PauliRepresentation

/-!
# The Pauli centralizer

Proposition 2.21, for actual complex matrices in any positive dimension:
a matrix commuting with all the Pauli X and Z operators is scalar.
No unitarity hypothesis is needed for this stronger linear-algebra statement.
-/

noncomputable section
namespace QuditClifford

variable {d n : ℕ} [NeZero d]

abbrev QuditOperator (d n : ℕ) := Matrix (Pauli.Basis d n) (Pauli.Basis d n) ℂ

/-- A tensor product of clocks is the diagonal of its phase polynomial. -/
theorem repr_Z_diagonal (z : Pauli.Basis d n) :
    Pauli.repr (Pauli.Z z) = Matrix.diagonal (fun j => phase d (dot z j)) := by
  classical
  ext i j
  by_cases h : i = j
  · subst i; simp [Pauli.repr, Matrix.diagonal_apply]
  · simp [Pauli.repr, Matrix.diagonal_apply, h]

/-- Commuting with every clock forces all off-diagonal entries to vanish. -/
theorem diagonal_of_commutes_Z (U : QuditOperator d n)
    (hZ : ∀ z, U * Pauli.repr (Pauli.Z z) = Pauli.repr (Pauli.Z z) * U) :
    U = Matrix.diagonal (fun j => U j j) := by
  classical
  ext row col
  by_cases h : row = col
  · subst row
    simp
  · have hi : ∃ i, row i ≠ col i := by
      by_contra h'
      push_neg at h'
      exact h (funext h')
    obtain ⟨i, hi⟩ := hi
    have he := congrArg (fun A : QuditOperator d n => A row col) (hZ (Pi.single i 1))
    simp only [repr_Z_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul] at he
    have he' : U row col * phase d (col i) = phase d (row i) * U row col := by
      simpa [dot, Pi.single_apply] using he
    have hne : phase d (col i) ≠ phase d (row i) := by
      intro hc
      exact hi ((phase_injective d hc).symm)
    have hu : U row col = 0 := by
      by_contra hu
      exact hne (mul_left_cancel₀ hu (he'.trans (mul_comm _ _)))
    simp [Matrix.diagonal_apply, h, hu]

/-- Proposition 2.21: the commutant of the Pauli generators consists of scalars. -/
theorem scalar_of_commutes_paulis (U : QuditOperator d n)
    (hX : ∀ x, U * Pauli.repr (Pauli.X x) = Pauli.repr (Pauli.X x) * U)
    (hZ : ∀ z, U * Pauli.repr (Pauli.Z z) = Pauli.repr (Pauli.Z z) * U) :
    ∃ c : ℂ, U = c • (1 : QuditOperator d n) := by
  classical
  have hd := diagonal_of_commutes_Z U hZ
  have hdiag (j : Pauli.Basis d n) : U j j = U 0 0 := by
    have hj := hX j
    rw [hd] at hj
    have he := congrArg (fun A : QuditOperator d n => A j 0) hj
    simpa [Matrix.diagonal_mul, Matrix.mul_diagonal, Pauli.repr] using he
  refine ⟨U 0 0, ?_⟩
  rw [hd]
  ext row col
  simp [Matrix.diagonal_apply, Matrix.one_apply, hdiag]

/-- Equivalent formulation that quantifies over all Pauli matrices. -/
theorem pauli_centralizer (U : QuditOperator d n) :
    (∀ p : Pauli d n, U * Pauli.repr p = Pauli.repr p * U) ↔
      ∃ c : ℂ, U = c • (1 : QuditOperator d n) := by
  constructor
  · intro h
    exact scalar_of_commutes_paulis U (fun x => h (Pauli.X x)) (fun z => h (Pauli.Z z))
  · rintro ⟨c, rfl⟩ p
    simp

/-- If two invertible operators induce the same conjugation on every Pauli,
their ratio is a scalar. The inverse equations are explicit, rather than
silently assuming an arbitrary matrix has an inverse. -/
theorem scalar_ratio_of_same_pauli_action (U V Uinv Vinv : QuditOperator d n)
    (hU : Uinv * U = 1) (hV : Vinv * V = 1)
    (h : ∀ p : Pauli d n,
      U * Pauli.repr p * Uinv = V * Pauli.repr p * Vinv) :
    ∃ c : ℂ, Uinv * V = c • (1 : QuditOperator d n) := by
  apply (pauli_centralizer (Uinv * V)).mp
  intro p
  have hp := congrArg (fun A => Uinv * A * V) (h p)
  simpa only [mul_assoc, ← mul_assoc Uinv U, hU, one_mul,
    ← mul_assoc Vinv V, hV, mul_one] using hp.symm

end QuditClifford
