import QuditClifford.CircuitSemantics
import QuditClifford.CliffordAction

/-! # Exact primitive circuit implementations of every Pauli

The words below expand all X and Z powers into the Figure 1 primitive alphabet.
Both ordinary omega-Paulis and the selected independent sign extension are
realized exactly. This is a matrix interpretation theorem, not a rewrite claim.
-/
noncomputable section
namespace QuditClifford.Circuit
open Matrix
variable {d n : ℕ} [NeZero d]

/-- A shift on one named wire is the corresponding faithful Pauli matrix. -/
theorem onWire_shift_eq_repr_X_single (i : Fin n) (a : ZMod d) :
    onWire i (shift d a) = Pauli.repr (Pauli.X (Pi.single i a)) := by
  classical
  ext row col
  have hrow : row = col + Pi.single i a ↔
      (∀ k, k ≠ i → row k = col k) ∧ row i = col i + a := by
    constructor
    · intro h
      subst row
      constructor
      · intro k hk
        simp [Pi.single_apply, hk]
      · simp
    · rintro ⟨ho, hi⟩
      funext k
      by_cases hk : k = i
      · subst k; simpa using hi
      · simpa [Pi.single_apply, hk] using ho k hk
  by_cases ho : ∀ k, k ≠ i → row k = col k <;>
    by_cases hi : row i = col i + a <;>
    simp [onWire, shift, basisMap, Pauli.repr, hrow, ho, hi]

/-- A clock on one named wire is the corresponding faithful Pauli matrix. -/
theorem onWire_clock_eq_repr_Z_single (i : Fin n) (a : ZMod d) :
    onWire i (clock d a) = Pauli.repr (Pauli.Z (Pi.single i a)) := by
  rw [clock, onWire_diagonal, repr_Z_diagonal]
  funext row
  simp [dot, Pi.single_apply]

/-- The expanded X word for each wire, concatenated in matrix order. -/
def allX (x : Pauli.Basis d n) : Word n :=
  ((List.finRange n).map (fun i => Xexp i (x i))).flatten

/-- The expanded Z word for each wire, concatenated in matrix order. -/
def allZ (z : Pauli.Basis d n) : Word n :=
  ((List.finRange n).map (fun i => Zexp i (z i))).flatten

private theorem denote_X_list (hd : Odd d) (x : Pauli.Basis d n) (is : List (Fin n)) :
    denote d ((is.map fun i => Xexp i (x i)).flatten) =
      Pauli.repr (Pauli.X ((is.map fun i => Pi.single i (x i)).sum)) := by
  induction is with
  | nil =>
    change 1 = Pauli.repr (1 : Pauli d n)
    rw [Pauli.repr_one]
  | cons i is ih =>
    simp only [List.map_cons, List.flatten_cons, List.sum_cons, denote_append]
    rw [denote_Xexp hd, onWire_shift_eq_repr_X_single, ih, ← Pauli.repr_mul, ← Pauli.X_add]

private theorem denote_Z_list (hd : Odd d) (z : Pauli.Basis d n) (is : List (Fin n)) :
    denote d ((is.map fun i => Zexp i (z i)).flatten) =
      Pauli.repr (Pauli.Z ((is.map fun i => Pi.single i (z i)).sum)) := by
  induction is with
  | nil =>
    change 1 = Pauli.repr (1 : Pauli d n)
    rw [Pauli.repr_one]
  | cons i is ih =>
    simp only [List.map_cons, List.flatten_cons, List.sum_cons, denote_append]
    rw [denote_Zexp hd, onWire_clock_eq_repr_Z_single, ih, ← Pauli.repr_mul, ← Pauli.Z_add]

omit [NeZero d] in
private theorem sum_single_finRange (x : Pauli.Basis d n) :
    ((List.finRange n).map fun i => Pi.single i (x i)).sum = x := by
  simpa [List.finRange, ← List.ofFn_id, List.map_ofFn, List.sum_ofFn] using
    Finset.univ_sum_single x

/-- The all-X primitive word denotes the tensor product of the requested shifts. -/
theorem denote_allX (hd : Odd d) (x : Pauli.Basis d n) :
    denote d (allX x) = Pauli.repr (Pauli.X x) := by
  rw [allX, denote_X_list hd, sum_single_finRange]

/-- The all-Z primitive word denotes the tensor product of the requested clocks. -/
theorem denote_allZ (hd : Odd d) (z : Pauli.Basis d n) :
    denote d (allZ z) = Pauli.repr (Pauli.Z z) := by
  rw [allZ, denote_Z_list hd, sum_single_finRange]

/-- An exact primitive word for a specified ordinary Pauli coordinate tuple. -/
def pauliWord (p : Pauli d n) : Word n := omegaPower p.phase ++ allX p.x ++ allZ p.z

theorem denote_pauliWord (hd : Odd d) (p : Pauli d n) :
    denote d (pauliWord p) = Pauli.repr p := by
  rw [pauliWord, denote_append, denote_append, denote_omegaPower hd,
    denote_allX hd, denote_allZ hd, ← repr_pauli_scalar, ← Pauli.repr_mul, ← Pauli.repr_mul,
    ← Pauli.normal_form]

/-- Include the independent sign required by Figure 1's scalar convention. -/
def signedPauliWord (p : SignedPauli d n) : Word n :=
  scalar (d * (Multiplicative.toAdd p.1).val) ++ pauliWord p.2

theorem denote_signedPauliWord (hd : Odd d) (p : SignedPauli d n) :
    denote d (signedPauliWord p) = SignedPauli.repr p := by
  have hs (s : ZMod 2) : (-1 : ℂ)^s.val = phase 2 s := by
    rw [← SignedPauli.phase_two_one, ← phase_nsmul]
    simp [nsmul_eq_mul]
  rw [signedPauliWord, denote_append, denote_scalar, denote_pauliWord hd,
    pow_mul, scalarGenerator_pow_dimension d hd, hs]
  simp [SignedPauli.repr]

/-- Every faithful ordinary Pauli matrix is unitary. -/
theorem pauli_repr_unitary (hd : Odd d) (p : Pauli d n) :
    Pauli.repr p ∈ Matrix.unitaryGroup (Pauli.Basis d n) ℂ := by
  rw [← denote_pauliWord hd p]
  exact denote_unitary _

/-- Faithful Pauli inversion is exactly the complex adjoint. -/
theorem pauli_repr_adjoint (hd : Odd d) (p : Pauli d n) :
    (Pauli.repr p)ᴴ = Pauli.repr p⁻¹ := by
  calc
    _ = (Pauli.repr p)ᴴ * (Pauli.repr p * Pauli.repr p⁻¹) := by
      rw [← Pauli.repr_mul, mul_inv_cancel, Pauli.repr_one, mul_one]
    _ = ((Pauli.repr p)ᴴ * Pauli.repr p) * Pauli.repr p⁻¹ := (mul_assoc _ _ _).symm
    _ = _ := by rw [show (Pauli.repr p)ᴴ * Pauli.repr p = 1 from (pauli_repr_unitary hd p).1, one_mul]

/-- Every faithful signed Pauli matrix is unitary. -/
theorem signedPauli_repr_unitary (hd : Odd d) (p : SignedPauli d n) :
    SignedPauli.repr p ∈ Matrix.unitaryGroup (Pauli.Basis d n) ℂ := by
  rw [← denote_signedPauliWord hd p]
  exact denote_unitary _

end QuditClifford.Circuit
