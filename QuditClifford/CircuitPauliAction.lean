import QuditClifford.CircuitSemantics
import QuditClifford.CliffordAction
import QuditClifford.Relations
import QuditClifford.CircuitSymplectic

/-! # Exact Pauli conjugation by primitive circuits on arbitrary named wires

All conjugation formulas retain the central Pauli phase. The resulting
normalizer membership concerns the concrete complex circuit matrices.
-/
noncomputable section
namespace QuditClifford.Circuit
open Matrix
variable {d n : ℕ} [NeZero d]

/-- Right multiplication by a Pauli selects one shifted computational column. -/
theorem matrix_mul_repr_apply (M : QuditOperator d n) (p : Pauli d n)
    (row col : Pauli.Basis d n) :
    (M * p.repr) row col = M row (col + p.x) * phase d (p.phase + dot p.z col) := by
  classical
  simp [Matrix.mul_apply, Pauli.repr, mul_ite]

/-- Left multiplication by a Pauli selects one shifted computational row. -/
theorem repr_mul_matrix_apply (p : Pauli d n) (M : QuditOperator d n)
    (row col : Pauli.Basis d n) :
    (p.repr * M) row col = phase d (p.phase + dot p.z (row - p.x)) * M (row - p.x) col := by
  classical
  have hh (mid : Pauli.Basis d n) : row = mid + p.x ↔ mid = row - p.x := by
    rw [eq_sub_iff_add_eq]
    exact eq_comm
  simp [Matrix.mul_apply, Pauli.repr, hh, ite_mul]

omit [NeZero d] in
/-- Updating one dot-product coordinate changes exactly its local contribution. -/
theorem dot_update_left (u v : Pauli.Basis d n) (i : Fin n) (a : ZMod d) :
    dot (Function.update u i a) v = dot u v + (a - u i) * v i := by
  have hu : Function.update u i a = u + (a - u i) • exponentBasis i := by
    funext k
    by_cases hk : k = i
    · subst k; simp [exponentBasis]
    · simp [Function.update_of_ne hk, exponentBasis, hk]
  rw [hu, dot_add_left, dot_smul_left, dot_basis_left]

omit [NeZero d] in
theorem dot_update_right (u v : Pauli.Basis d n) (i : Fin n) (a : ZMod d) :
    dot u (Function.update v i a) = dot u v + u i * (a - v i) := by
  rw [dot_comm, dot_update_left, dot_comm v u, mul_comm]

/-- Exact H conjugation, including the phase from restoring X-before-Z order. -/
def hadamardPauli (i : Fin n) (p : Pauli d n) : Pauli d n :=
  ⟨p.phase - p.x i * p.z i, Function.update p.x i (-p.z i), Function.update p.z i (p.x i)⟩

/-- Exact S conjugation in the paper's j(j-1)/2 phase convention. -/
def phasePauli (i : Fin n) (p : Pauli d n) : Pauli d n :=
  ⟨p.phase + quadratic d (p.x i), p.x, Function.update p.z i (p.z i + p.x i)⟩

/-- Exact CZ conjugation; both updated Z coordinates and the scalar are retained. -/
def controlledPhasePauli (i j : Fin n) (p : Pauli d n) : Pauli d n :=
  ⟨p.phase + p.x i * p.x j, p.x,
    p.z + p.x j • exponentBasis i + p.x i • exponentBasis j⟩

/-- The placed Fourier matrix has the exact full-Pauli pushing relation. -/
theorem hadamard_repr_push (i : Fin n) (p : Pauli d n) :
    onWire i (QuditClifford.H d) * p.repr = (hadamardPauli i p).repr * onWire i (QuditClifford.H d) := by
  classical
  ext row col
  rw [matrix_mul_repr_apply, repr_mul_matrix_apply]
  have hoff : (∀ k, k ≠ i → (row - (hadamardPauli i p).x) k = col k) ↔
      (∀ k, k ≠ i → row k = (col + p.x) k) := by
    constructor <;> intro h k hk
    · have hh := h k hk
      simpa [hadamardPauli, Function.update_of_ne hk, sub_eq_iff_eq_add] using hh
    · have hh := h k hk
      simpa [hadamardPauli, Function.update_of_ne hk, sub_eq_iff_eq_add] using hh
  by_cases hh : ∀ k, k ≠ i → row k = (col + p.x) k
  · have hm : row - (hadamardPauli i p).x = Function.update col i (row i + p.z i) := by
      funext k
      by_cases hk : k = i
      · subst k; simp [hadamardPauli]
      · simpa [hadamardPauli, Function.update_of_ne hk, sub_eq_iff_eq_add] using hh k hk
    rw [onWire, if_pos hh, onWire, if_pos (hoff.mpr hh), hm]
    simp only [hadamardPauli, Function.update_self, dot_update_right, dot_update_left,
      Pi.add_apply, QuditClifford.H, Matrix.smul_apply, smul_eq_mul, fourierMatrix]
    rw [mul_assoc, ← phase_add]
    rw [mul_left_comm (phase d _) ((lambda d * ↑(Real.sqrt d))⁻¹) (phase d _), ← phase_add]
    congr 2
    ring
  · rw [onWire, if_neg hh, onWire, if_neg (fun h => hh (hoff.mp h))]
    simp

/-- The placed quadratic phase gate has its exact full-Pauli pushing relation. -/
theorem phase_repr_push (hd : Odd d) (i : Fin n) (p : Pauli d n) :
    onWire i (QuditClifford.S d) * p.repr = (phasePauli i p).repr * onWire i (QuditClifford.S d) := by
  classical
  rw [QuditClifford.S, onWire_diagonal]
  ext row col
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Pauli.repr, phasePauli]
  split_ifs with h
  · subst row
    simp only [Pi.add_apply, one_mul, mul_one, dot_update_left, add_sub_cancel_left,
      ← phase_add, quadratic_add d hd]
    congr 1
    ring
  · simp

/-- The placed controlled phase has its exact full-Pauli pushing relation. -/
theorem controlledPhase_repr_push (i j : Fin n) (p : Pauli d n) :
    Matrix.diagonal (fun row : Pauli.Basis d n => phase d (row i * row j)) * p.repr =
      (controlledPhasePauli i j p).repr *
        Matrix.diagonal (fun row : Pauli.Basis d n => phase d (row i * row j)) := by
  classical
  ext row col
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Pauli.repr, controlledPhasePauli]
  split_ifs with h
  · subst row
    simp only [Pi.add_apply, dot_add_left, dot_smul_left, dot_basis_left, ← phase_add]
    congr 1
    ring
  · simp

/-- Exact action of each primitive gate on ordered Pauli coordinates. -/
def Gate.pauliAction (d : ℕ) [NeZero d] : Gate n → Pauli d n → Pauli d n
  | .scalar, p => p
  | .H i, p => hadamardPauli i p
  | .S i, p => phasePauli i p
  | .CZ i j _, p => controlledPhasePauli i j p

/-- Discarding only the Pauli phase gives the specified primitive symplectic action. -/
theorem Gate.pauliAction_coords (g : Gate n) (p : Pauli d n) :
    (g.pauliAction d p).coords = g.symplecticAction d p.coords := by
  cases g with
  | scalar => rfl
  | H i =>
    apply Prod.ext <;> funext k <;> by_cases hk : k = i <;>
      simp [Gate.pauliAction, hadamardPauli, Pauli.coords, Gate.symplecticAction,
        localHadamard, hk, Function.update_of_ne]
  | S i =>
    apply Prod.ext <;> funext k <;> by_cases hk : k = i <;>
      simp [Gate.pauliAction, phasePauli, Pauli.coords, Gate.symplecticAction,
        localPhaseShear, hk, Function.update_of_ne]
  | CZ i j h =>
    simp [Gate.pauliAction, controlledPhasePauli, Pauli.coords, Gate.symplecticAction,
      controlledPhase]

/-- Every primitive gate pushes an arbitrary full-register Pauli exactly. -/
theorem Gate.denote_repr_push (hd : Odd d) (g : Gate n) (p : Pauli d n) :
    g.denote d * p.repr = (g.pauliAction d p).repr * g.denote d := by
  cases g with
  | scalar => simp [Gate.denote, Gate.pauliAction, Matrix.smul_mul, Matrix.mul_smul]
  | H i => exact hadamard_repr_push i p
  | S i => exact phase_repr_push hd i p
  | CZ i j h => exact controlledPhase_repr_push i j p

/-- Exact arbitrary-wire primitive conjugation, including its central phase. -/
theorem Gate.denote_conjugate_repr (hd : Odd d) (g : Gate n) (p : Pauli d n) :
    g.denote d * p.repr * (g.denote d)ᴴ = (g.pauliAction d p).repr := by
  rw [g.denote_repr_push hd, mul_assoc, show g.denote d * (g.denote d)ᴴ = 1 from g.denote_unitary.2,
    mul_one]

/-- Each primitive matrix lies in the concrete Pauli normalizer. -/
theorem Gate.denote_normalizes (hd : Odd d) (g : Gate n) : NormalizesPaulis (g.denote d) :=
  fun p => ⟨g.pauliAction d p, g.denote_conjugate_repr hd p⟩

/-- Full exact Pauli action, in the matrix order used by primitive words. -/
def pauliAction (d : ℕ) [NeZero d] : Word n → Pauli d n → Pauli d n
  | [], p => p
  | g :: w, p => g.pauliAction d (pauliAction d w p)

@[simp] theorem pauliAction_nil (p : Pauli d n) : pauliAction d [] p = p := rfl
@[simp] theorem pauliAction_cons (g : Gate n) (w : Word n) (p : Pauli d n) :
    pauliAction d (g :: w) p = g.pauliAction d (pauliAction d w p) := rfl

/-- Exact Pauli action composes in precisely the primitive circuit order. -/
theorem pauliAction_append (u v : Word n) (p : Pauli d n) :
    pauliAction d (u ++ v) p = pauliAction d u (pauliAction d v p) := by
  induction u with
  | nil => rfl
  | cons g u ih => simp only [List.cons_append, pauliAction_cons, ih]

/-- The circuit's full Pauli action has the already defined exponent action. -/
theorem pauliAction_coords (w : Word n) (p : Pauli d n) :
    (pauliAction d w p).coords = symplecticAction d w p.coords := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    rw [pauliAction_cons, Gate.pauliAction_coords, ih]
    rfl

/-- Exact Pauli pushing for every expanded primitive circuit. -/
theorem denote_repr_push (hd : Odd d) (w : Word n) (p : Pauli d n) :
    denote d w * p.repr = (pauliAction d w p).repr * denote d w := by
  induction w with
  | nil => simp
  | cons g w ih =>
    rw [denote_cons, mul_assoc, ih, ← mul_assoc, Gate.denote_repr_push hd, mul_assoc]
    rfl

/-- Every generated circuit conjugates full Pauli matrices exactly according
to its proved coordinate action, including the scalar phase. -/
theorem denote_conjugate_repr (hd : Odd d) (w : Word n) (p : Pauli d n) :
    denote d w * p.repr * (denote d w)ᴴ = (pauliAction d w p).repr := by
  rw [denote_repr_push hd, mul_assoc,
    show denote d w * (denote d w)ᴴ = 1 from (denote_unitary w).2, mul_one]

/-- Every actual primitive circuit matrix belongs to the concrete normalizer. -/
theorem denote_normalizes (hd : Odd d) (w : Word n) : NormalizesPaulis (denote d w) :=
  fun p => ⟨pauliAction d w p, denote_conjugate_repr hd w p⟩

/-- The automorphism extracted from actual matrix conjugation is the explicit
phase-sensitive evaluator, by faithfulness of the Pauli representation. -/
theorem pauliConjugationAut_denote (hd : Odd d) (w : Word n) (p : Pauli d n) :
    pauliConjugationAut (denote d w) (denote_unitary w) (denote_normalizes hd w) p =
      pauliAction d w p := by
  apply Pauli.repr_injective
  rw [repr_pauliConjugationAut, denote_conjugate_repr hd]

/-- The genuine matrix-normalizer symplectic action of a circuit agrees with
the explicit primitive exponent evaluator. -/
theorem cliffordSymplecticAction_denote_apply (hd : Odd d) (w : Word n) (v : PhaseSpace d n) :
    (cliffordSymplecticAction (denote d w) (denote_unitary w) (denote_normalizes hd w)).val v =
      symplecticAction d w v := by
  change (pauliConjugationAut (denote d w) (denote_unitary w) (denote_normalizes hd w)
    (Pauli.representative v)).coords = _
  rw [pauliConjugationAut_denote hd, pauliAction_coords, Pauli.coords_representative]

end QuditClifford.Circuit
