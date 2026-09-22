import QuditClifford.Circuit
import QuditClifford.NormalCoordinates

/-!
# Compositional exponent semantics for primitive circuit words

Lists are in matrix order, consistently with `Circuit.denote`: the rightmost
primitive acts first. Scalars act trivially only on exponent coordinates; the
complex interpretation continues to retain their exact values.
-/

noncomputable section
namespace QuditClifford.Circuit
variable {n : ℕ}

/-- The explicit exponent action of each primitive generator. -/
def Gate.symplecticAction (d : ℕ) : Gate n → PhaseSpace d n → PhaseSpace d n
  | .scalar => id
  | .H i => localHadamard i
  | .S i => localPhaseShear i 1
  | .CZ i j _ => controlledPhase i j 1

/-- Exponent action in the same matrix order as exact circuit denotation. -/
def symplecticAction (d : ℕ) : Word n → PhaseSpace d n → PhaseSpace d n
  | [], v => v
  | g :: w, v => g.symplecticAction d (symplecticAction d w v)

@[simp] theorem symplecticAction_nil (d : ℕ) (v : PhaseSpace d n) :
    symplecticAction d [] v = v := rfl

@[simp] theorem symplecticAction_cons (d : ℕ) (g : Gate n) (w : Word n) (v : PhaseSpace d n) :
    symplecticAction d (g :: w) v = g.symplecticAction d (symplecticAction d w v) := rfl

@[simp] theorem symplecticAction_append (d : ℕ) (w t : Word n) (v : PhaseSpace d n) :
    symplecticAction d (w ++ t) v = symplecticAction d w (symplecticAction d t v) := by
  induction w with
  | nil => rfl
  | cons g w ih => simp [ih]

theorem Gate.symplecticAction_preserves (d : ℕ) (g : Gate n) :
    PreservesSymplectic (g.symplecticAction d) := by
  cases g with
  | scalar => exact PreservesSymplectic.id
  | H i => exact localHadamard_preserves i
  | S i => exact localPhaseShear_preserves i 1
  | CZ i j h => exact controlledPhase_preserves i j 1

theorem symplecticAction_preserves (d : ℕ) (w : Word n) :
    PreservesSymplectic (symplecticAction d w) := by
  induction w with
  | nil => exact PreservesSymplectic.id
  | cons g w ih => exact (g.symplecticAction_preserves d).comp ih

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
@[simp] theorem symplecticAction_scalar (k : ℕ) (v : PhaseSpace d n) :
    symplecticAction d (scalar k) v = v := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [scalar, List.replicate_succ, symplecticAction_cons,
      Gate.symplecticAction, id_eq] using ih

omit [NeZero d] in
@[simp] theorem symplecticAction_omegaPower (a : ZMod d) (v : PhaseSpace d n) :
    symplecticAction d (omegaPower a) v = v := symplecticAction_scalar _ v

omit [NeZero d] in
theorem symplecticAction_replicate_S (i : Fin n) (k : ℕ) (v : PhaseSpace d n) :
    symplecticAction d (List.replicate k (.S i)) v = localPhaseShear i (k : ZMod d) v := by
  induction k with
  | zero => simp [localPhaseShear]
  | succ k ih =>
    simp only [List.replicate_succ, symplecticAction_cons, Gate.symplecticAction, ih,
      localPhaseShear_add]
    congr 1
    push_cast
    ring

@[simp] theorem symplecticAction_Sexp (i : Fin n) (a : ZMod d) (v : PhaseSpace d n) :
    symplecticAction d (Sexp i a) v = localPhaseShear i a v := by
  simp [Sexp, symplecticAction_replicate_S]

/-- The expanded Pauli Z has trivial exponent conjugation action. -/
@[simp] theorem symplecticAction_Z (i : Fin n) (v : PhaseSpace d n) :
    symplecticAction d (Z (d := d) i) v = v := by
  simp only [Z, symplecticAction_append, symplecticAction_cons, symplecticAction_nil,
    symplecticAction_Sexp, Gate.symplecticAction]
  apply Prod.ext <;> funext k <;> by_cases h : k = i <;>
    simp [localHadamard, localPhaseShear, h]

/-- The expanded Pauli X has trivial exponent conjugation action. -/
@[simp] theorem symplecticAction_X (i : Fin n) (v : PhaseSpace d n) :
    symplecticAction d (X (d := d) i) v = v := by
  simp only [X, symplecticAction_append, symplecticAction_cons, symplecticAction_nil,
    symplecticAction_Sexp, Gate.symplecticAction]
  apply Prod.ext <;> funext k <;> by_cases h : k = i <;>
    simp [localHadamard, localPhaseShear, h]

omit [NeZero d] in
/-- Every repeated word with trivial exponent action stays trivial. -/
theorem symplecticAction_power_id (w : Word n)
    (hw : ∀ v : PhaseSpace d n, symplecticAction d w v = v) (k : ℕ) (v : PhaseSpace d n) :
    symplecticAction d (power w k) v = v := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simpa only [power, List.replicate_succ, List.flatten_cons, symplecticAction_append, hw] using ih

@[simp] theorem symplecticAction_Xexp (i : Fin n) (a : ZMod d) (v : PhaseSpace d n) :
    symplecticAction d (Xexp i a) v = v :=
  symplecticAction_power_id _ (symplecticAction_X i) _ v

@[simp] theorem symplecticAction_Zexp (i : Fin n) (a : ZMod d) (v : PhaseSpace d n) :
    symplecticAction d (Zexp i a) v = v :=
  symplecticAction_power_id _ (symplecticAction_Z i) _ v

/-- The exact primitive multiplier word has the expected multiplier exponent action. -/
@[simp] theorem symplecticAction_multiplier [Fact d.Prime] (i : Fin n) (a : (ZMod d)ˣ)
    (v : PhaseSpace d n) :
    symplecticAction d (multiplier i a) v = localMultiplier i a v := by
  simp only [multiplier, symplecticAction_append, symplecticAction_scalar,
    symplecticAction_omegaPower, symplecticAction_Zexp, symplecticAction_Xexp,
    symplecticAction_Sexp, symplecticAction_cons, symplecticAction_nil, Gate.symplecticAction]
  apply Prod.ext <;> funext k <;> by_cases h : k = i <;>
    simp only [localHadamard, localPhaseShear, localMultiplier, h, ite_true, ite_false,
      Pi.neg_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  all_goals simp only [Units.val_inv_eq_inv_val]
  all_goals field_simp
  all_goals ring

/-- Exponent action of controlled addition to wire j, with coefficient a. -/
def controlledAdd (i j : Fin n) (a : ZMod d) (v : PhaseSpace d n) : PhaseSpace d n :=
  (v.1 - (a * v.1 j) • exponentBasis i, v.2 + (a * v.2 i) • exponentBasis j)

omit [NeZero d] in
/-- The expanded T5 word has the usual controlled-addition exponent action. -/
@[simp] theorem symplecticAction_CX (i j : Fin n) (hij : i ≠ j) (v : PhaseSpace d n) :
    symplecticAction d (CX i j hij) v = controlledAdd i j 1 v := by
  simp only [CX, symplecticAction_cons, symplecticAction_nil, Gate.symplecticAction]
  apply Prod.ext <;> funext k <;>
    by_cases hi : k = i <;> by_cases hj : k = j <;>
    simp [localHadamard, controlledPhase, controlledAdd, exponentBasis, hi, hj, hij, hij.symm]
  all_goals ring

omit [NeZero d] in
/-- Repeating CZ k times multiplies its exponent shear by k. -/
theorem symplecticAction_replicate_CZ (i j : Fin n) (hij : i ≠ j) (k : ℕ)
    (v : PhaseSpace d n) :
    symplecticAction d (List.replicate k (.CZ i j hij)) v = controlledPhase i j (k : ZMod d) v := by
  induction k with
  | zero => simp [controlledPhase]
  | succ k ih =>
    simp only [List.replicate_succ, symplecticAction_cons, Gate.symplecticAction, ih,
      controlledPhase_add]
    congr 1
    push_cast
    ring

omit [NeZero d] in
theorem controlledAdd_add (i j : Fin n) (hij : i ≠ j) (a b : ZMod d) (v : PhaseSpace d n) :
    controlledAdd i j a (controlledAdd i j b v) = controlledAdd i j (a + b) v := by
  apply Prod.ext <;> funext k <;> by_cases hi : k = i <;> by_cases hj : k = j <;>
    simp [controlledAdd, exponentBasis, hij, hij.symm, hi, hj, add_mul, mul_add]
  all_goals ring

omit [NeZero d] in
theorem symplecticAction_power_CX (i j : Fin n) (hij : i ≠ j) (k : ℕ)
    (v : PhaseSpace d n) :
    symplecticAction d (power (CX i j hij) k) v = controlledAdd i j (k : ZMod d) v := by
  induction k with
  | zero => simp [power, controlledAdd]
  | succ k ih =>
    simp only [power, List.replicate_succ, List.flatten_cons, symplecticAction_append,
      symplecticAction_CX] at *
    rw [ih, controlledAdd_add i j hij]
    congr 1
    push_cast
    ring

/-- Relabel the two specified wires. -/
def swapAction (i j : Fin n) (v : PhaseSpace d n) : PhaseSpace d n :=
  (v.1 ∘ Equiv.swap i j, v.2 ∘ Equiv.swap i j)

omit [NeZero d] in
/-- The expanded T4 word has exact wire-swap exponent action. -/
@[simp] theorem symplecticAction_SWAP (i j : Fin n) (hij : i ≠ j) (v : PhaseSpace d n) :
    symplecticAction d (SWAP (d := d) i j hij) v = swapAction i j v := by
  simp only [SWAP, power, List.replicate_succ, List.replicate_zero, List.flatten_cons,
    List.flatten_nil, symplecticAction_append, symplecticAction_scalar,
    symplecticAction_cons, symplecticAction_nil, Gate.symplecticAction]
  apply Prod.ext <;> funext k <;>
    by_cases hi : k = i <;> by_cases hj : k = j <;>
    simp [localHadamard, controlledPhase, swapAction, exponentBasis, hi, hj, hij, hij.symm,
      Equiv.swap_apply_def]

end QuditClifford.Circuit
