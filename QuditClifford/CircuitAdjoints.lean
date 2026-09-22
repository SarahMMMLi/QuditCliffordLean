import QuditClifford.CircuitSemantics

/-! # Primitive circuit words for exact adjoints

Finite gate orders realize adjoints without extending the primitive alphabet.
This file proves matrix interpretation only. Derivability of the cancellation
identities from Figure 1 belongs to `CircuitInverses`.
-/
noncomputable section
namespace QuditClifford.Circuit
open Matrix
variable {d n : ℕ} [NeZero d]

/-- Adjoint words use only positive powers of the original primitive gates. -/
def Gate.inverseWord (d : ℕ) : Gate n → Word n
  | .scalar => List.replicate (2*d-1) .scalar
  | .H i => List.replicate 3 (.H i)
  | .S i => List.replicate (d-1) (.S i)
  | .CZ i j h => List.replicate (d-1) (.CZ i j h)

/-- Reverse factor order and replace each factor by its primitive adjoint word. -/
def inverseWord (d : ℕ) (w : Word n) : Word n :=
  (w.reverse.map (Gate.inverseWord d)).flatten

private theorem adjoint_eq_pow_pred (A : QuditOperator d n)
    (hA : A ∈ Matrix.unitaryGroup (Pauli.Basis d n) ℂ)
    (m : ℕ) (hm : 1 ≤ m) (hpow : A^m = 1) : Aᴴ = A^(m-1) := by
  calc
    Aᴴ = Aᴴ * (A * A^(m-1)) := by rw [← pow_succ', Nat.sub_add_cancel hm, hpow, mul_one]
    _ = (Aᴴ*A)*A^(m-1) := (mul_assoc _ _ _).symm
    _ = A^(m-1) := by rw [show Aᴴ*A=1 from hA.1, one_mul]

/-- Each selected positive-power word has exactly the adjoint matrix. -/
theorem Gate.denote_inverseWord (hdOdd : Odd d) (g : Gate n) :
    Circuit.denote d (g.inverseWord d) = (g.denote d)ᴴ := by
  have hd : 1 ≤ d := NeZero.pos d
  cases g with
  | scalar =>
    rw [Gate.inverseWord, denote_replicate]
    symm
    apply adjoint_eq_pow_pred _ (Gate.denote_unitary .scalar) (2*d) (by omega)
    simpa only [Circuit.scalar, denote_replicate, denote_nil] using (C0_sound (d := d) (n := n))
  | H i =>
    rw [Gate.inverseWord, denote_replicate]
    symm
    apply adjoint_eq_pow_pred _ (Gate.denote_unitary (.H i)) 4 (by decide)
    change onWire i (QuditClifford.H d) ^ 4 = 1
    rw [← onWire_pow, H_pow_four d hdOdd, onWire_one]
  | S i =>
    rw [Gate.inverseWord, denote_replicate]
    symm
    apply adjoint_eq_pow_pred _ (Gate.denote_unitary (.S i)) d hd
    simpa only [denote_replicate, denote_nil] using (C1_sound (d := d) i)
  | CZ i j h =>
    rw [Gate.inverseWord, denote_replicate]
    symm
    apply adjoint_eq_pow_pred _ (Gate.denote_unitary (.CZ i j h)) d hd
    simpa only [denote_replicate, denote_nil] using (C6_sound (d := d) i j h)

omit [NeZero d] in
@[simp] theorem inverseWord_nil : inverseWord d ([] : Word n) = [] := rfl

omit [NeZero d] in
@[simp] theorem inverseWord_cons (g : Gate n) (w : Word n) :
    inverseWord d (g::w) = inverseWord d w ++ g.inverseWord d := by
  simp [inverseWord]

/-- Every primitive circuit's adjoint is itself denoted by a primitive word. -/
theorem denote_inverseWord (hd : Odd d) (w : Word n) : denote d (inverseWord d w) = (denote d w)ᴴ := by
  induction w with
  | nil => simp
  | cons g w ih =>
    rw [inverseWord_cons, denote_append, Gate.denote_inverseWord hd, ih,
      denote_cons, Matrix.conjTranspose_mul]

/-- A circuit interpreted as a member of the genuine matrix unitary group. -/
def unitaryDenote (w : Word n) : Matrix.unitaryGroup (Pauli.Basis d n) ℂ :=
  ⟨denote d w, denote_unitary w⟩

@[simp] theorem unitaryDenote_nil : unitaryDenote (d := d) ([] : Word n) = 1 := rfl

@[simp] theorem unitaryDenote_append (u v : Word n) :
    unitaryDenote (d := d) (u++v) = unitaryDenote u * unitaryDenote v :=
  Subtype.ext (denote_append u v)

@[simp] theorem unitaryDenote_inverseWord (hd : Odd d) (w : Word n) :
    unitaryDenote (d := d) (inverseWord d w) = (unitaryDenote (d := d) w)⁻¹ :=
  Subtype.ext (denote_inverseWord hd w)

end QuditClifford.Circuit
