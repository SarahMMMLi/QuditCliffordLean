import QuditClifford.Circuit

/-! # Sound complex-matrix semantics on arbitrary named wires

The proofs in this file establish the tensor-placement laws from the concrete
matrix entries, rather than postulating a monoidal interpretation.
-/

noncomputable section
namespace QuditClifford
namespace Circuit

open Matrix

variable {d n : ℕ} [NeZero d]

/-- The column outside the chosen wire fixes all intermediate basis indices. -/
private theorem sum_onWire_right (i : Fin n) (A B : QuditMatrix d)
    (row col : Fin n → ZMod d) :
    ∑ mid, onWire i A row mid * onWire i B mid col =
      ∑ t : ZMod d, onWire i A row (Function.update col i t) *
        onWire i B (Function.update col i t) col := by
  classical
  let f := fun mid ↦ onWire i A row mid * onWire i B mid col
  have hinj : Function.Injective (fun t : ZMod d ↦ Function.update col i t) := by
    intro a b hab
    have hh := congrFun hab i
    simpa using hh
  change ∑ mid, f mid = ∑ t, f (Function.update col i t)
  rw [← Finset.sum_image hinj.injOn]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro mid _ hnot
  have hoff : ¬ ∀ k, k ≠ i → mid k = col k := by
    intro hm
    apply hnot
    apply Finset.mem_image.mpr
    refine ⟨mid i, Finset.mem_univ _, ?_⟩
    funext k
    by_cases hk : k = i
    · subst k; simp
    · simp [Function.update_of_ne hk, hm k hk]
  simp [f, onWire, hoff]

/-- Placement on a fixed wire preserves matrix multiplication. -/
theorem onWire_mul (i : Fin n) (A B : QuditMatrix d) :
    onWire i (A * B) = onWire i A * onWire i B := by
  classical
  ext row col
  rw [Matrix.mul_apply, sum_onWire_right]
  have hleft (t : ZMod d) :
      (∀ k, k ≠ i → row k = Function.update col i t k) ↔
        (∀ k, k ≠ i → row k = col k) := by
    constructor <;> intro h k hk
    · simpa [Function.update_of_ne hk] using h k hk
    · simpa [Function.update_of_ne hk] using h k hk
  have hright (t : ZMod d) :
      ∀ k, k ≠ i → Function.update col i t k = col k := by
    intro k hk
    simp [Function.update_of_ne hk]
  by_cases hoff : ∀ k, k ≠ i → row k = col k
  · have hh (t : ZMod d) : onWire i A row (Function.update col i t) *
          onWire i B (Function.update col i t) col = A (row i) t * B t (col i) := by
      rw [onWire, if_pos ((hleft t).mpr hoff), onWire, if_pos (hright t)]
      simp
    simp only [hh]
    simp only [onWire, if_pos hoff, Matrix.mul_apply]
  · have hh (t : ZMod d) : onWire i A row (Function.update col i t) = 0 := by
      rw [onWire, if_neg (fun h ↦ hoff ((hleft t).mp h))]
    simp only [hh, zero_mul, Finset.sum_const_zero]
    simp only [onWire, if_neg hoff]

omit [NeZero d] in
/-- Placement commutes with the complex adjoint. -/
theorem onWire_adjoint (i : Fin n) (A : QuditMatrix d) :
    (onWire i A)ᴴ = onWire i Aᴴ := by
  classical
  ext row col
  have hoff : (∀ k, k ≠ i → row k = col k) ↔ (∀ k, k ≠ i → col k = row k) := by
    simp only [eq_comm]
  by_cases h : ∀ k, k ≠ i → row k = col k
  · simp only [Matrix.conjTranspose_apply, onWire, if_pos h, if_pos (hoff.mp h)]
  · simp only [Matrix.conjTranspose_apply, onWire, if_neg h, if_neg ((not_congr hoff).mp h), map_zero, star_zero]

/-- A one-wire unitary remains unitary on every larger register. -/
theorem onWire_unitary (i : Fin n) (A : QuditMatrix d)
    (hA : A ∈ Matrix.unitaryGroup (ZMod d) ℂ) :
    onWire i A ∈ Matrix.unitaryGroup (Fin n → ZMod d) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change (onWire i A)ᴴ * onWire i A = 1
  rw [onWire_adjoint, ← onWire_mul, (show Aᴴ * A = 1 from hA.1), onWire_one]

/-- Placement preserves natural powers. -/
theorem onWire_pow (i : Fin n) (A : QuditMatrix d) (k : ℕ) :
    onWire i (A ^ k) = onWire i A ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, onWire_mul, ih, pow_succ]

/-- Every primitive gate denotes an actual unitary on the full register. -/
theorem Gate.denote_unitary (g : Gate n) :
    g.denote d ∈ Matrix.unitaryGroup (Fin n → ZMod d) ℂ := by
  cases g with
  | scalar =>
    apply Matrix.mem_unitaryGroup_iff'.mpr
    change (scalarGenerator d • (1 : QuditOperator d n))ᴴ * (scalarGenerator d • 1) = 1
    simp [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      scalarGenerator, omega, phase_star]
  | H i => exact onWire_unitary i _ (H_unitary d)
  | S i => exact onWire_unitary i _ (S_unitary d)
  | CZ i j h => exact phase_diagonal_unitary d (fun x : Fin n → ZMod d ↦ x i * x j)

@[simp] theorem denote_cons (g : Gate n) (w : Word n) :
    denote d (g :: w) = g.denote d * denote d w := rfl

/-- Every primitive circuit is unitary, in any arity (including zero wires). -/
theorem denote_unitary (w : Word n) :
    denote d w ∈ Matrix.unitaryGroup (Fin n → ZMod d) ℂ := by
  induction w with
  | nil => exact (Matrix.unitaryGroup _ ℂ).one_mem
  | cons g w ih =>
    rw [denote_cons]
    exact (Matrix.unitaryGroup _ ℂ).mul_mem g.denote_unitary ih

@[simp] theorem denote_replicate (g : Gate n) (k : ℕ) :
    denote d (List.replicate k g) = g.denote d ^ k := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, ih, pow_succ']

/-- The exact denotation of any scalar word. -/
theorem denote_scalar (k : ℕ) :
    denote d (scalar (n := n) k) = scalarGenerator d ^ k • (1 : QuditOperator d n) := by
  rw [scalar, denote_replicate]
  change (scalarGenerator d • (1 : QuditOperator d n)) ^ k = _
  rw [smul_pow, one_pow]

/-- Figure 1 C0 is sound on every number of wires. -/
theorem C0_sound : denote d (scalar (n := n) (2*d)) = denote d ([] : Word n) := by
  simp [denote_scalar]

/-- Figure 1 C1 is sound on every named wire. -/
theorem C1_sound (i : Fin n) :
    denote d (List.replicate d (.S i)) = denote d ([] : Word n) := by
  rw [denote_replicate]
  change onWire i (QuditClifford.S d) ^ d = 1
  rw [← onWire_pow, S_pow_dimension, onWire_one]

/-- Figure 1 C6 is sound on any two distinct named wires. -/
theorem C6_sound (i j : Fin n) (h : i ≠ j) :
    denote d (List.replicate d (.CZ i j h)) = denote d ([] : Word n) := by
  rw [denote_replicate]
  change Matrix.diagonal (fun x : Fin n → ZMod d ↦ phase d (x i * x j)) ^ d = 1
  ext row col
  simp [Matrix.diagonal_pow, Matrix.diagonal_apply, Matrix.one_apply, Pi.pow_apply]

omit [NeZero d] in
/-- Placement of a diagonal matrix is the corresponding register diagonal. -/
theorem onWire_diagonal (i : Fin n) (f : ZMod d → ℂ) :
    onWire i (Matrix.diagonal f) = Matrix.diagonal (fun row : Fin n → ZMod d ↦ f (row i)) := by
  classical
  ext row col
  by_cases h : row = col
  · subst row; simp [onWire, Matrix.diagonal_apply]
  · by_cases hoff : ∀ k, k ≠ i → row k = col k
    · have hi : row i ≠ col i := by
        intro hi
        apply h
        funext k
        by_cases hk : k = i
        · simpa [hk] using hi
        · exact hoff k hk
      simp only [onWire, if_pos hoff, Matrix.diagonal_apply, if_neg h, if_neg hi]
    · simp only [onWire, if_neg hoff, Matrix.diagonal_apply, if_neg h]

theorem denote_Sexp (i : Fin n) (a : ZMod d) :
    denote d (Sexp i a) = onWire i (QuditClifford.S d ^ a.val) := by
  rw [Sexp, denote_replicate, onWire_pow]
  rfl

private theorem neg_one_val : (-1 : ZMod d).val = d - 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)
  simp [ZMod.val_neg_one]

/-- The fully expanded T3 word has exactly the desired Z matrix on any wire. -/
theorem denote_Z (hd : Odd d) (i : Fin n) :
    denote d (Z (d := d) i) = onWire i (QuditClifford.Z d) := by
  simp only [Z, denote_append, denote_cons, denote_nil, Gate.denote, mul_one,
    denote_Sexp, neg_one_val]
  simp only [← onWire_mul]
  apply congrArg (onWire i)
  simpa only [pow_two, mul_assoc] using Z_derived_word d hd

/-- The fully expanded T2 word has exactly the desired X matrix on any wire. -/
theorem denote_X (hd : Odd d) (i : Fin n) :
    denote d (X (d := d) i) = onWire i (QuditClifford.X d) := by
  simp only [X, denote_append, denote_cons, denote_nil, Gate.denote, mul_one,
    denote_Sexp, neg_one_val]
  simp only [← onWire_mul]
  apply congrArg (onWire i)
  simpa only [pow_two, mul_assoc] using X_derived_word d hd

/-- Matrix multiplication with a placed one-wire operator is a one-coordinate sum. -/
theorem mul_onWire_apply (i : Fin n) (M : QuditOperator d n) (B : QuditMatrix d)
    (row col : Fin n → ZMod d) :
    (M * onWire i B) row col =
      ∑ t : ZMod d, M row (Function.update col i t) * B t (col i) := by
  classical
  rw [Matrix.mul_apply]
  let f := fun mid ↦ M row mid * onWire i B mid col
  have hinj : Function.Injective (fun t : ZMod d ↦ Function.update col i t) := by
    intro a b hab
    have hh := congrFun hab i
    simpa using hh
  have hsum : ∑ mid, f mid = ∑ t, f (Function.update col i t) := by
    rw [← Finset.sum_image hinj.injOn]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro mid _ hnot
    have hoff : ¬ ∀ k, k ≠ i → mid k = col k := by
      intro hm
      apply hnot
      apply Finset.mem_image.mpr
      refine ⟨mid i, Finset.mem_univ _, ?_⟩
      funext k
      by_cases hk : k = i
      · subst k; simp
      · simp [Function.update_of_ne hk, hm k hk]
    simp [f, onWire, hoff]
  change ∑ mid, f mid = _
  rw [hsum]
  apply Finset.sum_congr rfl
  intro t _
  have hoff : ∀ k, k ≠ i → Function.update col i t k = col k := by
    intro k hk; simp [Function.update_of_ne hk]
  simp only [f, onWire, if_pos hoff, Function.update_self]

omit [NeZero d] in
private theorem off_update_iff (i j : Fin n) (hij : i ≠ j)
    (row col : Fin n → ZMod d) (t : ZMod d) :
    (∀ k, k ≠ i → row k = Function.update col j t k) ↔
      ((∀ k, k ≠ i → k ≠ j → row k = col k) ∧ row j = t) := by
  constructor
  · intro h
    constructor
    · intro k hki hkj
      simpa [Function.update_of_ne hkj] using h k hki
    · simpa using h j hij.symm
  · rintro ⟨h, hj⟩ k hki
    by_cases hkj : k = j
    · subst k; simp [hj]
    · simp [Function.update_of_ne hkj, h k hki hkj]

/-- Exact entries of a product of two operators on distinct wires. -/
theorem onWire_mul_other_apply (i j : Fin n) (hij : i ≠ j) (A B : QuditMatrix d)
    (row col : Fin n → ZMod d) :
    (onWire i A * onWire j B) row col =
      if ∀ k, k ≠ i → k ≠ j → row k = col k then A (row i) (col i) * B (row j) (col j) else 0 := by
  classical
  rw [mul_onWire_apply]
  simp only [onWire, off_update_iff i j hij, Function.update_of_ne hij]
  by_cases hoff : ∀ k, k ≠ i → k ≠ j → row k = col k
  · simp only [iff_true_intro hoff, true_and, if_true]
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  · simp only [hoff, false_and, if_false, zero_mul, Finset.sum_const_zero]

/-- Operators on distinct wires commute exactly. -/
theorem onWire_commute (i j : Fin n) (hij : i ≠ j) (A B : QuditMatrix d) :
    onWire i A * onWire j B = onWire j B * onWire i A := by
  ext row col
  rw [onWire_mul_other_apply i j hij, onWire_mul_other_apply j i hij.symm]
  have hoff : (∀ k, k ≠ i → k ≠ j → row k = col k) ↔
      (∀ k, k ≠ j → k ≠ i → row k = col k) := by
    constructor <;> intro h k ha hb <;> exact h k hb ha
  simp only [hoff, mul_comm]

/-- A diagonal independent of wire i commutes with every operator placed on i. -/
theorem onWire_diagonal_commute (i : Fin n) (A : QuditMatrix d)
    (f : (Fin n → ZMod d) → ℂ)
    (hf : ∀ row col, (∀ k, k ≠ i → row k = col k) → f row = f col) :
    onWire i A * Matrix.diagonal f = Matrix.diagonal f * onWire i A := by
  classical
  ext row col
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hoff : ∀ k, k ≠ i → row k = col k
  · simp only [onWire, if_pos hoff, hf row col hoff, mul_comm]
  · simp only [onWire, if_neg hoff, zero_mul, mul_zero]

/-- A one-wire operation commutes with controlled-Z on two other wires. -/
theorem onWire_CZ_commute (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k)
    (A : QuditMatrix d) :
    onWire i A * Matrix.diagonal (fun x : Fin n → ZMod d ↦ phase d (x j * x k)) =
      Matrix.diagonal (fun x : Fin n → ZMod d ↦ phase d (x j * x k)) * onWire i A := by
  apply onWire_diagonal_commute
  intro row col hoff
  rw [hoff j hij.symm, hoff k hik.symm]

/-- Any two diagonal operators commute. -/
theorem diagonals_commute {α : Type*} [Fintype α] [DecidableEq α] (f g : α → ℂ) :
    Matrix.diagonal f * Matrix.diagonal g = Matrix.diagonal g * Matrix.diagonal f := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext a
  exact mul_comm _ _

/-- Disjoint supports give exact commutation for all primitive gate combinations. -/
theorem Gate.denote_commute (a b : Gate n) (h : Disjoint a.support b.support) :
    a.denote d * b.denote d = b.denote d * a.denote d := by
  classical
  cases a with
  | scalar => simp [Gate.denote, Matrix.smul_mul, Matrix.mul_smul]
  | H i =>
    cases b with
    | scalar => simp [Gate.denote, Matrix.smul_mul, Matrix.mul_smul]
    | H j =>
      apply onWire_commute
      simpa [Gate.support, ne_comm] using h
    | S j =>
      apply onWire_commute
      simpa [Gate.support, ne_comm] using h
    | CZ j k hjk =>
      have h' : i ≠ j ∧ i ≠ k := by simpa [Gate.support, ne_comm] using h
      exact onWire_CZ_commute i j k h'.1 h'.2 _
  | S i =>
    cases b with
    | scalar => simp [Gate.denote, Matrix.smul_mul, Matrix.mul_smul]
    | H j =>
      apply onWire_commute
      simpa [Gate.support, ne_comm] using h
    | S j =>
      apply onWire_commute
      simpa [Gate.support, ne_comm] using h
    | CZ j k hjk =>
      have h' : i ≠ j ∧ i ≠ k := by simpa [Gate.support, ne_comm] using h
      exact onWire_CZ_commute i j k h'.1 h'.2 _
  | CZ i j hij =>
    cases b with
    | scalar => simp [Gate.denote, Matrix.smul_mul, Matrix.mul_smul]
    | H k =>
      have h' : k ≠ i ∧ k ≠ j := by simpa [Gate.support, ne_comm] using h.symm
      exact (onWire_CZ_commute k i j h'.1 h'.2 _).symm
    | S k =>
      have h' : k ≠ i ∧ k ≠ j := by simpa [Gate.support, ne_comm] using h.symm
      exact (onWire_CZ_commute k i j h'.1 h'.2 _).symm
    | CZ k l hkl => exact diagonals_commute _ _

/-- The structural wiring equations are sound in the concrete interpretation. -/
theorem structural_sound {u v : Word n} (h : Structural u v) : denote d u = denote d v := by
  cases h with
  | disjoint a b hab =>
    simpa only [denote_cons, denote_nil, mul_one] using Gate.denote_commute a b hab
  | CZ_symmetry i j hij =>
    simp only [denote_cons, denote_nil, mul_one, Gate.denote]
    apply congrArg Matrix.diagonal
    funext x
    rw [mul_comm]

/-- Figure 1 C8 is sound as an expanded primitive word on arbitrary wires. -/
theorem C8_sound (i j : Fin n) (h : i ≠ j) :
    denote d [.CZ i j h, .S i] = denote d [.S i, .CZ i j h] := by
  simp only [denote_cons, denote_nil, mul_one, Gate.denote, QuditClifford.S, onWire_diagonal]
  exact diagonals_commute _ _

/-- Powers of the paper's root represented by the primitive scalar alphabet. -/
theorem denote_omegaPower (hd : Odd d) (a : ZMod d) :
    denote d (omegaPower (n := n) a) = phase d a • (1 : QuditOperator d n) := by
  rw [omegaPower, denote_scalar, pow_mul, scalarGenerator_pow_dimension_add_one d hd,
    ← phase_natCast, ZMod.natCast_zmod_val]

/-- The expanded power word acts as translation by its residue exponent. -/
theorem denote_Xexp (hd : Odd d) (i : Fin n) (a : ZMod d) :
    denote d (Xexp i a) = onWire i (shift d a) := by
  rw [Xexp, denote_power, denote_X hd, ← onWire_pow]
  simp [QuditClifford.X, shift_pow, nsmul_eq_mul]

/-- The expanded power word acts as the clock with its residue exponent. -/
theorem denote_Zexp (hd : Odd d) (i : Fin n) (a : ZMod d) :
    denote d (Zexp i a) = onWire i (clock d a) := by
  rw [Zexp, denote_power, denote_Z hd, ← onWire_pow]
  simp [QuditClifford.Z, clock_pow, nsmul_eq_mul]

/-- Figure 1 C5 is sound as an expanded primitive word on every named wire. -/
theorem C5_sound (hd : Odd d) (i : Fin n) :
    denote d [.S i, .H i, .H i, .S i, .H i, .H i] =
      denote d [.H i, .H i, .S i, .H i, .H i, .S i] := by
  have hlocal : QuditClifford.S d * (QuditClifford.H d ^ 2 * QuditClifford.S d * QuditClifford.H d ^ 2) =
      (QuditClifford.H d ^ 2 * QuditClifford.S d * QuditClifford.H d ^ 2) * QuditClifford.S d := by
    rw [H_sq_S_H_sq d hd, ← mul_assoc, SZ_eq_ZS, mul_assoc]
  simp only [denote_cons, denote_nil, mul_one, Gate.denote, ← onWire_mul]
  apply congrArg (onWire i)
  simpa only [pow_two, mul_assoc] using hlocal

end Circuit
end QuditClifford
