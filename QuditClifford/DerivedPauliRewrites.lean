import QuditClifford.PresentedCircuit

/-!
# Derived Pauli relations inside the actual Figure 1 presentation

The calculations take place in the syntactic quotient group and are transported
back to contextual derivations. They never infer a rewrite from matrix equality.
This proves a concrete subset of Pauli rules, rather than assuming the standalone
Pauli block presentation is already realized by primitive Clifford circuits.
-/

noncomputable section
namespace QuditClifford.Circuit

variable {d n : ℕ} [NeZero d]

theorem classWord_cons (g : (ZMod d)ˣ) (a : Gate n) (w : Word n) :
    classWord g (a::w) = classWord g [a] * classWord g w := rfl

/-- Word powers become group powers in the genuine syntactic quotient. -/
theorem classWord_power (g : (ZMod d)ˣ) (w : Word n) (k : ℕ) :
    classWord g (power w k) = classWord g w ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [power_succ, classWord_append, ih, pow_succ']

/-- Repeated primitive letters become powers of their one-letter class. -/
theorem classWord_replicate (g : (ZMod d)ˣ) (a : Gate n) (k : ℕ) :
    classWord g (List.replicate k a) = classWord g [a] ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, classWord_cons, ih, pow_succ']

private theorem val_neg_one_pred : (-1 : ZMod d).val = d-1 := by
  cases d with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ k => simpa only [Nat.add_sub_cancel] using ZMod.val_neg_one k

variable [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

private abbrev hClass (i : Fin n) : PresentedCircuit g n := classWord g [.H i]
private abbrev sClass (i : Fin n) : PresentedCircuit g n := classWord g [.S i]
private abbrev zClass (i : Fin n) : PresentedCircuit g n := classWord g (Z (d := d) i)
private abbrev xClass (i : Fin n) : PresentedCircuit g n := classWord g (X (d := d) i)

private theorem hClass_four (i : Fin n) : hClass g i ^ 4 = 1 := by
  have h := (classWord_eq_iff_derives g (List.replicate 4 (.H i)) []).mpr
    (derives_H_four Fact.out g Fact.out i)
  simpa only [classWord_replicate, classWord_nil] using h

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
private theorem sClass_order (i : Fin n) : sClass g i ^ d = 1 := by
  have h := (classWord_eq_iff_derives g (List.replicate d (.S i)) []).mpr
    (.rule (Or.inr (Figure1Rule.C1 i)))
  simpa only [classWord_replicate, classWord_nil] using h

private theorem hClass_inv (i : Fin n) : (hClass g i)⁻¹ = hClass g i ^ 3 := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ', hClass_four]

private theorem hClass_sq_inv (i : Fin n) : (hClass g i ^ 2)⁻¹ = hClass g i ^ 2 := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_add]
  exact hClass_four g i

/-- The displayed S inverse is its actual inverse in the syntactic quotient. -/
theorem classWord_Sexp_neg_one (i : Fin n) :
    classWord g (Sexp i (-1 : ZMod d)) = (classWord g [.S i])⁻¹ := by
  have h := classWord_inverseWord g [.S i]
  simpa only [inverseWord_cons, inverseWord_nil, List.nil_append, Gate.inverseWord,
    Sexp, val_neg_one_pred] using h

private theorem zClass_expand (i : Fin n) :
    zClass g i = (hClass g i ^ 2 * sClass g i * hClass g i ^ 2) * (sClass g i)⁻¹ := by
  change (hClass g i * hClass g i * sClass g i * hClass g i * hClass g i) *
    classWord g (Sexp i (-1 : ZMod d)) = _
  rw [classWord_Sexp_neg_one]
  simp only [pow_two, mul_assoc, sClass]

private theorem xClass_expand (i : Fin n) :
    xClass g i = hClass g i * sClass g i * hClass g i ^ 2 * (sClass g i)⁻¹ * hClass g i := by
  change (hClass g i * sClass g i * hClass g i * hClass g i) *
    classWord g (Sexp i (-1 : ZMod d)) * hClass g i = _
  rw [classWord_Sexp_neg_one]
  simp only [pow_two, mul_assoc, sClass]

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
/-- C5 makes S commute with its H-squared conjugate. -/
private theorem sClass_commute_conjugate (i : Fin n) :
    Commute (sClass g i) (hClass g i ^ 2 * sClass g i * hClass g i ^ 2) := by
  have h := (classWord_eq_iff_derives g _ _).mpr
    (show Derives g [.S i,.H i,.H i,.S i,.H i,.H i]
      [.H i,.H i,.S i,.H i,.H i,.S i] from .rule (Or.inr (Figure1Rule.C5 i)))
  change sClass g i * (hClass g i ^ 2 * sClass g i * hClass g i ^ 2) =
    (hClass g i ^ 2 * sClass g i * hClass g i ^ 2) * sClass g i
  change sClass g i * hClass g i * hClass g i * sClass g i * hClass g i * hClass g i =
    hClass g i * hClass g i * sClass g i * hClass g i * hClass g i * sClass g i at h
  simpa only [pow_two, mul_assoc] using h

/-- Z commutes with S in the syntactic quotient, using C5. -/
theorem classWord_Z_commute_S (i : Fin n) :
    Commute (classWord g (Z (d := d) i)) (classWord g [.S i]) := by
  change Commute (zClass g i) (sClass g i)
  rw [zClass_expand]
  exact (sClass_commute_conjugate g i).symm.mul_left (Commute.refl _).inv_left

/-- The derived Z word has order dividing d in the syntactic quotient. -/
theorem classWord_Z_order (i : Fin n) : classWord g (Z (d := d) i) ^ d = 1 := by
  change zClass g i ^ d = 1
  rw [zClass_expand, ((sClass_commute_conjugate g i).symm.inv_right).mul_pow,
    inv_pow, sClass_order, inv_one, mul_one]
  have hp : hClass g i ^ 2 * sClass g i * hClass g i ^ 2 =
      hClass g i ^ 2 * sClass g i * (hClass g i ^ 2)⁻¹ := by rw [hClass_sq_inv]
  rw [hp, conj_pow, sClass_order, mul_one, mul_inv_cancel]

/-- T2 and T3 already give X = H^-1 Z H using the derived H fourth-order rule. -/
theorem classWord_X_conjugate_Z (i : Fin n) :
    classWord g (X (d := d) i) =
      (classWord g [.H i])⁻¹ * classWord g (Z (d := d) i) * classWord g [.H i] := by
  change xClass g i = (hClass g i)⁻¹ * zClass g i * hClass g i
  rw [xClass_expand, zClass_expand, hClass_inv]
  have hh : hClass g i ^ 3 * hClass g i ^ 2 = hClass g i := by
    rw [← pow_add]
    change hClass g i ^ (4+1) = _
    rw [pow_succ, hClass_four, one_mul]
  simp only [← mul_assoc, hh]

/-- The derived X word has order dividing d by conjugation of Z. -/
theorem classWord_X_order (i : Fin n) : classWord g (X (d := d) i) ^ d = 1 := by
  rw [classWord_X_conjugate_Z]
  have hconj : (classWord g [.H i])⁻¹ * classWord g (Z (d := d) i) * classWord g [.H i] =
      (classWord g [.H i])⁻¹ * classWord g (Z (d := d) i) * ((classWord g [.H i])⁻¹)⁻¹ := by
    rw [inv_inv]
  rw [hconj, conj_pow, classWord_Z_order, mul_one, mul_inv_cancel]

/-- The basic Fourier pushing rule HX=ZH holds in the actual presented group. -/
theorem classWord_HX_eq_ZH (i : Fin n) :
    classWord g [.H i] * classWord g (X (d := d) i) =
      classWord g (Z (d := d) i) * classWord g [.H i] := by
  rw [classWord_X_conjugate_Z]
  group

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
/-- An actual Figure 1 derivation commuting the expanded Z word past S. -/
theorem derives_Z_S_commute (hd : Odd d) (hg : orderOf g = d-1) (i : Fin n) :
    Derives g (Z (d := d) i ++ [.S i]) ([.S i] ++ Z (d := d) i) := by
  letI : Fact (Odd d) := ⟨hd⟩
  letI : Fact (orderOf g = d-1) := ⟨hg⟩
  apply (classWord_eq_iff_derives g _ _).mp
  simpa only [classWord_append] using (classWord_Z_commute_S g i).eq

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
/-- An actual Figure 1 derivation of Z^d=1 for the expanded primitive word. -/
theorem derives_Z_order (hd : Odd d) (hg : orderOf g = d-1) (i : Fin n) :
    Derives g (power (Z (d := d) i) d) [] := by
  letI : Fact (Odd d) := ⟨hd⟩
  letI : Fact (orderOf g = d-1) := ⟨hg⟩
  apply (classWord_eq_iff_derives g _ _).mp
  rw [classWord_power, classWord_Z_order, classWord_nil]

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
/-- An actual Figure 1 derivation of X^d=1 for the expanded primitive word. -/
theorem derives_X_order (hd : Odd d) (hg : orderOf g = d-1) (i : Fin n) :
    Derives g (power (X (d := d) i) d) [] := by
  letI : Fact (Odd d) := ⟨hd⟩
  letI : Fact (orderOf g = d-1) := ⟨hg⟩
  apply (classWord_eq_iff_derives g _ _).mp
  rw [classWord_power, classWord_X_order, classWord_nil]

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
/-- T2 equals H cubed, then T3, then H by explicit syntactic derivability. -/
theorem derives_X_conjugate_Z (hd : Odd d) (hg : orderOf g = d-1) (i : Fin n) :
    Derives g (X (d := d) i) (List.replicate 3 (.H i) ++ Z (d := d) i ++ [.H i]) := by
  letI : Fact (Odd d) := ⟨hd⟩
  letI : Fact (orderOf g = d-1) := ⟨hg⟩
  apply (classWord_eq_iff_derives g _ _).mp
  rw [classWord_append, classWord_append, classWord_replicate]
  change xClass g i = hClass g i ^ 3 * zClass g i * hClass g i
  rw [← hClass_inv]
  exact classWord_X_conjugate_Z g i

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
/-- The expanded-word Fourier pushing relation is derived, not inferred from matrices. -/
theorem derives_HX_eq_ZH (hd : Odd d) (hg : orderOf g = d-1) (i : Fin n) :
    Derives g ([.H i] ++ X (d := d) i) (Z (d := d) i ++ [.H i]) := by
  letI : Fact (Odd d) := ⟨hd⟩
  letI : Fact (orderOf g = d-1) := ⟨hg⟩
  apply (classWord_eq_iff_derives g _ _).mp
  simpa only [classWord_append] using classWord_HX_eq_ZH g i

end QuditClifford.Circuit
