import QuditClifford.ScalarCompleteness
import QuditClifford.CircuitAdjoints

/-!
# Syntactic inverses from Figure 1

These are contextual derivations from the stated rules, rather than applications
of matrix equality in the reverse direction.
-/

noncomputable section
namespace QuditClifford
namespace Circuit

variable {d n : ℕ} [NeZero d]

@[simp] theorem power_zero (w : Word n) : power w 0 = [] := rfl
@[simp] theorem power_succ (w : Word n) (k : ℕ) : power w (k+1) = w ++ power w k := by
  simp [power, List.replicate_succ]

theorem power_add (w : Word n) (k l : ℕ) : power w (k+l) = power w k ++ power w l := by
  simp only [power, List.replicate_add, List.flatten_append]

theorem power_mul (w : Word n) (k l : ℕ) : power (power w k) l = power w (k*l) := by
  induction l with
  | zero => simp
  | succ l ih => rw [power_succ, ih, Nat.mul_succ, Nat.add_comm, power_add]

/-- Contextual rewriting is compatible with arbitrary word powers. -/
theorem derives_power (g : (ZMod d)ˣ) {u v : Word n} (h : Derives g u v) (k : ℕ) :
    Derives g (power u k) (power v k) := by
  induction k with
  | zero => exact .refl _
  | succ k ih => simpa only [power_succ] using h.append ih

/-- C3 at exponent zero removes the expanded multiplier at one. -/
theorem derives_multiplier_one (g : (ZMod d)ˣ) (i : Fin n) :
    Derives g (multiplier (d := d) i 1) [] := by
  have h : Derives g (power (multiplier i g) (0 : Fin d).val)
      (multiplier i (g^(0 : Fin d).val)) := .rule (Or.inr (Figure1Rule.C3 i 0))
  simpa only [Fin.val_zero, pow_zero, power_zero] using h.symm

/-- C3 at exponent d-1 supplies the full generator cycle. -/
theorem derives_multiplier_cycle (g : (ZMod d)ˣ) (hg : orderOf g = d-1) (i : Fin n) :
    Derives g (power (multiplier i g) (d-1)) [] := by
  have hlt : d-1 < d := Nat.sub_lt (NeZero.pos d) (by decide)
  have h : Derives g (power (multiplier i g) (d-1)) (multiplier i (g^(d-1))) :=
    .rule (Or.inr (Figure1Rule.C3 i ⟨d-1,hlt⟩))
  have hp : g ^ (d-1) = 1 := by rw [← hg, pow_orderOf_eq_one]
  rw [hp] at h
  exact h.trans (derives_multiplier_one g i)

/-- Scalar primitives commute with every letter by the wiring rules. -/
theorem derives_scalar_gate_commute (g : (ZMod d)ˣ) (a : Gate n) :
    Derives g [.scalar,a] [a,.scalar] :=
  .rule (Or.inl (Structural.disjoint .scalar a (by simp [Gate.support])))

/-- Scalar primitives commute with arbitrary words using contextual rewrites. -/
theorem derives_scalar_one_commute (g : (ZMod d)ˣ) (w : Word n) :
    Derives g ([.scalar] ++ w) (w ++ [.scalar]) := by
  induction w with
  | nil => exact .refl _
  | cons a w ih =>
    have h₁ := (derives_scalar_gate_commute g a).append_right w
    have h₂ := ih.append_left [a]
    simpa only [List.cons_append, List.nil_append, List.append_assoc] using h₁.trans h₂

/-- Arbitrary scalar words commute with arbitrary circuits by wiring coherence alone. -/
theorem derives_scalar_commute (g : (ZMod d)ˣ) (k : ℕ) (w : Word n) :
    Derives g (scalar k ++ w) (w ++ scalar k) := by
  induction k with
  | zero => simpa only [scalar, List.replicate_zero, List.nil_append, List.append_nil] using
      (Presentation.Derives.refl (R := Rules g) w)
  | succ k ih =>
    have h₁ := ih.append_left [.scalar]
    have h₂ := (derives_scalar_one_commute g w).append_right (scalar k)
    simpa [scalar, List.replicate_succ, List.append_assoc] using h₁.trans h₂

variable [Fact d.Prime]

omit [NeZero d] in
/-- A multiplicative generator reaches -1 halfway through its cycle. -/
theorem generator_half_pow (hd : Odd d) (g : (ZMod d)ˣ) (hg : orderOf g = d-1) :
    g ^ ((d-1)/2) = -1 := by
  have hd3 : 3 ≤ d := by
    have hp := (Fact.out : d.Prime).two_le
    have ho := Nat.odd_iff.mp hd
    omega
  have hhalf : (d-1)/2 * 2 = d-1 := by
    have ho := Nat.odd_iff.mp hd
    omega
  have hs : (g ^ ((d-1)/2)) ^ 2 = 1 := by
    rw [← pow_mul, hhalf, ← hg, pow_orderOf_eq_one]
  have hn : g ^ ((d-1)/2) ≠ 1 :=
    pow_ne_one_of_lt_orderOf (by omega) (by rw [hg]; omega)
  have hval : ((g : ZMod d) ^ ((d-1)/2)) ^ 2 = 1 := by
    simpa using congrArg (fun a : (ZMod d)ˣ => (a : ZMod d)) hs
  rcases sq_eq_one_iff.mp hval with h | h
  · exact (hn (Units.ext (by simpa using h))).elim
  · apply Units.ext
    simpa using h

/-- Two expanded negation multipliers cancel by the finite C3 family. -/
theorem derives_multiplier_neg_one_sq (hd : Odd d) (g : (ZMod d)ˣ)
    (hg : orderOf g = d-1) (i : Fin n) :
    Derives g (multiplier (d := d) i (-1) ++ multiplier (d := d) i (-1)) [] := by
  have hlt : (d-1)/2 < d := by have hp := NeZero.pos d; omega
  have hhalf : (d-1)/2 + (d-1)/2 = d-1 := by
    have ho := Nat.odd_iff.mp hd
    omega
  have h : Derives g (power (multiplier i g) ((d-1)/2))
      (multiplier i (g ^ ((d-1)/2))) :=
    .rule (Or.inr (Figure1Rule.C3 i ⟨_,hlt⟩))
  rw [generator_half_pow hd g hg] at h
  have h₂ := h.symm.append h.symm
  rw [← power_add, hhalf] at h₂
  exact h₂.trans (derives_multiplier_cycle g hg i)

/-- C2, C3, scalar coherence and C0 derive the actual fourth-order H relation. -/
theorem derives_H_four (hd : Odd d) (g : (ZMod d)ˣ) (hg : orderOf g = d-1) (i : Fin n) :
    Derives g (List.replicate 4 (.H i)) [] := by
  let k := d * ((d-1)/2)
  let m := multiplier (d := d) i (-1)
  have h₂ : Derives g [.H i,.H i] (scalar k ++ m) :=
    .rule (Or.inr (Figure1Rule.C2 i))
  have hstart := h₂.append h₂
  have hswap := (derives_scalar_commute g k m).symm.context (scalar k) m
  have hscalar : Derives (n := n) g (scalar k ++ scalar k) [] := by
    have heq : (k+k) % (2*d) = 0 % (2*d) := by
      have hk : k+k = (2*d)*((d-1)/2) := by dsimp [k]; ring
      rw [hk, Nat.mul_mod_right]
      simp
    simpa only [scalar, List.replicate_add, List.replicate_zero] using
      scalar_derives_of_mod_eq (n := n) g (k+k) 0 heq
  have hend := hscalar.append (derives_multiplier_neg_one_sq hd g hg i)
  have hmiddle : Derives g (scalar k ++ m ++ (scalar k ++ m))
      ((scalar k ++ scalar k) ++ (m ++ m)) := by
    simpa only [List.append_assoc] using hswap
  simpa only [List.replicate_succ, List.replicate_zero, List.cons_append, List.nil_append, m]
    using hstart.trans (hmiddle.trans hend)

/-- An order relation gives both positive-power cancellation orientations. -/
private theorem derives_replicate_cancel (g : (ZMod d)ˣ) (a : Gate n) (m : ℕ) (hm : 1 ≤ m)
    (h : Derives g (List.replicate m a) []) :
    Derives g ([a] ++ List.replicate (m-1) a) [] ∧
      Derives g (List.replicate (m-1) a ++ [a]) [] := by
  have hl : [a] ++ List.replicate (m-1) a = List.replicate m a := by
    change List.replicate 1 a ++ List.replicate (m-1) a = _
    rw [← List.replicate_add, Nat.add_sub_of_le hm]
  have hr : List.replicate (m-1) a ++ [a] = List.replicate m a := by
    change List.replicate (m-1) a ++ List.replicate 1 a = _
    rw [← List.replicate_add, Nat.sub_add_cancel hm]
  exact ⟨hl.symm ▸ h, hr.symm ▸ h⟩

/-- Every primitive gate cancels its explicit inverse word using only Figure 1. -/
theorem derives_gate_inverse (hd : Odd d) (g : (ZMod d)ˣ) (hg : orderOf g = d-1)
    (a : Gate n) :
    Derives g ([a] ++ a.inverseWord d) [] ∧ Derives g (a.inverseWord d ++ [a]) [] := by
  cases a with
  | scalar =>
    exact derives_replicate_cancel g .scalar (2*d) (by have hp := NeZero.pos d; omega)
      (.rule (Or.inr Figure1Rule.C0))
  | H i =>
    exact derives_replicate_cancel g (.H i) 4 (by decide) (derives_H_four hd g hg i)
  | S i =>
    exact derives_replicate_cancel g (.S i) d (NeZero.pos d)
      (.rule (Or.inr (Figure1Rule.C1 i)))
  | CZ i j h =>
    exact derives_replicate_cancel g (.CZ i j h) d (NeZero.pos d)
      (.rule (Or.inr (Figure1Rule.C6 i j h)))

/-- A word followed by its inverse word cancels by actual contextual derivations. -/
theorem derives_append_inverseWord (hd : Odd d) (g : (ZMod d)ˣ) (hg : orderOf g = d-1)
    (w : Word n) : Derives g (w ++ inverseWord d w) [] := by
  induction w with
  | nil => exact .refl _
  | cons a w ih =>
    have h₁ := ih.context [a] (a.inverseWord d)
    have h₂ := (derives_gate_inverse hd g hg a).1
    simpa only [inverseWord_cons, List.append_assoc, List.cons_append, List.nil_append] using
      h₁.trans h₂

/-- The inverse word also cancels when placed before the original word. -/
theorem derives_inverseWord_append (hd : Odd d) (g : (ZMod d)ˣ) (hg : orderOf g = d-1)
    (w : Word n) : Derives g (inverseWord d w ++ w) [] := by
  induction w with
  | nil => exact .refl _
  | cons a w ih =>
    have h₁ := ((derives_gate_inverse hd g hg a).2).context (inverseWord d w) w
    have h₁' : Derives g (inverseWord d (a::w) ++ (a::w)) (inverseWord d w ++ w) := by
      simpa only [inverseWord_cons, List.append_assoc, List.cons_append,
        List.nil_append, List.append_nil] using h₁
    exact h₁'.trans ih

/-- Common right contexts can be cancelled syntactically once inverses have been derived. -/
theorem derives_cancel_right (hd : Odd d) (g : (ZMod d)ˣ) (hg : orderOf g = d-1)
    {u v w : Word n} (h : Derives g (u ++ w) (v ++ w)) : Derives g u v := by
  have hc := derives_append_inverseWord hd g hg w
  have hu : Derives g (u ++ (w ++ inverseWord d w)) u := by
    simpa only [List.append_nil] using hc.append_left u
  have hv : Derives g (v ++ (w ++ inverseWord d w)) v := by
    simpa only [List.append_nil] using hc.append_left v
  have hm : Derives g (u ++ (w ++ inverseWord d w)) (v ++ (w ++ inverseWord d w)) := by
    simpa only [List.append_assoc] using h.append_right (inverseWord d w)
  exact hu.symm.trans (hm.trans hv)

/-- Common left contexts can likewise be cancelled using derived inverse words. -/
theorem derives_cancel_left (hd : Odd d) (g : (ZMod d)ˣ) (hg : orderOf g = d-1)
    {u v w : Word n} (h : Derives g (w ++ u) (w ++ v)) : Derives g u v := by
  have hc := derives_inverseWord_append hd g hg w
  have hu : Derives g (inverseWord d w ++ (w ++ u)) u := by
    simpa only [List.append_assoc, List.nil_append] using hc.append_right u
  have hv : Derives g (inverseWord d w ++ (w ++ v)) v := by
    simpa only [List.append_assoc, List.nil_append] using hc.append_right v
  exact hu.symm.trans ((h.append_left (inverseWord d w)).trans hv)

end Circuit
end QuditClifford
