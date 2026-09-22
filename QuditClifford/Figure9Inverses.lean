import QuditClifford.Figure9Syntax
import QuditClifford.AdjacentCircuitInverses
import QuditClifford.AdjacentNormalCircuit

/-! # Syntactic inverses from the eighteen Figure 9 equations

The finite multiplier-cycle equations give Fourier order four. Primitive
cancellation and the group structure require no additional deletion relation.
-/
noncomputable section
namespace QuditClifford.Circuit
variable {d n : ℕ} [NeZero d]

/-- Scalar erasure preserves a derivation because generating equations contain no scalar letters. -/
theorem Figure9Derives.eraseScalar (g : (ZMod d)ˣ) {u v : Word n}
    (h : Figure9Derives g u v) :
    Figure9Derives g (Circuit.eraseScalar u) (Circuit.eraseScalar v) := by
  induction h with
  | refl w => exact .refl _
  | rule h => rw [h.2.2.2.1, h.2.2.2.2]; exact .rule h
  | symm h ih => exact ih.symm
  | trans h k ih ik => exact ih.trans ik
  | context l r h ih =>
      simpa only [eraseScalar_append] using
        ih.context (Circuit.eraseScalar l) (Circuit.eraseScalar r)

/-- Contextual Figure 9 derivations are compatible with positive powers. -/
theorem figure9Derives_power (g : (ZMod d)ˣ) {u v : Word n}
    (h : Figure9Derives g u v) (k : ℕ) :
    Figure9Derives g (power u k) (power v k) := by
  induction k with
  | zero => exact .refl _
  | succ k ih => simpa only [power_succ] using h.append ih

/-- The finite C3 family exposes the generator's selected powers. -/
theorem figure9Derives_multiplier_generator_pow (g : (ZMod d)ˣ) (i : Fin n)
    (k : Fin d) :
    Figure9Derives g (power (eraseScalar (multiplier i g)) k.val)
      (eraseScalar (multiplier i (g^k.val))) := by
  apply Presentation.Derives.rule
  refine ⟨Or.inr (Figure9Rule.C3 i k),
    (isAdjacentWord_multiplier i g).eraseScalar.power k.val,
    (isAdjacentWord_multiplier i (g^k.val)).eraseScalar, ?_, ?_⟩
  all_goals simp

/-- C3 at zero identifies the expanded multiplier at one with the identity. -/
theorem figure9Derives_multiplier_one (g : (ZMod d)ˣ) (i : Fin n) :
    Figure9Derives g (eraseScalar (multiplier (d := d) i 1)) [] := by
  simpa only [Fin.val_zero, pow_zero, power_zero] using
    (figure9Derives_multiplier_generator_pow g i 0).symm

/-- C3 at d-1 is the complete generator cycle. -/
theorem figure9Derives_multiplier_cycle (g : (ZMod d)ˣ)
    (hg : orderOf g = d-1) (i : Fin n) :
    Figure9Derives g (power (eraseScalar (multiplier i g)) (d-1)) [] := by
  have hlt : d-1 < d := Nat.sub_lt (NeZero.pos d) (by decide)
  have h := figure9Derives_multiplier_generator_pow g i ⟨d-1,hlt⟩
  have hp : g^(d-1) = 1 := by rw [← hg, pow_orderOf_eq_one]
  change Figure9Derives g (power (eraseScalar (multiplier i g)) (d-1))
    (eraseScalar (multiplier i (g^(d-1)))) at h
  rw [hp] at h
  exact h.trans (figure9Derives_multiplier_one g i)

variable [Fact d.Prime]

/-- The midpoint multiplier squares to the identity using C3 alone. -/
theorem figure9Derives_multiplier_neg_one_sq (hd : Odd d) (g : (ZMod d)ˣ)
    (hg : orderOf g = d-1) (i : Fin n) :
    Figure9Derives g
      (eraseScalar (multiplier (d := d) i (-1)) ++ eraseScalar (multiplier (d := d) i (-1))) [] := by
  have hlt : (d-1)/2 < d := by have hp := NeZero.pos d; omega
  have hhalf : (d-1)/2 + (d-1)/2 = d-1 := by
    have ho := Nat.odd_iff.mp hd
    omega
  have h := figure9Derives_multiplier_generator_pow g i ⟨(d-1)/2,hlt⟩
  change Figure9Derives g (power (eraseScalar (multiplier i g)) ((d-1)/2))
    (eraseScalar (multiplier i (g^((d-1)/2)))) at h
  rw [generator_half_pow hd g hg] at h
  have h₂ := h.symm.append h.symm
  rw [← power_add, hhalf] at h₂
  exact h₂.trans (figure9Derives_multiplier_cycle g hg i)

/-- Fourier order four follows from C2 and the finite C3 family. -/
theorem figure9Derives_H_four (hd : Odd d) (g : (ZMod d)ˣ)
    (hg : orderOf g = d-1) (i : Fin n) :
    Figure9Derives g (List.replicate 4 (.H i)) [] := by
  have h : Figure9Derives g [.H i,.H i] (eraseScalar (multiplier (d := d) i (-1))) := by
    apply Presentation.Derives.rule
    refine ⟨Or.inr (Figure9Rule.C2 i), by simp,
      (isAdjacentWord_multiplier i (-1)).eraseScalar, ?_, ?_⟩
    all_goals simp
  simpa only [List.replicate_succ, List.replicate_zero, List.cons_append, List.nil_append]
    using (h.append h).trans (figure9Derives_multiplier_neg_one_sq hd g hg i)

private theorem figure9Derives_replicate_cancel (g : (ZMod d)ˣ) (a : Gate n)
    (m : ℕ) (hm : 1 ≤ m) (h : Figure9Derives g (List.replicate m a) []) :
    Figure9Derives g ([a] ++ List.replicate (m-1) a) [] ∧
      Figure9Derives g (List.replicate (m-1) a ++ [a]) [] := by
  have hl : [a] ++ List.replicate (m-1) a = List.replicate m a := by
    change List.replicate 1 a ++ List.replicate (m-1) a = _
    rw [← List.replicate_add, Nat.add_sub_of_le hm]
  have hr : List.replicate (m-1) a ++ [a] = List.replicate m a := by
    change List.replicate (m-1) a ++ List.replicate 1 a = _
    rw [← List.replicate_add, Nat.sub_add_cancel hm]
  exact ⟨hl.symm ▸ h, hr.symm ▸ h⟩

/-- Erased adjacent primitives cancel their explicit inverse words. -/
theorem figure9Derives_gate_inverse (hd : Odd d) (g : (ZMod d)ˣ)
    (hg : orderOf g = d-1) (a : Gate n) (ha : a.IsAdjacent) :
    Figure9Derives g (eraseScalar ([a] ++ a.inverseWord d)) [] ∧
      Figure9Derives g (eraseScalar (a.inverseWord d ++ [a])) [] := by
  cases a with
  | scalar => simpa [Gate.inverseWord] using
      (show Figure9Derives g ([] : Word n) [] from .refl _)
  | H i =>
    simpa [Gate.inverseWord] using figure9Derives_replicate_cancel g (.H i) 4 (by decide)
      (figure9Derives_H_four hd g hg i)
  | S i =>
    have h : Figure9Derives g (List.replicate d (.S i)) [] := by
      apply Presentation.Derives.rule
      refine ⟨Or.inr (Figure9Rule.C1 i), IsAdjacentWord.replicate ha d,
        isAdjacentWord_nil, ?_, ?_⟩
      all_goals simp
    simpa [Gate.inverseWord] using
      figure9Derives_replicate_cancel g (.S i) d (NeZero.pos d) h
  | CZ i j hne =>
    have h : Figure9Derives g (List.replicate d (.CZ i j hne)) [] := by
      apply Presentation.Derives.rule
      refine ⟨Or.inr (Figure9Rule.C6 i j hne), IsAdjacentWord.replicate ha d,
        isAdjacentWord_nil, ?_, ?_⟩
      all_goals simp
    simpa [Gate.inverseWord] using
      figure9Derives_replicate_cancel g (.CZ i j hne) d (NeZero.pos d) h

/-- The erasure of a word followed by its inverse cancels by Figure 9. -/
theorem figure9Derives_append_inverseWord (hd : Odd d) (g : (ZMod d)ˣ)
    (hg : orderOf g = d-1) (w : Word n) (hw : IsAdjacentWord w) :
    Figure9Derives g (eraseScalar (w ++ inverseWord d w)) [] := by
  induction w with
  | nil => exact .refl _
  | cons a w ih =>
    obtain ⟨ha, hw⟩ := (isAdjacentWord_cons a w).mp hw
    have h₁ := (ih hw).context (eraseScalar [a]) (eraseScalar (a.inverseWord d))
    have h₂ := (figure9Derives_gate_inverse hd g hg a ha).1
    simp only [eraseScalar_append, List.append_nil] at h₁ h₂
    have hh := h₁.trans h₂
    cases a <;> simpa only [inverseWord_cons, eraseScalar_append, eraseScalar,
      List.append_assoc, List.cons_append, List.nil_append, List.append_nil] using hh

/-- The inverse cancels on the left as well. -/
theorem figure9Derives_inverseWord_append (hd : Odd d) (g : (ZMod d)ˣ)
    (hg : orderOf g = d-1) (w : Word n) (hw : IsAdjacentWord w) :
    Figure9Derives g (eraseScalar (inverseWord d w ++ w)) [] := by
  induction w with
  | nil => exact .refl _
  | cons a w ih =>
    obtain ⟨ha, hw⟩ := (isAdjacentWord_cons a w).mp hw
    have h₁ := ((figure9Derives_gate_inverse hd g hg a ha).2).context
      (eraseScalar (inverseWord d w)) (eraseScalar w)
    have h₁' : Figure9Derives g (eraseScalar (inverseWord d (a::w) ++ (a::w)))
        (eraseScalar (inverseWord d w ++ w)) := by
      cases a <;> simpa only [inverseWord_cons, eraseScalar_append, eraseScalar,
        List.append_assoc, List.cons_append, List.nil_append, List.append_nil] using h₁
    exact h₁'.trans (ih hw)

/-- A common adjacent left context cancels after scalar erasure. -/
theorem figure9Derives_cancel_left (hd : Odd d) (g : (ZMod d)ˣ)
    (hg : orderOf g = d-1) {u v w : Word n} (hw : IsAdjacentWord w)
    (h : Figure9Derives g (eraseScalar (w ++ u)) (eraseScalar (w ++ v))) :
    Figure9Derives g (eraseScalar u) (eraseScalar v) := by
  have hc := figure9Derives_inverseWord_append hd g hg w hw
  have hu : Figure9Derives g
      (eraseScalar (inverseWord d w) ++ eraseScalar (w ++ u)) (eraseScalar u) := by
    simpa only [eraseScalar_append, List.append_assoc, List.nil_append]
      using hc.append_right (eraseScalar u)
  have hv : Figure9Derives g
      (eraseScalar (inverseWord d w) ++ eraseScalar (w ++ v)) (eraseScalar v) := by
    simpa only [eraseScalar_append, List.append_assoc, List.nil_append]
      using hc.append_right (eraseScalar v)
  exact hu.symm.trans ((h.append_left (eraseScalar (inverseWord d w))).trans hv)

/-- Taking inverse words respects the eighteen-rule equivalence relation. -/
theorem figure9Derives_inverseWord (hd : Odd d) (g : (ZMod d)ˣ)
    (hg : orderOf g = d-1) {u v : Word n} (hu : IsAdjacentWord u)
    (hv : IsAdjacentWord v)
    (h : Figure9Derives g (eraseScalar u) (eraseScalar v)) :
    Figure9Derives g (eraseScalar (inverseWord d u)) (eraseScalar (inverseWord d v)) := by
  apply figure9Derives_cancel_left hd g hg hu
  have h₁ := figure9Derives_append_inverseWord hd g hg u hu
  have h₂ := figure9Derives_append_inverseWord hd g hg v hv
  have h₃ := h.symm.append_right (eraseScalar (inverseWord d v))
  simp only [eraseScalar_append] at h₁ h₂ ⊢
  exact h₁.trans (h₂.symm.trans h₃)

end QuditClifford.Circuit
