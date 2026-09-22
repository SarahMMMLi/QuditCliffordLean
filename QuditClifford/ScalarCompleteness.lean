import QuditClifford.CircuitSemantics

/-!
# Exact completeness for the scalar fragment

This is the scalar part of the final lifting argument in Theorem 4.10. It is
proved for the actual primitive `-ω` words using C0, not by assuming a scalar
normal form. It also proves Figure 1 completeness for zero-qudit circuits.
It does not assume or establish projective completeness for positive arities.
-/

noncomputable section
namespace QuditClifford
namespace Circuit

variable {d n : ℕ} [NeZero d]

/-- C0 removes a full period from an arbitrary scalar word. -/
theorem scalar_reduce_period (g : (ZMod d)ˣ) (k : ℕ) :
    Derives (n := n) g (scalar (2*d+k)) (scalar k) := by
  change Presentation.Derives (Rules g) _ _
  have hr : Presentation.Derives (Rules g) (scalar (n := n) (2*d)) [] :=
    .rule (Or.inr (Figure1Rule.C0))
  simpa only [scalar, List.replicate_add, List.nil_append] using hr.append_right (scalar k)

/-- C0 gives a derivation to the unique exponent representative modulo 2d. -/
theorem scalar_normalize (g : (ZMod d)ˣ) (k : ℕ) :
    Derives (n := n) g (scalar k) (scalar (k % (2*d))) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k < 2*d
    · rw [Nat.mod_eq_of_lt hk]
      exact .refl _
    · have hle : 2*d ≤ k := Nat.le_of_not_gt hk
      have hpos : 0 < 2*d := Nat.mul_pos (by decide) (NeZero.pos d)
      have hlt : k - 2*d < k := Nat.sub_lt (lt_of_lt_of_le hpos hle) hpos
      have hstep := scalar_reduce_period (n := n) g (k - 2*d)
      rw [Nat.add_sub_of_le hle] at hstep
      exact hstep.trans (by simpa only [← Nat.mod_eq_sub_mod hle] using ih _ hlt)

/-- Equal residues of scalar exponents give an actual C0 rewrite derivation. -/
theorem scalar_derives_of_mod_eq (g : (ZMod d)ˣ) (k l : ℕ)
    (h : k % (2*d) = l % (2*d)) :
    Derives (n := n) g (scalar k) (scalar l) :=
  (scalar_normalize g k).trans (h ▸ (scalar_normalize g l).symm)

/-- Exact matrix equality of scalar words implies they are interderivable by C0. -/
theorem scalar_complete (hd : Odd d) (g : (ZMod d)ˣ) (k l : ℕ)
    (h : denote d (scalar (n := n) k) = denote d (scalar l)) :
    Derives g (scalar (n := n) k) (scalar l) := by
  have hp : scalarGenerator d ^ k = scalarGenerator d ^ l := by
    have he := congrArg (fun A : QuditOperator d n => A 0 0) h
    simpa [denote_scalar] using he
  have hroot := scalarGenerator_primitive d hd
  have horder : orderOf (scalarGenerator d) = 2*d := hroot.eq_orderOf.symm
  apply scalar_derives_of_mod_eq g k l
  have hpos : 0 < 2*d := Nat.mul_pos (by decide) (NeZero.pos d)
  apply hroot.pow_inj (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos)
  simpa only [← horder, pow_mod_orderOf] using hp

/-- A zero-wire circuit contains only scalar primitives. -/
theorem zero_wire_word (w : Word 0) : w = scalar w.length := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    cases a with
    | scalar => simpa [scalar, List.replicate_succ] using congrArg (List.cons Gate.scalar) ih
    | H i => exact Fin.elim0 i
    | S i => exact Fin.elim0 i
    | CZ i j h => exact Fin.elim0 i

/-- The entire completeness target is proved in arity zero. Higher arities
still require the symplectic/projective normalization arguments. -/
theorem zero_wire_complete (hd : Odd d) (g : (ZMod d)ˣ) : Figure1Complete (n := 0) g := by
  intro a b h
  rw [zero_wire_word a, zero_wire_word b] at h ⊢
  exact scalar_complete hd g _ _ h

private theorem zero_gate_scalar (a : Gate 0) : a = .scalar := by
  cases a with
  | scalar => rfl
  | H i => exact Fin.elim0 i
  | S i => exact Fin.elim0 i
  | CZ i j h => exact Fin.elim0 i

/-- Figure 1 is also exact-sound in arity zero: only C0 has an instance. -/
theorem zero_wire_sound (g : (ZMod d)ˣ) : Figure1Sound (n := 0) g := by
  apply Presentation.sound_derives
  intro a b hr
  rcases hr with hs | hf
  · cases hs with
    | disjoint a b _ => rw [zero_gate_scalar a, zero_gate_scalar b]
    | CZ_symmetry i j h => exact Fin.elim0 i
  · cases hf
    · exact C0_sound
    all_goals exact Fin.elim0 (by assumption : Fin 0)

/-- Complete exact verification of the zero-wire specialization. -/
theorem zero_wire_sound_and_complete (hd : Odd d) (g : (ZMod d)ˣ) :
    Figure1Sound (n := 0) g ∧ Figure1Complete (n := 0) g :=
  ⟨zero_wire_sound g, zero_wire_complete hd g⟩

end Circuit
end QuditClifford
