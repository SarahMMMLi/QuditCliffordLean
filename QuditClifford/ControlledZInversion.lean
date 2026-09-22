import QuditClifford.TwoWirePauliRewrites

/-!
# Fourier-square inversion of controlled Z

C9 iterated to the half-cycle of the primitive multiplier gives inversion
of controlled Z. C3 identifies that half-cycle with the negation multiplier,
and C2 transfers its action to the square of H. All equalities are in the
actual Figure 1 word quotient.
-/

noncomputable section
namespace QuditClifford.Circuit

/-- Iterating a relation that transports a generator to one of its powers. -/
theorem mul_pow_transport {G : Type*} [Monoid G] {c m : G} {a : ℕ}
    (hm : c*m = m*c^a) (k : ℕ) : c*m^k = m^k*c^(a^k) := by
  have hp (b : ℕ) : c^b*m = m*(c^a)^b :=
    ((show SemiconjBy m (c^a) c from hm.symm).pow_right b).symm
  induction k with
  | zero => simp
  | succ k hk =>
    calc
      c*m^(k+1) = (c*m^k)*m := by rw [pow_succ, mul_assoc]
      _ = (m^k*c^(a^k))*m := by rw [hk]
      _ = m^k*(m*(c^a)^(a^k)) := by rw [mul_assoc, hp]
      _ = m^(k+1)*c^(a^(k+1)) := by
        rw [← mul_assoc, ← pow_succ, ← pow_mul, pow_succ a k, Nat.mul_comm a]

variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

set_option linter.unusedSectionVars false in
omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
/-- The controlled-Z order relation, directly from C6. -/
theorem classWord_CZ_order (i j : Fin n) (hij : i ≠ j) :
    classWord g [.CZ i j hij] ^ d = 1 := by
  have he := (classWord_eq_iff_derives g _ _).mpr
    (show Derives g (List.replicate d (.CZ i j hij)) [] from
      .rule (Or.inr (Figure1Rule.C6 i j hij)))
  simpa only [classWord_replicate, classWord_nil] using he

private theorem generator_half_val :
    (g : ZMod d).val ^ ((d-1)/2) % d = d-1 := by
  have hres : (((g : ZMod d).val ^ ((d-1)/2) : ℕ) : ZMod d) = -1 := by
    simp only [Nat.cast_pow, ZMod.natCast_zmod_val]
    exact congrArg (fun a : (ZMod d)ˣ => (a : ZMod d))
      (generator_half_pow (show Odd d from Fact.out) g Fact.out)
  have hv := congrArg ZMod.val hres
  rw [ZMod.val_natCast] at hv
  have hn : (-1 : ZMod d).val = d-1 := by
    cases d with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ k => simp
  exact hv.trans hn

/-- C9 at the half-cycle of the primitive multiplier, evaluated using C3. -/
theorem classWord_CZ_negation_multiplier (i j : Fin n) (hij : i ≠ j) :
    classWord g [.CZ i j hij] * classWord g (multiplier (d := d) i (-1)) =
      classWord g (multiplier (d := d) i (-1)) *
        (classWord g [.CZ i j hij])⁻¹ := by
  have hlt : (d-1)/2 < d := by have hp := NeZero.pos d; omega
  have hm := (classWord_eq_iff_derives g _ _).mpr
    (show Derives g (power (multiplier i g) ((d-1)/2))
      (multiplier i (g^((d-1)/2))) from
      .rule (Or.inr (Figure1Rule.C3 i ⟨_, hlt⟩)))
  rw [classWord_power, generator_half_pow (show Odd d from Fact.out) g Fact.out] at hm
  have ht := mul_pow_transport (classWord_CZ_multiplier g i j hij) ((d-1)/2)
  rw [hm, pow_eq_pow_mod _ (classWord_CZ_order g i j hij), generator_half_val] at ht
  have hi : (classWord g [.CZ i j hij])^(d-1) = (classWord g [.CZ i j hij])⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ]
    have hd : d-1+1=d := by have hp := NeZero.pos d; omega
    rw [hd, classWord_CZ_order]
  rwa [hi] at ht

set_option linter.unusedSectionVars false in
omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
private theorem scalar_commute (k : ℕ) (q : PresentedCircuit g n) :
    Commute (classWord g (scalar k)) q := by
  obtain ⟨w, rfl⟩ := classWord_surjective g q
  have he := (classWord_eq_iff_derives g _ _).mpr (derives_scalar_commute g k w)
  simpa only [classWord_append] using he

/-- Conjugating controlled Z by H squared on its first wire inverts it. -/
theorem classWord_H_sq_conjugate_CZ_left (i j : Fin n) (hij : i ≠ j) :
    (classWord g [.H i])^2 * classWord g [.CZ i j hij] *
        ((classWord g [.H i])^2)⁻¹ = (classWord g [.CZ i j hij])⁻¹ := by
  let q := (classWord g [.H i])^2
  let c := classWord g [.CZ i j hij]
  have hq : q = classWord g (scalar (d*((d-1)/2))) *
      classWord g (multiplier (d := d) i (-1)) := by
    have he := (classWord_eq_iff_derives g _ _).mpr
      (show Derives g [.H i,.H i]
        (scalar (d*((d-1)/2)) ++ multiplier (d := d) i (-1)) from
        .rule (Or.inr (Figure1Rule.C2 i)))
    change classWord g [.H i] * classWord g [.H i] = _ at he
    simpa only [q, pow_two] using he
  have hq2 : q*q = 1 := by
    have he := (classWord_eq_iff_derives g _ _).mpr
      (derives_H_four (show Odd d from Fact.out) g Fact.out i)
    simpa only [classWord_replicate, classWord_nil, q, ← pow_add] using he
  have hqi : q⁻¹ = q := inv_eq_of_mul_eq_one_right hq2
  have hcq : c*q = q*c⁻¹ := by
    rw [hq, ← mul_assoc, (scalar_commute g (d*((d-1)/2)) c).eq.symm,
      mul_assoc, classWord_CZ_negation_multiplier, ← mul_assoc]
  change q*c*q⁻¹ = c⁻¹
  calc
    q*c*q⁻¹ = q*(c*q) := by rw [hqi, mul_assoc]
    _ = q*(q*c⁻¹) := by rw [hcq]
    _ = c⁻¹ := by rw [← mul_assoc, hq2, one_mul]

/-- Conjugating controlled Z by H squared on its second wire inverts it. -/
theorem classWord_H_sq_conjugate_CZ_right (i j : Fin n) (hij : i ≠ j) :
    (classWord g [.H j])^2 * classWord g [.CZ i j hij] *
        ((classWord g [.H j])^2)⁻¹ = (classWord g [.CZ i j hij])⁻¹ := by
  rw [classWord_CZ_symmetry g i j hij]
  exact classWord_H_sq_conjugate_CZ_left g j i hij.symm

end QuditClifford.Circuit
