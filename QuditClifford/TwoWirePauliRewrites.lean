import QuditClifford.PauliWeylRewrites

/-!
# Controlled-Z pushing through the expanded Pauli Z words

C8 and C9 show that CZ commutes with the multiplier conjugate of S. C4
identifies that conjugate with a nonzero power of Z times a power of S.
The previously derived order of Z then removes the nonzero exponent.
Every equality is in the actual Figure 1 word quotient.
-/

noncomputable section
namespace QuditClifford.Circuit

/-- A commutation rule transports across a conjugation that raises the other
factor to a natural power. -/
theorem commute_conjugate_of_mul_eq_mul_pow {G : Type*} [Group G]
    {c m s : G} {k : ℕ} (hm : c*m = m*c^k) (hs : Commute c s) :
    Commute c (m*s*m⁻¹) := by
  show c*(m*s*m⁻¹) = (m*s*m⁻¹)*c
  calc
    _ = (c*m)*s*m⁻¹ := by group
    _ = m*c^k*s*m⁻¹ := by rw [hm]
    _ = m*s*c^k*m⁻¹ := by rw [mul_assoc m (c^k) s, (hs.pow_left k).eq, ← mul_assoc]
    _ = m*s*m⁻¹*(m*c^k)*m⁻¹ := by group
    _ = _ := by rw [← hm]; group

variable {d n : ℕ} [NeZero d] [Fact d.Prime]

omit [NeZero d] in
/-- A nonzero residue power of an element whose order divides the prime d
still generates that element. This is group arithmetic, independent of semantics. -/
theorem pow_residue_mul_inv (q : Type*) [Monoid q] (v : q) (hv : v^d = 1)
    (a : ZMod d) (ha : a ≠ 0) : (v^a.val)^a⁻¹.val = v := by
  have he : (a.val*a⁻¹.val)%d = 1 := by
    rw [← ZMod.val_mul, mul_inv_cancel₀ ha, ZMod.val_one]
  rw [← pow_mul, pow_eq_pow_mod _ hv, he, pow_one]

omit [NeZero d] in
/-- Commutation with one nonzero residue power implies commutation with the
original element when its order divides d. -/
theorem commute_of_commute_residue_power {G : Type*} [Monoid G]
    {u v : G} (hv : v^d = 1) (a : ZMod d) (ha : a ≠ 0)
    (h : Commute u (v^a.val)) : Commute u v := by
  have hp := h.pow_right a⁻¹.val
  rwa [pow_residue_mul_inv G v hv a ha] at hp

variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

omit [NeZero d] in
/-- A primitive generator in odd prime dimension cannot be the unit one. -/
theorem generator_val_ne_one : (g : ZMod d) ≠ 1 := by
  intro he
  have hg : g = 1 := Units.val_eq_one.mp he
  have hord : orderOf g = d-1 := Fact.out
  rw [hg, orderOf_one] at hord
  have hd : Odd d := Fact.out
  have hp := (Fact.out : d.Prime).two_le
  have he2 : d = 2 := by omega
  exact (by decide : ¬Odd 2) (he2 ▸ hd)

omit [NeZero d] in
private theorem correction_ne_zero :
    (1-(g : ZMod d)) * (2*(g : ZMod d)^2)⁻¹ ≠ 0 := by
  have ht : (2 : ZMod d) ≠ 0 := by
    intro he
    have hh := QuditClifford.two_mul_half d (show Odd d from Fact.out)
    simp [he] at hh
  apply mul_ne_zero
  · exact sub_ne_zero.mpr (generator_val_ne_one g).symm
  · exact inv_ne_zero (mul_ne_zero ht (pow_ne_zero 2 g.ne_zero))

set_option linter.unusedSectionVars false in
/-- C8 in the actual word quotient. -/
theorem classWord_CZ_commute_S_left (i j : Fin n) (hij : i ≠ j) :
    Commute (classWord g [.CZ i j hij]) (classWord g [.S i]) := by
  have he := (classWord_eq_iff_derives g _ _).mpr
    (show Derives g [.CZ i j hij,.S i] [.S i,.CZ i j hij] from
      .rule (Or.inr (Figure1Rule.C8 i j hij)))
  exact he

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
/-- C9 in the actual word quotient. -/
theorem classWord_CZ_multiplier (i j : Fin n) (hij : i ≠ j) :
    classWord g [.CZ i j hij] * classWord g (multiplier i g) =
      classWord g (multiplier i g) * classWord g [.CZ i j hij] ^ (g : ZMod d).val := by
  have he := (classWord_eq_iff_derives g _ _).mpr
    (show Derives g ([.CZ i j hij] ++ multiplier i g)
      (multiplier i g ++ List.replicate (g : ZMod d).val (.CZ i j hij)) from
      .rule (Or.inr (Figure1Rule.C9 i j hij)))
  simpa only [classWord_append, classWord_replicate] using he

/-- The exact C4 multiplier conjugate of S. -/
theorem classWord_multiplier_conjugate_S (i : Fin n) :
    classWord g (multiplier i g) * classWord g [.S i] * (classWord g (multiplier i g))⁻¹ =
      classWord g (Z (d := d) i)^((1-(g : ZMod d)) * (2*(g : ZMod d)^2)⁻¹).val *
        classWord g [.S i] ^ ((↑g⁻¹ : ZMod d)^2).val := by
  have he := (classWord_eq_iff_derives g _ _).mpr
    (show Derives g (multiplier i g ++ [.S i])
      (Zexp i ((1-(g : ZMod d)) * (2*(g : ZMod d)^2)⁻¹) ++
        Sexp i ((↑g⁻¹ : ZMod d)^2) ++ multiplier i g) from
      .rule (Or.inr (Figure1Rule.C4 i)))
  simp only [classWord_append, Zexp, Sexp, classWord_power, classWord_replicate] at he
  rw [he]
  group

/-- CZ commutes with the expanded Z on its first wire, derived using C4,C8,C9. -/
theorem classWord_CZ_commute_Z_left (i j : Fin n) (hij : i ≠ j) :
    Commute (classWord g [.CZ i j hij]) (classWord g (Z (d := d) i)) := by
  have hs := classWord_CZ_commute_S_left g i j hij
  have hm := classWord_CZ_multiplier g i j hij
  have hc := commute_conjugate_of_mul_eq_mul_pow hm hs
  rw [classWord_multiplier_conjugate_S] at hc
  have hs' := hs.pow_right ((↑g⁻¹ : ZMod d)^2).val
  have hz := hc.mul_right hs'.inv_right
  simp only [mul_assoc, mul_inv_cancel, mul_one] at hz
  exact commute_of_commute_residue_power (classWord_Z_order g i) _
    (correction_ne_zero g) hz

set_option linter.unusedSectionVars false in
/-- Swapping the named CZ operands is a structural equality of word classes. -/
theorem classWord_CZ_symmetry (i j : Fin n) (hij : i ≠ j) :
    classWord g [.CZ i j hij] = classWord g [.CZ j i hij.symm] :=
  (classWord_eq_iff_derives g _ _).mpr (.rule (Or.inl (Structural.CZ_symmetry i j hij)))

/-- CZ commutes with the expanded Z on its second wire by structural symmetry. -/
theorem classWord_CZ_commute_Z_right (i j : Fin n) (hij : i ≠ j) :
    Commute (classWord g [.CZ i j hij]) (classWord g (Z (d := d) j)) := by
  rw [classWord_CZ_symmetry g i j hij]
  exact classWord_CZ_commute_Z_left g j i hij.symm

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
/-- Actual contextual derivation of first-wire CZ-Z commutation. -/
theorem derives_CZ_Z_left (hd : Odd d) (hg : orderOf g = d-1)
    (i j : Fin n) (hij : i ≠ j) :
    Derives g ([.CZ i j hij] ++ Z (d := d) i) (Z (d := d) i ++ [.CZ i j hij]) := by
  letI : Fact (Odd d) := ⟨hd⟩
  letI : Fact (orderOf g = d-1) := ⟨hg⟩
  apply (classWord_eq_iff_derives g _ _).mp
  simpa only [classWord_append] using (classWord_CZ_commute_Z_left g i j hij).eq

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
/-- Actual contextual derivation of second-wire CZ-Z commutation. -/
theorem derives_CZ_Z_right (hd : Odd d) (hg : orderOf g = d-1)
    (i j : Fin n) (hij : i ≠ j) :
    Derives g ([.CZ i j hij] ++ Z (d := d) j) (Z (d := d) j ++ [.CZ i j hij]) := by
  letI : Fact (Odd d) := ⟨hd⟩
  letI : Fact (orderOf g = d-1) := ⟨hg⟩
  apply (classWord_eq_iff_derives g _ _).mp
  simpa only [classWord_append] using (classWord_CZ_commute_Z_right g i j hij).eq

end QuditClifford.Circuit
