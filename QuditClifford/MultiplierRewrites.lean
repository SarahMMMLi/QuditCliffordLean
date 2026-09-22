import QuditClifford.DerivedPauliRewrites

/-!
# The multiplier subgroup inside the Figure 1 presentation

C3 is only a finite family, indexed by `Fin d`. Its full multiplicative law is
proved below using the generator cycle and the primitive-root hypothesis.
-/
noncomputable section
namespace QuditClifford.Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]

/-- The primitive-root assumption reaches every unit by a natural power. -/
theorem exists_generator_power (g : (ZMod d)ˣ) (hg : orderOf g = d-1)
    (a : (ZMod d)ˣ) : ∃ k : ℕ, g^k = a := by
  have htop : Subgroup.zpowers g = ⊤ := by
    apply (Subgroup.card_eq_iff_eq_top (Subgroup.zpowers g)).mp
    rw [Nat.card_zpowers, hg, Nat.card_eq_fintype_card, ZMod.card_units]
  have hmem : a ∈ Subgroup.zpowers g := by rw [htop]; trivial
  exact mem_powers_iff_mem_zpowers.mpr hmem

/-- C3 extends to all natural powers using its d-1 cycle. -/
theorem classWord_multiplier_gpow (g : (ZMod d)ˣ) (hg : orderOf g = d-1)
    (i : Fin n) (k : ℕ) :
    classWord g (multiplier i (g^k)) = classWord g (multiplier i g)^k := by
  have hd2 := (Fact.out : d.Prime).two_le
  have hr : k % (d-1) < d := lt_trans (Nat.mod_lt _ (by omega)) (by omega)
  have he := (classWord_eq_iff_derives g _ _).mpr
    (show Derives g (power (multiplier i g) (k%(d-1)))
      (multiplier i (g^(k%(d-1)))) from .rule (Or.inr (Figure1Rule.C3 i ⟨_,hr⟩)))
  have hc := (classWord_eq_iff_derives g _ _).mpr (derives_multiplier_cycle g hg i)
  simp only [classWord_power, classWord_nil] at he hc
  rw [← pow_eq_pow_mod k hc] at he
  have hgpow : g^k = g^(k%(d-1)) := by rw [← hg]; exact (pow_mod_orderOf g k).symm
  rw [hgpow]
  exact he.symm

/-- Multipliers multiply correctly in the actual syntactic Figure 1 group. -/
theorem classWord_multiplier_mul (g : (ZMod d)ˣ) (hg : orderOf g = d-1)
    (i : Fin n) (a b : (ZMod d)ˣ) :
    classWord g (multiplier i (a*b)) =
      classWord g (multiplier i a) * classWord g (multiplier i b) := by
  obtain ⟨k,rfl⟩ := exists_generator_power g hg a
  obtain ⟨l,rfl⟩ := exists_generator_power g hg b
  rw [← pow_add, classWord_multiplier_gpow g hg, classWord_multiplier_gpow g hg,
    classWord_multiplier_gpow g hg, pow_add]

/-- The all-unit multiplier product is an actual contextual derivation. -/
theorem derives_multiplier_mul (g : (ZMod d)ˣ) (hg : orderOf g = d-1)
    (i : Fin n) (a b : (ZMod d)ˣ) :
    Derives g (multiplier i a ++ multiplier i b) (multiplier i (a*b)) := by
  exact (classWord_eq_iff_derives g _ _).mp (classWord_multiplier_mul g hg i a b).symm

end QuditClifford.Circuit
