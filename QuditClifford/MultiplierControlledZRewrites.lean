import QuditClifford.MultiplierRewrites
import QuditClifford.ControlledZInversion

/-!
# Arbitrary-unit multiplier transport through controlled Z

Figure 1 C9 names only the chosen primitive generator. The finite C3 family,
the generator cycle, and C6 extend it to every unit and residue exponent.
These are equalities in the syntactic Figure 1 quotient, retaining scalars.
-/
noncomputable section
namespace QuditClifford.Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ)

/-- C9 extends to all multipliers on the first CZ operand. -/
theorem classWord_CZ_multiplier_unit_left (hg : orderOf g = d-1)
    (i j : Fin n) (hij : i ≠ j) (a : (ZMod d)ˣ) :
    classWord g [.CZ i j hij] * classWord g (multiplier i a) =
      classWord g (multiplier i a) * classWord g [.CZ i j hij] ^ (a : ZMod d).val := by
  obtain ⟨k, rfl⟩ := exists_generator_power g hg a
  rw [classWord_multiplier_gpow g hg]
  have he := mul_pow_transport (classWord_CZ_multiplier g i j hij) k
  have hv : (g : ZMod d).val ^ k % d = ((g^k : (ZMod d)ˣ) : ZMod d).val := by
    rw [Units.val_pow_eq_pow_val, ← ZMod.val_natCast]
    simp only [Nat.cast_pow, ZMod.natCast_zmod_val]
  rw [pow_eq_pow_mod _ (classWord_CZ_order g i j hij), hv] at he
  exact he

/-- Residue powers of C9, with the multiplier on the right. -/
theorem classWord_CZpow_multiplier_left (hg : orderOf g = d-1)
    (i j : Fin n) (hij : i ≠ j) (a : (ZMod d)ˣ) (b : ZMod d) :
    classWord g [.CZ i j hij] ^ b.val * classWord g (multiplier i a) =
      classWord g (multiplier i a) *
        classWord g [.CZ i j hij] ^ (b * (a : ZMod d)).val := by
  have he := (show SemiconjBy (classWord g (multiplier i a))
      (classWord g [.CZ i j hij] ^ (a : ZMod d).val)
      (classWord g [.CZ i j hij]) from
    (classWord_CZ_multiplier_unit_left g hg i j hij a).symm).pow_right b.val
  rw [← pow_mul, pow_eq_pow_mod _ (classWord_CZ_order g i j hij),
    Nat.mul_comm, ← ZMod.val_mul] at he
  exact he.symm

/-- C9 solved in the direction needed for pushing a multiplier past a CZ power. -/
theorem classWord_multiplier_CZpow_left (hg : orderOf g = d-1)
    (i j : Fin n) (hij : i ≠ j) (a : (ZMod d)ˣ) (b : ZMod d) :
    classWord g (multiplier i a) * classWord g [.CZ i j hij] ^ b.val =
      classWord g [.CZ i j hij] ^ (b * (↑a⁻¹ : ZMod d)).val *
        classWord g (multiplier i a) := by
  have he := classWord_CZpow_multiplier_left g hg i j hij a (b * (↑a⁻¹ : ZMod d))
  simpa only [mul_assoc, Units.inv_mul, mul_one] using he.symm

/-- The same exact transport on the second CZ operand. -/
theorem classWord_multiplier_CZpow_right (hg : orderOf g = d-1)
    (i j : Fin n) (hij : i ≠ j) (a : (ZMod d)ˣ) (b : ZMod d) :
    classWord g (multiplier j a) * classWord g [.CZ i j hij] ^ b.val =
      classWord g [.CZ i j hij] ^ (b * (↑a⁻¹ : ZMod d)).val *
        classWord g (multiplier j a) := by
  have hs := (classWord_eq_iff_derives g _ _).mpr
    (show Derives g [.CZ i j hij] [.CZ j i hij.symm] from
      .rule (Or.inl (.CZ_symmetry i j hij)))
  rw [hs]
  exact classWord_multiplier_CZpow_left g hg j i hij.symm a b

/-- Arbitrary multiplier/CZ transport is an actual Figure 1 derivation. -/
theorem derives_multiplier_CZexp_left (hg : orderOf g = d-1)
    (i j : Fin n) (hij : i ≠ j) (a : (ZMod d)ˣ) (b : ZMod d) :
    Derives g (multiplier i a ++ List.replicate b.val (.CZ i j hij))
      (List.replicate (b * (↑a⁻¹ : ZMod d)).val (.CZ i j hij) ++ multiplier i a) := by
  apply (classWord_eq_iff_derives g _ _).mp
  simpa only [classWord_append, classWord_replicate] using
    classWord_multiplier_CZpow_left g hg i j hij a b

end QuditClifford.Circuit
