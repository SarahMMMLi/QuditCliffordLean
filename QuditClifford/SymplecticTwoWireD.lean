import QuditClifford.SymplecticOneWire
import QuditClifford.MultiplierControlledZRewrites
import QuditClifford.WireRewrites

/-!
# Eight two-wire D-box rewrite cases

This ports all Fourier and phase D cases of Appendix F and its zero-a CZ
case, using the literal expanded Figure 6 words and the actual Figure 1 rules.
Seven hold exactly; the both-nonzero Fourier case uses explicit Pauli erasure.
The ninth case is in `SymplecticTwoWireDCZ`. No semantic equality is used to
obtain a derivation.
-/
noncomputable section
namespace QuditClifford.Circuit
variable {d n : ℕ} [NeZero d]
variable (g : (ZMod d)ˣ)

/-- Disjoint one-letter circuits commute by wiring coherence. -/
theorem classWord_disjoint (a b : Gate n) (hab : Disjoint a.support b.support) :
    Commute (classWord g [a]) (classWord g [b]) :=
  (classWord_eq_iff_derives g _ _).mpr (.rule (Or.inl (.disjoint a b hab)))

/-- Controlled-phase commutes with S on its first named wire by C8. -/
theorem classWord_CZ_commute_S_first (i j : Fin n) (hij : i ≠ j) :
    Commute (classWord g [.CZ i j hij]) (classWord g [.S i]) :=
  (classWord_eq_iff_derives g _ _).mpr (.rule (Or.inr (.C8 i j hij)))

/-- Controlled-phase commutes with S on its second named wire using symmetry. -/
theorem classWord_CZ_commute_S_right (i j : Fin n) (hij : i ≠ j) :
    Commute (classWord g [.CZ i j hij]) (classWord g [.S j]) := by
  have hs := (classWord_eq_iff_derives g _ _).mpr
    (show Derives g [.CZ i j hij] [.CZ j i hij.symm] from
      .rule (Or.inl (.CZ_symmetry i j hij)))
  rw [hs]
  exact classWord_CZ_commute_S_first g j i hij.symm

/-- C6 justifies residue addition for controlled-phase powers. -/
theorem derives_CZexp_add [Fact d.Prime] (i j : Fin n) (hij : i ≠ j) (a b : ZMod d) :
    Derives g (List.replicate a.val (.CZ i j hij) ++ List.replicate b.val (.CZ i j hij))
      (List.replicate (a+b).val (.CZ i j hij)) := by
  apply (classWord_eq_iff_derives g _ _).mp
  rw [classWord_append, classWord_replicate, classWord_replicate,
    classWord_replicate, ← pow_add, ZMod.val_add]
  exact pow_eq_pow_mod _ (classWord_CZ_order g i j hij)

/-- SWAP transports S from the first named wire by C10. -/
theorem classWord_SWAP_S_left (i j : Fin n) (hij : i ≠ j) :
    classWord g (SWAP (d := d) i j hij) * classWord g [.S i] =
      classWord g [.S j] * classWord g (SWAP (d := d) i j hij) :=
  (classWord_eq_iff_derives g _ _).mpr (.rule (Or.inr (.C10 i j hij)))

/-- SWAP transports H from the first named wire by C11. -/
theorem classWord_SWAP_H_left (i j : Fin n) (hij : i ≠ j) :
    classWord g (SWAP (d := d) i j hij) * classWord g [.H i] =
      classWord g [.H j] * classWord g (SWAP (d := d) i j hij) :=
  (classWord_eq_iff_derives g _ _).mpr (.rule (Or.inr (.C11 i j hij)))

/-- C7 says the expanded SWAP word is an involution syntactically. -/
theorem classWord_SWAP_sq (i j : Fin n) (hij : i ≠ j) :
    classWord g (SWAP (d := d) i j hij)^2 = 1 := by
  exact (classWord_eq_iff_derives g _ _).mpr
    (show Derives g (SWAP (d := d) i j hij ++ SWAP (d := d) i j hij) [] from
      .rule (Or.inr (.C7 i j hij)))

private theorem reverse_involution_transport {M : Type*} [Monoid M]
    (t a b : M) (ht : t*t = 1) (hab : t*a = b*t) : t*b = a*t := by
  calc
    t*b = t*b*(t*t) := by rw [ht, mul_one]
    _ = t*(b*t)*t := by simp only [mul_assoc]
    _ = t*(t*a)*t := by rw [hab]
    _ = a*t := by simp only [← mul_assoc, ht, one_mul]

/-- C7 and C10 also transport S from the second named wire. -/
theorem classWord_SWAP_S_right (i j : Fin n) (hij : i ≠ j) :
    classWord g (SWAP (d := d) i j hij) * classWord g [.S j] =
      classWord g [.S i] * classWord g (SWAP (d := d) i j hij) := by
  exact reverse_involution_transport _ _ _ (classWord_SWAP_sq g i j hij)
    (classWord_SWAP_S_left g i j hij)

/-- C7 and C11 also transport H from the second named wire. -/
theorem classWord_SWAP_H_right (i j : Fin n) (hij : i ≠ j) :
    classWord g (SWAP (d := d) i j hij) * classWord g [.H j] =
      classWord g [.H i] * classWord g (SWAP (d := d) i j hij) := by
  exact reverse_involution_transport _ _ _ (classWord_SWAP_sq g i j hij)
    (classWord_SWAP_H_left g i j hij)

end QuditClifford.Circuit
namespace QuditClifford.NormalBoxes
open Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ)

/-- D with nonzero a absorbs S on the second wire by adding exponents. -/
theorem derives_D_S_right_nonzero (a b : ZMod d) (ha : a ≠ 0)
    (i j : Fin n) (hij : i ≠ j) :
    Derives g (dWord a b i j hij ++ [.S j]) (dWord a (b-a) i j hij) := by
  have he : -b/a+1 = -(b-a)/a := by field_simp; ring
  have hr := (derives_Sexp_S g j (-b/a)).append_left
    (Circuit.SWAP (d := d) i j hij ++ List.replicate (-a).val (.CZ i j hij) ++ [.H j])
  rw [he] at hr
  simpa only [dWord, if_neg ha, List.append_assoc] using hr

/-- D with a=0 transports S on the second wire to the first wire. -/
theorem derives_D_S_right_zero (b : ZMod d) (i j : Fin n) (hij : i ≠ j) :
    Derives g (dWord 0 b i j hij ++ [.S j]) ([.S i] ++ dWord 0 b i j hij) := by
  apply (classWord_eq_iff_derives g _ _).mp
  simp only [dWord, if_pos rfl, ↓reduceIte, classWord_append, classWord_replicate]
  have hc := ((classWord_CZ_commute_S_right g i j hij).pow_left (-b).val).eq
  rw [mul_assoc, hc, ← mul_assoc, classWord_SWAP_S_right, mul_assoc]

/-- D transports S on the first wire to the second wire in every branch. -/
theorem derives_D_S_left (a b : ZMod d) (i j : Fin n) (hij : i ≠ j) :
    Derives g (dWord a b i j hij ++ [.S i]) ([.S j] ++ dWord a b i j hij) := by
  apply (classWord_eq_iff_derives g _ _).mp
  by_cases ha : a = 0
  · simp only [dWord, if_pos ha, classWord_append, classWord_replicate]
    have hc := ((classWord_CZ_commute_S_first g i j hij).pow_left (-b).val).eq
    rw [mul_assoc, hc, ← mul_assoc, classWord_SWAP_S_left, mul_assoc]
  · have hH : Commute (classWord g [.H j]) (classWord g [.S i]) :=
      classWord_disjoint g (.H j) (.S i) (by simpa [Gate.support] using hij)
    have hS : Commute (classWord g (Sexp j (-b/a))) (classWord g [.S i]) := by
      rw [Sexp, classWord_replicate]
      exact (classWord_disjoint g (.S j) (.S i) (by simpa [Gate.support] using hij)).pow_left _
    have hc := (((classWord_CZ_commute_S_first g i j hij).pow_left (-a).val).mul_left hH).mul_left hS
    simp only [dWord, if_neg ha, classWord_append, classWord_replicate]
    calc
      _ = classWord g (Circuit.SWAP (d := d) i j hij) *
          ((classWord g [.CZ i j hij] ^(-a).val * classWord g [.H j] *
            classWord g (Sexp j (-b/a))) * classWord g [.S i]) := by simp only [mul_assoc]
      _ = _ := by rw [hc.eq]; simp only [← mul_assoc]; rw [classWord_SWAP_S_left]

/-- D with a=0 absorbs CZ by C6 exponent addition. -/
theorem derives_D_CZ_zero (b : ZMod d) (i j : Fin n) (hij : i ≠ j) :
    Derives g (dWord 0 b i j hij ++ [.CZ i j hij]) (dWord 0 (b-1) i j hij) := by
  have he : -b+1 = -(b-1) := by ring
  have hr := (derives_CZexp_add g i j hij (-b) 1).append_left (Circuit.SWAP (d := d) i j hij)
  rw [he] at hr
  simpa only [dWord, if_pos rfl, ↓reduceIte, ZMod.val_one, List.replicate_one, List.append_assoc] using hr

/-- D_00 is the literal SWAP word and transports H to the first wire. -/
theorem derives_D_H_zero_zero (i j : Fin n) (hij : i ≠ j) :
    Derives g (dWord (0 : ZMod d) 0 i j hij ++ [.H j])
      ([.H i] ++ dWord (0 : ZMod d) 0 i j hij) := by
  apply (classWord_eq_iff_derives g _ _).mp
  simpa only [dWord, if_pos rfl, ↓reduceIte, neg_zero, ZMod.val_zero, List.replicate_zero,
    List.append_nil, classWord_append] using classWord_SWAP_H_right g i j hij

/-- D_0b with b nonzero absorbs H by its literal definition. -/
theorem derives_D_H_zero_nonzero (b : ZMod d) (hb : b ≠ 0)
    (i j : Fin n) (hij : i ≠ j) :
    Derives g (dWord 0 b i j hij ++ [.H j]) (dWord b 0 i j hij) := by
  simp only [dWord, if_pos rfl, ↓reduceIte, if_neg hb, neg_zero, zero_div, Sexp,
    ZMod.val_zero, List.replicate_zero, List.append_nil]
  exact .refl _

end QuditClifford.NormalBoxes

namespace QuditClifford.Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

/-- C6 also gives the inverse of a residue-valued controlled-phase power. -/
theorem classWord_CZexp_neg (i j : Fin n) (hij : i ≠ j) (a : ZMod d) :
    classWord g [.CZ i j hij] ^(-a).val = (classWord g [.CZ i j hij] ^a.val)⁻¹ := by
  symm
  apply inv_eq_of_mul_eq_one_left
  have he := (classWord_eq_iff_derives g _ _).mpr (derives_CZexp_add g i j hij (-a) a)
  simpa only [classWord_append, classWord_replicate, neg_add_cancel, ZMod.val_zero, pow_zero] using he

/-- The Fourier-square inversion law transports every CZ residue power. -/
theorem classWord_CZexp_H_sq_right (i j : Fin n) (hij : i ≠ j) (a : ZMod d) :
    classWord g [.CZ i j hij] ^(-a).val * classWord g [.H j] ^2 =
      classWord g [.H j] ^2 * classWord g [.CZ i j hij] ^a.val := by
  have he := congrArg (fun z => z^a.val) (classWord_H_sq_conjugate_CZ_right g i j hij)
  simp only [conj_pow, inv_pow] at he
  have hr := congrArg (fun z => z * classWord g [.H j] ^2) he
  rw [classWord_CZexp_neg]
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hr.symm

set_option linter.unusedSectionVars false in
/-- SWAP transports a residue-valued S power from its second named wire. -/
theorem classWord_SWAP_Sexp_right (i j : Fin n) (hij : i ≠ j) (a : ZMod d) :
    classWord g (SWAP (d := d) i j hij) * classWord g (Sexp j a) =
      classWord g (Sexp i a) * classWord g (SWAP (d := d) i j hij) := by
  simpa only [Sexp, classWord_replicate] using
    (show SemiconjBy (classWord g (SWAP (d := d) i j hij))
      (classWord g [.S j]) (classWord g [.S i]) from classWord_SWAP_S_right g i j hij).pow_right a.val

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
/-- SWAP transports the erased multiplier by its already derived H/S transport. -/
theorem symplecticClassWord_SWAP_multiplier_right (i j : Fin n) (hij : i ≠ j)
    (a : (ZMod d)ˣ) :
    symplecticClassWord g (SWAP (d := d) i j hij) * symplecticClassWord g (multiplier j a) =
      symplecticClassWord g (multiplier i a) * symplecticClassWord g (SWAP (d := d) i j hij) := by
  have hr := (classWord_eq_iff_derives g _ _).mpr
    (derives_SWAP_multiplier_left g j i hij.symm a)
  have hs := (classWord_eq_iff_derives g _ _).mpr (derives_SWAP_symmetry g i j hij)
  simp only [classWord_append] at hr
  rw [← hs] at hr
  simpa only [map_mul, presentedToSymplectic_classWord] using congrArg (presentedToSymplectic g) hr

end QuditClifford.Circuit
namespace QuditClifford.NormalBoxes
open Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

/-- The nonzero-a, zero-b Fourier D case holds exactly by CZ inversion. -/
theorem derives_D_H_nonzero_zero (a : ZMod d) (ha : a ≠ 0)
    (i j : Fin n) (hij : i ≠ j) :
    Derives g (dWord a 0 i j hij ++ [.H j])
      (List.replicate 2 (.H i) ++ dWord 0 (-a) i j hij) := by
  apply (classWord_eq_iff_derives g _ _).mp
  have ht := (show SemiconjBy (classWord g (Circuit.SWAP (d := d) i j hij))
    (classWord g [.H j]) (classWord g [.H i]) from classWord_SWAP_H_right g i j hij).pow_right 2
  simp only [dWord, if_neg ha, if_pos rfl, ↓reduceIte, neg_zero, zero_div, Sexp,
    ZMod.val_zero, List.replicate_zero, List.append_nil, neg_neg,
    classWord_append, classWord_replicate]
  calc
    _ = classWord g (Circuit.SWAP (d := d) i j hij) *
        (classWord g [.CZ i j hij] ^(-a).val * classWord g [.H j] ^2) := by simp only [pow_two, mul_assoc]
    _ = classWord g (Circuit.SWAP (d := d) i j hij) *
        (classWord g [.H j] ^2 * classWord g [.CZ i j hij] ^a.val) := by
      rw [classWord_CZexp_H_sq_right]
    _ = _ := by rw [← mul_assoc, ht, mul_assoc]


end QuditClifford.NormalBoxes

namespace QuditClifford.NormalBoxes
open Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

/-- The both-nonzero Fourier D case. Its dirty factor is written as S(a/b)
followed by M(b/a), the derived equivalent of the source's reversed order. -/
theorem symplectic_D_H_nonzero_nonzero (a b : ZMod d) (ha : a ≠ 0) (hb : b ≠ 0)
    (i j : Fin n) (hij : i ≠ j) :
    SymplecticDerives g (dWord a b i j hij ++ [.H j])
      (Sexp i (a/b) ++ Circuit.multiplier i (Units.mk0 (b/a) (div_ne_zero hb ha)) ++
        dWord b (-a) i j hij) := by
  let x := Units.mk0 (-b/a) (div_ne_zero (neg_ne_zero.mpr hb) ha)
  let v := Units.mk0 (b/a) (div_ne_zero hb ha)
  let W := symplecticClassWord g (Circuit.SWAP (d := d) i j hij)
  let H := symplecticClassWord g [.H j]
  let C (r : ZMod d) := symplecticClassWord g [.CZ i j hij] ^r.val
  let Si (r : ZMod d) := symplecticClassWord g (Sexp i r)
  let Sj (r : ZMod d) := symplecticClassWord g (Sexp j r)
  let Mi := symplecticClassWord g (Circuit.multiplier i v)
  let Mj := symplecticClassWord g (Circuit.multiplier j v)
  have hx : -x = v := by ext; dsimp [x, v]; ring
  have hxi : -(↑x⁻¹ : ZMod d) = a/b := by dsimp [x]; field_simp
  have hh : H * Sj (-b/a) * H = Sj (a/b) * Mj * H * Sj (a/b) := by
    have ht := symplecticClassWord_H_Sexp_H g j x
    rw [hx, hxi] at ht
    exact ht
  have hs : W * Sj (a/b) = Si (a/b) * W := by
    simpa only [map_mul, presentedToSymplectic_classWord] using
      congrArg (presentedToSymplectic g) (classWord_SWAP_Sexp_right g i j hij (a/b))
  have hm : W * Mj = Mi * W := symplecticClassWord_SWAP_multiplier_right g i j hij v
  have hc : Commute (C (-a)) (Sj (a/b)) := by
    have ht := ((classWord_CZ_commute_S_right g i j hij).pow_left (-a).val).pow_right (a/b).val
    simpa only [C, Sj, Commute, SemiconjBy, Sexp, classWord_replicate,
      symplecticClassWord_replicate, map_mul, map_pow, presentedToSymplectic_classWord] using
      congrArg (presentedToSymplectic g) ht.eq
  have hcm : C (-a) * Mj = Mj * C (-b) := by
    have ht := classWord_CZpow_multiplier_left g Fact.out j i hij.symm v (-a)
    rw [← classWord_CZ_symmetry g i j hij] at ht
    have he : -a * (v : ZMod d) = -b := by dsimp [v]; field_simp; ring
    rw [he] at ht
    simpa only [map_mul, map_pow, presentedToSymplectic_classWord] using
      congrArg (presentedToSymplectic g) ht
  have ht : W * C (-a) * H * Sj (-b/a) * H =
      Si (a/b) * Mi * (W * C (-b) * H * Sj (a/b)) := by
    calc
      _ = W * C (-a) * (H * Sj (-b/a) * H) := by group
      _ = W * C (-a) * (Sj (a/b) * Mj * H * Sj (a/b)) := by rw [hh]
      _ = W * (C (-a) * Sj (a/b)) * Mj * H * Sj (a/b) := by group
      _ = W * (Sj (a/b) * C (-a)) * Mj * H * Sj (a/b) := by rw [hc.eq]
      _ = (W * Sj (a/b)) * (C (-a) * Mj) * H * Sj (a/b) := by group
      _ = (Si (a/b) * W) * (Mj * C (-b)) * H * Sj (a/b) := by rw [hs, hcm]
      _ = Si (a/b) * (W * Mj) * C (-b) * H * Sj (a/b) := by group
      _ = _ := by rw [hm]; group
  apply (symplecticClassWord_eq_iff_derives g _ _).mp
  simpa only [dWord, if_neg ha, if_neg hb, neg_neg, symplecticClassWord_append,
    symplecticClassWord_replicate, W, H, C, Si, Sj, Mi, Mj, v, mul_assoc] using ht

/-- The same D case in the paper's multiplier-before-phase order, after
translating to the selected raw-multiplier convention. -/
theorem symplectic_D_H_nonzero_nonzero_source (a b : ZMod d) (ha : a ≠ 0) (hb : b ≠ 0)
    (i j : Fin n) (hij : i ≠ j) :
    SymplecticDerives g (dWord a b i j hij ++ [.H j])
      (Circuit.multiplier i (Units.mk0 (b/a) (div_ne_zero hb ha)) ++ Sexp i (b/a) ++
        dWord b (-a) i j hij) := by
  let v := Units.mk0 (b/a) (div_ne_zero hb ha)
  have hc := symplecticClassWord_multiplier_Sexp g Fact.out i v (b/a)
  have he : (b/a)*(↑v⁻¹ : ZMod d)^2 = a/b := by
    dsimp [v]
    field_simp
    ring
  rw [he] at hc
  have h := (symplecticClassWord_eq_iff_derives g _ _).mpr
    (symplectic_D_H_nonzero_nonzero g a b ha hb i j hij)
  apply (symplecticClassWord_eq_iff_derives g _ _).mp
  simp only [symplecticClassWord_append] at h ⊢
  change _ = (symplecticClassWord g (Circuit.multiplier i v)*symplecticClassWord g (Sexp i (b/a)))*_
  rw [hc]
  exact h

end QuditClifford.NormalBoxes
