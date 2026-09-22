import QuditClifford.SymplecticOneWire
import QuditClifford.MultiplierControlledZRewrites
import QuditClifford.WireRewrites
import QuditClifford.ControlledXPauliRewrites

/-!
# Controlled-phase pushing through an A box

The proofs use the literal expanded SWAP and CX words inside the syntactic
Pauli-erased quotient. They are not inferred from exponent equality.
-/

noncomputable section
namespace QuditClifford.Circuit

private theorem four_inverse {G : Type*} [Group G] (a : G) (ha : a^4=1) :
    a*a^2 = a⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  simpa only [← pow_succ', ← pow_succ] using ha

/-- The Fourier cube expression for SWAP implies its three-CX expression. -/
private theorem swap_three_cx {G : Type*} [Group G] (a b c w : G)
    (hab : Commute a b) (ha : a^4=1) (hb : b^4=1)
    (hac : a^2*c*(a^2)⁻¹=c⁻¹) (hbc : b^2*c*(b^2)⁻¹=c⁻¹)
    (hw : w=(c*a*b)^3) (hwa : w*a=b*w) :
    w = (b⁻¹*c*b) * (a⁻¹*c*a)⁻¹ * (b⁻¹*c*b) * b^2 := by
  let q := a*b
  have hq4 : q^4=1 := by dsimp [q]; rw [hab.mul_pow, ha, hb, one_mul]
  have hqinv : q⁻¹=q*q^2 := (four_inverse q hq4).symm
  have hq2 : q^2=a^2*b^2 := hab.mul_pow 2
  have haq : a⁻¹*b⁻¹=q⁻¹ := by dsimp [q]; rw [mul_inv_rev, hab.inv_inv.eq]
  have hq2c : Commute (q^2) c := by
    change q^2*c=c*q^2
    apply (mul_right_cancel_iff (a := (q^2)⁻¹)).mp
    rw [hq2, mul_inv_rev]
    calc
      _ = a^2*(b^2*c*(b^2)⁻¹)*(a^2)⁻¹ := by group
      _ = a^2*c⁻¹*(a^2)⁻¹ := by rw [hbc]
      _ = (a^2*c*(a^2)⁻¹)⁻¹ := by group
      _ = c := by rw [hac, inv_inv]
      _ = _ := by group
  have hq2b : q^2*b⁻¹=q*a := by
    rw [hq2]
    dsimp [q]
    calc
      _ = a*(a*b) := by simp only [pow_two]; group
      _ = a*(b*a) := by rw [hab.eq]
      _ = _ := by group
  have hl : (a⁻¹*c*a)⁻¹=a*c*a⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev, inv_inv, ← hac]
    group
  symm
  calc
    _ = b⁻¹*c*(b*a)*c*(a⁻¹*b⁻¹)*c*(b*b^2) := by rw [hl]; group
    _ = b⁻¹*c*q*c*q⁻¹*c*b⁻¹ := by
      rw [hab.symm.eq, haq, four_inverse b hb]
    _ = b⁻¹*c*q*c*q*c*q^2*b⁻¹ := by
      rw [hqinv]
      simp only [mul_assoc]
      rw [← mul_assoc (q^2), hq2c.eq]
      simp only [mul_assoc]
    _ = b⁻¹*w*a := by
      rw [mul_assoc (b⁻¹*c*q*c*q*c), hq2b, hw]
      dsimp [q]
      simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc]
    _ = w := by rw [mul_assoc, hwa, inv_mul_cancel_left]

variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

set_option linter.unusedSectionVars false in
private theorem gate_commute (a b : Gate n) (h : Disjoint a.support b.support) :
    Commute (symplecticClassWord g [a]) (symplecticClassWord g [b]) :=
  (symplecticClassWord_eq_iff_derives g _ _).mpr
    (derives_symplectic g (.rule (Or.inl (Structural.disjoint a b h))))

private theorem h_four (i : Fin n) : symplecticClassWord g [.H i] ^4=1 := by
  have he := (symplecticClassWord_eq_iff_derives g _ _).mpr
    (derives_symplectic g (derives_H_four Fact.out g Fact.out i))
  simpa only [symplecticClassWord_replicate, symplecticClassWord_nil] using he

/-- The exact expanded SWAP, after scalar erasure, is three controlled additions
with a final Fourier square. This is derived from T4, C2, C9, and C11. -/
theorem symplecticClassWord_SWAP_three_CX (i j : Fin n) (hij : i ≠ j) :
    symplecticClassWord g (SWAP (d := d) i j hij) =
      symplecticClassWord g (CX i j hij) *
      (symplecticClassWord g (CX j i hij.symm))⁻¹ *
      symplecticClassWord g (CX i j hij) * symplecticClassWord g [.H j] ^2 := by
  have hab := gate_commute g (.H i) (.H j) (by simp [Gate.support, hij, hij.symm])
  have hac := congrArg (presentedToSymplectic g) (classWord_H_sq_conjugate_CZ_left g i j hij)
  have hbc := congrArg (presentedToSymplectic g) (classWord_H_sq_conjugate_CZ_right g i j hij)
  simp only [map_mul, map_inv, map_pow, presentedToSymplectic_classWord] at hac hbc
  have hwa := (symplecticClassWord_eq_iff_derives g _ _).mpr
    (derives_symplectic g (derives_SWAP_H_left g i j hij))
  simp only [symplecticClassWord_append] at hwa
  have hw : symplecticClassWord g (SWAP (d := d) i j hij) =
      (symplecticClassWord g [.CZ i j hij] * symplecticClassWord g [.H i] *
        symplecticClassWord g [.H j])^3 := by
    simp only [SWAP, symplecticClassWord_append, symplecticClassWord_scalar,
      one_mul, symplecticClassWord_power]
    rfl
  have he := swap_three_cx _ _ _ _ hab (h_four g i) (h_four g j) hac hbc hw hwa
  have hcx := congrArg (presentedToSymplectic g) (classWord_CX_conjugate g i j hij)
  have hcx' := congrArg (presentedToSymplectic g) (classWord_CX_conjugate g j i hij.symm)
  have hcz := congrArg (presentedToSymplectic g) (classWord_CZ_symmetry g j i hij.symm)
  simp only [map_mul, map_inv, presentedToSymplectic_classWord] at hcx hcx' hcz
  rw [hcz] at hcx'
  simpa only [← hcx, ← hcx'] using he

private abbrev hh (i : Fin n) := symplecticClassWord g [.H i]
private abbrev mm (i : Fin n) (a : (ZMod d)ˣ) := symplecticClassWord g (multiplier i a)
private abbrev cc (i j : Fin n) (hij : i ≠ j) := symplecticClassWord g [.CZ i j hij]
private abbrev xx (i j : Fin n) (hij : i ≠ j) := symplecticClassWord g (CX i j hij)
private abbrev ww (i j : Fin n) (hij : i ≠ j) := symplecticClassWord g (SWAP (d := d) i j hij)

private theorem cx_eq (i j : Fin n) (hij : i ≠ j) :
    xx g i j hij = (hh g j)⁻¹ * cc g i j hij * hh g j := by
  simpa only [map_mul, map_inv, presentedToSymplectic_classWord] using
    congrArg (presentedToSymplectic g) (classWord_CX_conjugate g i j hij)

private theorem hsquare_cz (i j : Fin n) (hij : i ≠ j) :
    hh g j ^2 * cc g i j hij * (hh g j ^2)⁻¹ = (cc g i j hij)⁻¹ := by
  simpa only [map_mul, map_inv, map_pow, presentedToSymplectic_classWord] using
    congrArg (presentedToSymplectic g) (classWord_H_sq_conjugate_CZ_right g i j hij)

theorem symplecticClassWord_H_CZ_Hinv (i j : Fin n) (hij : i ≠ j) :
    hh g j * cc g i j hij * (hh g j)⁻¹ = (xx g i j hij)⁻¹ := by
  rw [cx_eq, mul_inv_rev, mul_inv_rev, inv_inv, ← hsquare_cz g i j hij]
  group

/-- A useful Fourier/CZ factorization with the actual SWAP word. -/
theorem symplecticClassWord_H_CZ_factor (i j : Fin n) (hij : i ≠ j) :
    hh g i * cc g i j hij =
      (hh g j * cc g i j hij * (hh g j)⁻¹) * ww g i j hij *
        xx g i j hij * hh g i * hh g j ^2 := by
  have hb : hh g j ^2 * xx g i j hij = (xx g i j hij)⁻¹ * hh g j ^2 := by
    apply (mul_right_cancel_iff (a := (hh g j ^2)⁻¹)).mp
    rw [cx_eq]
    have hc := hsquare_cz g i j hij
    calc
      _ = (hh g j)⁻¹ * (hh g j ^2 * cc g i j hij * (hh g j ^2)⁻¹) * hh g j := by group
      _ = (hh g j)⁻¹ * (cc g i j hij)⁻¹ * hh g j := by rw [hc]
      _ = _ := by group
  have hc : hh g i * cc g i j hij = (xx g j i hij.symm)⁻¹ * hh g i := by
    have h := symplecticClassWord_H_CZ_Hinv g j i hij.symm
    have hz := congrArg (presentedToSymplectic g) (classWord_CZ_symmetry g j i hij.symm)
    simp only [presentedToSymplectic_classWord] at hz
    change hh g i * symplecticClassWord g [.CZ j i hij.symm] * (hh g i)⁻¹ = _ at h
    rw [hz] at h
    calc
      _ = (hh g i * cc g i j hij * (hh g i)⁻¹) * hh g i := by group
      _ = _ := by rw [h]
  have hab := gate_commute g (.H i) (.H j) (by simp [Gate.support, hij, hij.symm])
  symm
  rw [symplecticClassWord_H_CZ_Hinv, show ww g i j hij = _ from symplecticClassWord_SWAP_three_CX g i j hij]
  calc
    _ = (xx g j i hij.symm)⁻¹ * xx g i j hij *
        (hh g j ^2 * xx g i j hij) * hh g i * hh g j ^2 := by group
    _ = (xx g j i hij.symm)⁻¹ * hh g j ^2 * hh g i * hh g j ^2 := by rw [hb]; group
    _ = (xx g j i hij.symm)⁻¹ * hh g i * (hh g j ^2 * hh g j ^2) := by
      rw [mul_assoc ((xx g j i hij.symm)⁻¹), (hab.pow_right 2).symm.eq]
      group
    _ = (xx g j i hij.symm)⁻¹ * hh g i := by
      rw [← pow_add]
      change _ * hh g j ^4 = _
      rw [h_four, mul_one]
    _ = _ := hc.symm

private theorem multiplier_commute_gate (i : Fin n) (a : (ZMod d)ˣ) (b : Gate n)
    (hi : i ∉ b.support) : Commute (mm g i a) (symplecticClassWord g [b]) := by
  have hH := (gate_commute g b (.H i) (by simpa [Gate.support] using hi)).symm
  have hS := (gate_commute g b (.S i) (by simpa [Gate.support] using hi)).symm
  have hs (c : ZMod d) : Commute (symplecticClassWord g (Sexp i c))
      (symplecticClassWord g [b]) := by
    simpa only [Sexp, symplecticClassWord_replicate] using hS.pow_left c.val
  dsimp [mm]
  rw [symplecticClassWord_multiplier_expand]
  exact (((((hs _).mul_left hH).mul_left (hs _)).mul_left hH).mul_left (hs _)).mul_left hH

theorem symplecticClassWord_multiplier_CX_target (i j : Fin n) (hij : i ≠ j) (a : (ZMod d)ˣ) :
    mm g j a * xx g i j hij = xx g i j hij ^(a : ZMod d).val * mm g j a := by
  have hM := symplecticClassWord_multiplier_H g j a⁻¹
  change mm g j a⁻¹ * hh g j = hh g j * mm g j (a⁻¹)⁻¹ at hM
  rw [inv_inv] at hM
  have hMi : mm g j a * (hh g j)⁻¹ = (hh g j)⁻¹ * mm g j a⁻¹ := by
    calc
      _ = (hh g j)⁻¹ * (hh g j * mm g j a) * (hh g j)⁻¹ := by group
      _ = _ := by rw [← hM]; group
  have hc := congrArg (presentedToSymplectic g)
    (classWord_multiplier_CZpow_right g Fact.out i j hij a⁻¹ (1 : ZMod d))
  simp only [map_mul, map_pow, presentedToSymplectic_classWord, ZMod.val_one,
    pow_one, one_mul, inv_inv] at hc
  change mm g j a⁻¹ * cc g i j hij = cc g i j hij ^(a : ZMod d).val * mm g j a⁻¹ at hc
  rw [cx_eq]
  calc
    _ = (hh g j)⁻¹ * (mm g j a⁻¹ * cc g i j hij) * hh g j := by simp only [← mul_assoc]; rw [hMi]
    _ = (hh g j)⁻¹ * cc g i j hij ^(a : ZMod d).val * (hh g j * mm g j a) := by
      rw [hc, mul_assoc, mul_assoc, hM]
      group
    _ = _ := by
      have hp : ((hh g j)⁻¹ * cc g i j hij * hh g j) ^ (a : ZMod d).val =
          (hh g j)⁻¹ * cc g i j hij ^ (a : ZMod d).val * hh g j := by
        simpa using (conj_pow (a := (hh g j)⁻¹) (b := cc g i j hij) (i := (a : ZMod d).val))
      rw [hp]
      group

set_option linter.unusedSectionVars false in
private theorem multiplier_SWAP (i j : Fin n) (hij : i ≠ j) (a : (ZMod d)ˣ) :
    mm g i a * ww g i j hij = ww g i j hij * mm g j a := by
  have hw := (symplecticClassWord_eq_iff_derives g _ _).mpr
    (derives_symplectic g (derives_SWAP_symmetry g i j hij))
  have ht := (symplecticClassWord_eq_iff_derives g _ _).mpr
    (derives_symplectic g (derives_SWAP_multiplier_left g j i hij.symm a))
  simp only [symplecticClassWord_append, ← hw] at ht
  exact ht.symm

/-- The nonzero A/CZ algebra before the final S exponent is restored. -/
theorem symplecticClassWord_multiplier_H_CZ (i j : Fin n) (hij : i ≠ j)
    (a : (ZMod d)ˣ) :
    mm g i a * hh g i * cc g i j hij =
      (hh g j * cc g i j hij ^(↑a⁻¹ : ZMod d).val * (hh g j)⁻¹) * ww g i j hij *
        xx g i j hij ^(a : ZMod d).val * hh g i * mm g j (-a) := by
  have hihj := multiplier_commute_gate g i a (.H j) (by simp [Gate.support, hij])
  have hjhi := multiplier_commute_gate g j a (.H i) (by simp [Gate.support, hij.symm])
  have hc := congrArg (presentedToSymplectic g)
    (classWord_multiplier_CZpow_left g Fact.out i j hij a (1 : ZMod d))
  simp only [map_mul, map_pow, presentedToSymplectic_classWord, ZMod.val_one, pow_one, one_mul] at hc
  change mm g i a * cc g i j hij = cc g i j hij ^(↑a⁻¹ : ZMod d).val * mm g i a at hc
  have hd : mm g i a * (hh g j * cc g i j hij * (hh g j)⁻¹) =
      (hh g j * cc g i j hij ^(↑a⁻¹ : ZMod d).val * (hh g j)⁻¹) * mm g i a := by
    calc
      _ = hh g j * (mm g i a * cc g i j hij) * (hh g j)⁻¹ := by
        simp only [← mul_assoc]; rw [hihj.eq]
      _ = _ := by rw [hc, mul_assoc, mul_assoc, hihj.inv_right.eq]; group
  have hn : mm g j a * hh g j ^2 = mm g j (-a) := by
    rw [symplecticClassWord_H_sq, ← symplecticClassWord_multiplier_mul g Fact.out]
    simp only [mul_neg_one]
  calc
    _ = mm g i a * (hh g i * cc g i j hij) := by group
    _ = mm g i a * ((hh g j * cc g i j hij * (hh g j)⁻¹) * ww g i j hij *
        xx g i j hij * hh g i * hh g j ^2) := by rw [symplecticClassWord_H_CZ_factor]
    _ = (hh g j * cc g i j hij ^(↑a⁻¹ : ZMod d).val * (hh g j)⁻¹) *
        (mm g i a * ww g i j hij) * xx g i j hij * hh g i * hh g j ^2 := by
      have hd' := hd
      simp only [← mul_assoc] at hd' ⊢
      rw [hd']
    _ = (hh g j * cc g i j hij ^(↑a⁻¹ : ZMod d).val * (hh g j)⁻¹) * ww g i j hij *
        (mm g j a * xx g i j hij) * hh g i * hh g j ^2 := by rw [multiplier_SWAP]; group
    _ = _ := by
      rw [symplecticClassWord_multiplier_CX_target]
      simp only [mul_assoc]
      rw [← mul_assoc (mm g j a), hjhi.eq, mul_assoc (hh g i), hn]

end QuditClifford.Circuit

namespace QuditClifford.NormalBoxes
open Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

omit [Fact (Odd d)] in
/-- The zero-a A/CZ case is exact: it is the all-unit form of C9. -/
theorem derives_A_CZ_zero (A : ABox (ZMod d)) (ha : A.a=0)
    (i j : Fin n) (hij : i ≠ j) :
    Derives g (A.toWord i ++ [.CZ i j hij])
      (List.replicate (A.b⁻¹).val (.CZ i j hij) ++ A.toWord i) := by
  have he := classWord_multiplier_CZpow_left g Fact.out i j hij
    (Units.mk0 A.b (A.b_ne_zero ha)) (1 : ZMod d)
  simp only [ZMod.val_one, pow_one, one_mul, Units.val_inv_eq_inv_val, Units.val_mk0] at he
  apply (classWord_eq_iff_derives g _ _).mp
  simpa only [ABox.toWord, dif_pos ha, classWord_append, classWord_replicate] using he

/-- The new A label after the nonzero branch of CZ-through-A. -/
def ABox.controlledPhaseStep (A : ABox (ZMod d)) (ha : A.a ≠ 0) : ABox (ZMod d) :=
  ⟨0, -A.a, fun h => ha (neg_eq_zero.mp (congrArg Prod.fst h))⟩

set_option maxHeartbeats 200000 in
/-- The nonzero-a A/CZ case from Appendix F. The output is the literal B word
and A_(0,-a) word with the stated dirty Fourier-conjugated CZ prefix. -/
theorem symplecticDerives_A_CZ_nonzero (A : ABox (ZMod d)) (ha : A.a ≠ 0)
    (i j : Fin n) (hij : i ≠ j) :
    SymplecticDerives g (A.toWord i ++ [.CZ i j hij])
      ([.H j] ++ List.replicate (A.a⁻¹).val (.CZ i j hij) ++ List.replicate 3 (.H j) ++
        bWord A.a A.b i j hij ++ (A.controlledPhaseStep ha).toWord j) := by
  let u : (ZMod d)ˣ := Units.mk0 A.a ha
  let t : ZMod d := -A.b/A.a
  have hs : Commute (symplecticClassWord g (Sexp i t)) (cc g i j hij) := by
    have hc := congrArg (presentedToSymplectic g) (classWord_CZ_commute_S_left g i j hij).eq
    have hc' : Commute (symplecticClassWord g [.S i]) (cc g i j hij) := by
      simpa only [map_mul, presentedToSymplectic_classWord] using hc.symm
    simpa only [Sexp, symplecticClassWord_replicate] using hc'.pow_left t.val
  have hm : Commute (mm g j (-u)) (symplecticClassWord g (Sexp i t)) := by
    have h := multiplier_commute_gate g j (-u) (.S i) (by simp [Gate.support, hij.symm])
    simpa only [Sexp, symplecticClassWord_replicate] using h.pow_right t.val
  have hh3 : hh g j ^3 = (hh g j)⁻¹ := by
    simpa only [← pow_succ'] using four_inverse (hh g j) (h_four g j)
  apply (symplecticClassWord_eq_iff_derives g _ _).mp
  simp only [ABox.toWord, dif_neg ha, ABox.controlledPhaseStep, dif_pos rfl,
    bWord, if_neg ha, symplecticClassWord_append, symplecticClassWord_replicate,
    symplecticClassWord_power, ↓reduceDIte]
  have hu : (Units.mk0 (-A.a) (neg_ne_zero.mpr ha) : (ZMod d)ˣ) = -u := Units.ext rfl
  rw [hu]
  change mm g i u * hh g i * symplecticClassWord g (Sexp i t) * cc g i j hij =
    hh g j * cc g i j hij ^ (↑u⁻¹ : ZMod d).val * hh g j ^3 *
      (ww g i j hij * xx g i j hij ^(u : ZMod d).val * hh g i *
        symplecticClassWord g (Sexp i t)) * mm g j (-u)
  rw [hh3]
  calc
    _ = mm g i u * hh g i * cc g i j hij * symplecticClassWord g (Sexp i t) := by
      rw [mul_assoc (mm g i u * hh g i), hs.eq]
      group
    _ = _ := by
      rw [symplecticClassWord_multiplier_H_CZ]
      simp only [mul_assoc]
      rw [hm.eq]

end QuditClifford.NormalBoxes
