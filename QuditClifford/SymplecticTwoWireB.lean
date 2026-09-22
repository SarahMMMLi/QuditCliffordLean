import QuditClifford.SymplecticTwoWireD
import QuditClifford.ControlledXPauliRewrites
import QuditClifford.MultiplierControlledZRewrites

/-!
# All nine two-wire B-box rewrite cases

This ports the B cases from Appendix F and the pinned Agda `BR/Two/B.agda`:
H and S on the first wire, and S on the second wire, with all zero/nonzero
branches. Six cases hold as exact Figure 1 derivations. The remaining three
use the explicit scalar-and-Pauli erasure. All proofs use literal expanded
Figure 6 words, derived C12 conjugation laws, and syntactic group algebra.
-/

noncomputable section
namespace QuditClifford.Circuit
variable {d n : ℕ} [NeZero d]
variable (g : (ZMod d)ˣ)

/-- Controlled addition commutes with S on its control wire by C8 and
structural interchange with its target-wire H factors. -/
theorem classWord_CX_commute_S_control (i j : Fin n) (hij : i ≠ j) :
    Commute (classWord g (CX i j hij)) (classWord g [.S i]) := by
  have hH : Commute (classWord g [.H j]) (classWord g [.S i]) :=
    classWord_disjoint g (.H j) (.S i) (by simpa [Gate.support] using hij)
  change Commute (classWord g [.H j] * (classWord g [.H j] *
    (classWord g [.H j] * (classWord g [.CZ i j hij] * classWord g [.H j]))))
      (classWord g [.S i])
  exact hH.mul_left (hH.mul_left (hH.mul_left
    ((classWord_CZ_commute_S_first g i j hij).mul_left hH)))

/-- Every power of a controlled addition commutes with its control's S gate. -/
theorem derives_CXpower_S_control (i j : Fin n) (hij : i ≠ j) (k : ℕ) :
    Derives g (power (CX i j hij) k ++ [.S i])
      ([.S i] ++ power (CX i j hij) k) := by
  apply (classWord_eq_iff_derives g _ _).mp
  simpa only [classWord_append, classWord_power] using
    ((classWord_CX_commute_S_control g i j hij).pow_left k).eq

variable [Fact d.Prime] [Fact (Odd d)] [Fact (orderOf g = d-1)]

/-- SWAP commutes with CZ by its expanded definition and the two C11 transports. -/
theorem classWord_SWAP_commute_CZ (i j : Fin n) (hij : i ≠ j) :
    Commute (classWord g (SWAP (d := d) i j hij)) (classWord g [.CZ i j hij]) := by
  let W := classWord g (SWAP (d := d) i j hij)
  let A := classWord g [.H i]*classWord g [.H j]
  let C := classWord g [.CZ i j hij]
  let T : PresentedCircuit g n := classWord g (scalar (d*((d-1)/2)))
  have hH : Commute (classWord g [.H i]) (classWord g [.H j]) :=
    classWord_disjoint g (.H i) (.H j) (by simpa [Gate.support] using hij.symm)
  have hWA : Commute W A := by
    change W*(classWord g [.H i]*classWord g [.H j]) =
      (classWord g [.H i]*classWord g [.H j])*W
    rw [← mul_assoc, classWord_SWAP_H_left, mul_assoc, classWord_SWAP_H_right,
      ← mul_assoc, hH.symm.eq]
  have hW : W = T*(C*A)^3 := by
    simp only [W, SWAP, classWord_append, classWord_power]
    rfl
  have hT : Commute T (C*A) := by
    exact (classWord_eq_iff_derives g _ _).mpr
      (derives_scalar_commute g _ [.CZ i j hij, .H i, .H j])
  have hWB : Commute W (C*A) := by
    rw [hW]
    exact hT.mul_left ((Commute.refl (C*A)).pow_left 3)
  have hh := hWB.mul_right hWA.inv_right
  simpa only [mul_assoc, mul_inv_cancel, mul_one] using hh

/-- C12 after explicitly erasing its Pauli correction. -/
theorem symplecticClassWord_CX_conjugate_S (i j : Fin n) (hij : i ≠ j) :
    symplecticClassWord g (CX i j hij)*symplecticClassWord g [.S j]*
      (symplecticClassWord g (CX i j hij))⁻¹ =
        symplecticClassWord g [.S j]*symplecticClassWord g [.S i]*
          (symplecticClassWord g [.CZ i j hij])⁻¹ := by
  have h := congrArg (presentedToSymplectic g) (classWord_CX_conjugate_S g i j hij)
  simpa only [map_mul, map_inv, presentedToSymplectic_classWord, symplecticClassWord_Z,
    mul_one] using h

/-- Conjugation of CZ by CX follows from the two orientations of C12. -/
theorem symplecticClassWord_CX_conjugate_CZ (i j : Fin n) (hij : i ≠ j) :
    symplecticClassWord g (CX i j hij)*symplecticClassWord g [.CZ i j hij]*
      (symplecticClassWord g (CX i j hij))⁻¹ =
        (symplecticClassWord g [.S i])⁻¹^2*symplecticClassWord g [.CZ i j hij] := by
  let A := symplecticClassWord g (CX i j hij)
  let S := symplecticClassWord g [.S i]
  let T := symplecticClassWord g [.S j]
  let C := symplecticClassWord g [.CZ i j hij]
  let F := MulAut.conj A
  have hFS : F S = S := by
    have h := congrArg (presentedToSymplectic g) (classWord_CX_commute_S_control g i j hij).eq
    change A*S = S*A at h
    change A*S*A⁻¹ = S
    rw [h]; group
  have hFT : F T = T*S*C⁻¹ := symplecticClassWord_CX_conjugate_S g i j hij
  have hSC : Commute S C := by
    have h := congrArg (presentedToSymplectic g) (classWord_CZ_commute_S_first g i j hij).eq
    exact h.symm
  have hminus : A⁻¹*T*A = T*S*C := by
    have h := congrArg (presentedToSymplectic g) (classWord_CX_inv_conjugate_S g i j hij)
    simpa only [map_mul, map_inv, presentedToSymplectic_classWord] using h
  have he : 1 = (S*C⁻¹*S)*F C := by
    apply mul_left_cancel (a := T)
    have hh := congrArg F hminus
    have hhleft : F (A⁻¹*T*A) = T := by simp only [F, MulAut.conj_apply]; group
    rw [hhleft, map_mul, map_mul, hFT, hFS] at hh
    simpa only [mul_one, mul_assoc] using hh
  have he' : F C = (S*C⁻¹*S)⁻¹ := eq_inv_of_mul_eq_one_right he.symm
  change F C = S⁻¹^2*C
  rw [he']
  have hc := hSC.inv_left.eq
  simp only [mul_inv_rev, inv_inv, pow_two]
  rw [mul_assoc, ← hc, ← mul_assoc]

private theorem quadratic_conjugation_pow {G : Type*} [Group G]
    (A S T C : G) (hAS : Commute A S) (hSC : Commute S C)
    (hT : A*T*A⁻¹ = T*S*C⁻¹) (hC : A*C*A⁻¹ = S⁻¹^2*C) (k : ℕ) :
    A^k*T*(A^k)⁻¹ = T*S^(k*k)*(C⁻¹)^k := by
  let F := MulAut.conj A
  have hFS : F S = S := by change A*S*A⁻¹=S; rw [hAS.eq]; group
  have hFC : F C = S⁻¹^2*C := hC
  have hFT : F T = T*S*C⁻¹ := hT
  induction k with
  | zero => simp
  | succ k ih =>
    have hpow : A^(k+1)*T*(A^(k+1))⁻¹ = F (A^k*T*(A^k)⁻¹) := by
      simp only [F, MulAut.conj_apply, pow_succ', mul_inv_rev]; group
    rw [hpow, ih, map_mul, map_mul, map_pow, map_pow, map_inv, hFS, hFT, hFC]
    have hc : (S⁻¹^2*C)⁻¹ = S^2*C⁻¹ := by
      simp only [mul_inv_rev, inv_pow, inv_inv]
      exact (hSC.pow_left 2).inv_right.symm.eq
    rw [hc, (hSC.pow_left 2).inv_right.mul_pow]
    have hcp := (hSC.pow_left (k*k)).inv_right.symm.eq
    calc
      _ = T*S*(C⁻¹*S^(k*k))*(S^2)^k*(C⁻¹)^k := by simp only [mul_assoc]
      _ = T*(S*S^(k*k)*(S^2)^k)*(C⁻¹*(C⁻¹)^k) := by
        rw [hcp]
        have hck := ((hSC.pow_left 2).pow_left k).inv_right.symm.eq
        simp only [mul_assoc]
        rw [← mul_assoc C⁻¹ ((S^2)^k) ((C⁻¹)^k), hck]
        simp only [mul_assoc]
      _ = _ := by
        simp only [← pow_mul, ← pow_add, ← pow_succ']
        congr 2
        ring_nf

/-- Iterated C12 gives the quadratic diagonal correction for any CX power. -/
theorem symplecticClassWord_CXpow_conjugate_S (i j : Fin n) (hij : i ≠ j) (k : ℕ) :
    symplecticClassWord g (CX i j hij)^k*symplecticClassWord g [.S j]*
      (symplecticClassWord g (CX i j hij)^k)⁻¹ =
        symplecticClassWord g [.S j]*symplecticClassWord g [.S i] ^ (k*k)*
          (symplecticClassWord g [.CZ i j hij])⁻¹^k := by
  apply quadratic_conjugation_pow
  · exact congrArg (presentedToSymplectic g) (classWord_CX_commute_S_control g i j hij).eq
  · exact (congrArg (presentedToSymplectic g) (classWord_CZ_commute_S_first g i j hij).eq).symm
  · exact symplecticClassWord_CX_conjugate_S g i j hij
  · exact symplecticClassWord_CX_conjugate_CZ g i j hij

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
/-- Residue addition for CZ powers in the syntactic Pauli erasure. -/
theorem symplecticClassWord_CZexp_add (i j : Fin n) (hij : i ≠ j) (a b : ZMod d) :
    symplecticClassWord g (List.replicate (a+b).val (.CZ i j hij)) =
      symplecticClassWord g (List.replicate a.val (.CZ i j hij))*
        symplecticClassWord g (List.replicate b.val (.CZ i j hij)) := by
  exact ((symplecticClassWord_eq_iff_derives g _ _).mpr
    (derives_symplectic g (derives_CZexp_add g i j hij a b))).symm

/-- Negated field-valued CZ exponents are inverses in the erased presentation. -/
theorem symplecticClassWord_CZexp_neg (i j : Fin n) (hij : i ≠ j) (a : ZMod d) :
    symplecticClassWord g (List.replicate (-a).val (.CZ i j hij)) =
      (symplecticClassWord g (List.replicate a.val (.CZ i j hij)))⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← symplecticClassWord_CZexp_add]
  simp

/-- The powered controlled-addition/S rule with finite-field exponents,
including its quadratic control-wire phase and inverse controlled phase. -/
theorem symplecticClassWord_CXpower_S_target (i j : Fin n) (hij : i ≠ j) (k : ZMod d) :
    symplecticClassWord g (power (CX i j hij) k.val)*symplecticClassWord g [.S j] =
      symplecticClassWord g [.S j]*symplecticClassWord g (Sexp i (k*k))*
        symplecticClassWord g (List.replicate (-k).val (.CZ i j hij))*
          symplecticClassWord g (power (CX i j hij) k.val) := by
  have hs := symplecticClassWord_Sexp_nsmul g i k k.val
  simp only [ZMod.natCast_zmod_val, Sexp, symplecticClassWord_replicate, ← pow_mul] at hs
  have hc : symplecticClassWord g (List.replicate (-k).val (.CZ i j hij)) =
      (symplecticClassWord g [.CZ i j hij])⁻¹^k.val := by
    rw [symplecticClassWord_CZexp_neg, symplecticClassWord_replicate, inv_pow]
  simp only [symplecticClassWord_power]
  rw [show symplecticClassWord g (Sexp i (k*k)) =
      symplecticClassWord g [.S i] ^ (k.val*k.val) by
        simpa only [Sexp, symplecticClassWord_replicate] using hs, hc]
  have h := symplecticClassWord_CXpow_conjugate_S g i j hij k.val
  have hh := congrArg (fun q : PresentedSymplectic g n =>
    q*symplecticClassWord g (CX i j hij)^k.val) h
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh

/-- H squared on the control inverts the actual controlled-addition word. -/
theorem classWord_H_sq_conjugate_CX_control (i j : Fin n) (hij : i ≠ j) :
    classWord g [.H i] ^ 2 * classWord g (CX i j hij) * (classWord g [.H i] ^ 2)⁻¹ =
      (classWord g (CX i j hij))⁻¹ := by
  let F := MulAut.conj (classWord g [.H i] ^ 2)
  have hH : F (classWord g [.H j]) = classWord g [.H j] := by
    have h := (classWord_disjoint g (.H i) (.H j) (by simpa [Gate.support] using hij.symm)).pow_left 2
    change classWord g [.H i] ^ 2*classWord g [.H j]*(classWord g [.H i] ^ 2)⁻¹ = _
    rw [h.eq]; group
  have hC : F (classWord g [.CZ i j hij]) = (classWord g [.CZ i j hij])⁻¹ :=
    classWord_H_sq_conjugate_CZ_left g i j hij
  change F (classWord g (CX i j hij)) = (classWord g (CX i j hij))⁻¹
  rw [classWord_CX_conjugate, map_mul, map_mul, map_inv, hH, hC]
  group

/-- Field-valued powers of CX add using its derived order-d relation. -/
theorem classWord_CXpower_add (i j : Fin n) (hij : i ≠ j) (a b : ZMod d) :
    classWord g (power (CX i j hij) (a+b).val) =
      classWord g (power (CX i j hij) a.val)*classWord g (power (CX i j hij) b.val) := by
  simp only [classWord_power, ZMod.val_add, ← pow_add]
  exact (pow_eq_pow_mod _ (classWord_CX_order g i j hij)).symm

/-- Negating a field-valued CX power produces its genuine group inverse. -/
theorem classWord_CXpower_neg (i j : Fin n) (hij : i ≠ j) (a : ZMod d) :
    classWord g (power (CX i j hij) (-a).val) =
      (classWord g (power (CX i j hij) a.val))⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← classWord_CXpower_add]
  simp

/-- Moving H squared through an arbitrary controlled-addition power negates it. -/
theorem classWord_CXpower_H_sq_control (i j : Fin n) (hij : i ≠ j) (a : ZMod d) :
    classWord g (power (CX i j hij) a.val)*classWord g [.H i] ^ 2 =
      classWord g [.H i] ^ 2*classWord g (power (CX i j hij) (-a).val) := by
  let Q := classWord g [.H i] ^ 2
  let A := classWord g (CX i j hij)
  have h : Q*A⁻¹ = A*Q := by
    have he := congrArg Inv.inv (classWord_H_sq_conjugate_CX_control g i j hij)
    have hf : Q*A⁻¹*Q⁻¹ = A := by simpa only [mul_inv_rev, inv_inv, mul_assoc] using he
    have hh := congrArg (fun q : PresentedCircuit g n => q*Q) hf
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh
  have hh := (show SemiconjBy Q A⁻¹ A from h).pow_right a.val
  rw [classWord_CXpower_neg, classWord_power, ← inv_pow]
  exact hh.symm

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
/-- Multiplication of a CZ exponent is repeated composition by C6. -/
theorem symplecticClassWord_CZexp_nsmul (i j : Fin n) (hij : i ≠ j) (a : ZMod d) (k : ℕ) :
    symplecticClassWord g (List.replicate ((k : ZMod d)*a).val (.CZ i j hij)) =
      symplecticClassWord g (List.replicate a.val (.CZ i j hij))^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul,
      symplecticClassWord_CZexp_add, ih, pow_succ]

/-- The powered-CX conjugation law for an arbitrary target phase exponent. -/
theorem symplecticClassWord_CXpower_conjugate_Sexp (i j : Fin n) (hij : i ≠ j)
    (k t : ZMod d) :
    symplecticClassWord g (power (CX i j hij) k.val)*symplecticClassWord g (Sexp j t)*
      (symplecticClassWord g (power (CX i j hij) k.val))⁻¹ =
        symplecticClassWord g (Sexp j t)*symplecticClassWord g (Sexp i (t*(k*k)))*
          symplecticClassWord g (List.replicate (t*(-k)).val (.CZ i j hij)) := by
  let A := symplecticClassWord g (power (CX i j hij) k.val)
  let T := symplecticClassWord g [.S j]
  let S := symplecticClassWord g (Sexp i (k*k))
  let C := symplecticClassWord g (List.replicate (-k).val (.CZ i j hij))
  have hT : MulAut.conj A T = T*S*C := by
    have h := congrArg (fun q : PresentedSymplectic g n => q*A⁻¹)
      (symplecticClassWord_CXpower_S_target g i j hij k)
    simpa only [MulAut.conj_apply, A, T, S, C, mul_assoc, mul_inv_cancel, mul_one] using h
  have hTS : Commute T S := by
    have h := congrArg (presentedToSymplectic g)
      ((classWord_disjoint g (.S j) (.S i) (by simpa [Gate.support] using hij)).pow_right (k*k).val).eq
    simpa only [map_mul, map_pow, presentedToSymplectic_classWord, T, S, Sexp,
      symplecticClassWord_replicate] using h
  have hTC : Commute T C := by
    have h := congrArg (presentedToSymplectic g)
      (((classWord_CZ_commute_S_right g i j hij).pow_left (-k).val).symm).eq
    simpa only [map_mul, map_pow, presentedToSymplectic_classWord, T, C,
      symplecticClassWord_replicate] using h
  have hSC : Commute S C := by
    have h := congrArg (presentedToSymplectic g)
      (((classWord_CZ_commute_S_first g i j hij).pow_left (-k).val).pow_right (k*k).val).symm.eq
    simpa only [map_mul, map_pow, presentedToSymplectic_classWord, S, C, Sexp,
      symplecticClassWord_replicate] using h
  have he := map_pow (MulAut.conj A) T t.val
  rw [hT, (hTC.mul_left hSC).mul_pow, hTS.mul_pow] at he
  have hs := symplecticClassWord_Sexp_nsmul g i (k*k) t.val
  have hc := symplecticClassWord_CZexp_nsmul g i j hij (-k) t.val
  simp only [ZMod.natCast_zmod_val] at hs hc
  change A*symplecticClassWord g (Sexp j t)*A⁻¹ = _
  rw [hs, hc]
  simpa only [A, T, S, C, Sexp, symplecticClassWord_replicate, MulAut.conj_apply] using he

private theorem conjugate_iterate {G : Type*} [Group G] (A S C : G)
    (hAS : Commute A S) (hC : A*C*A⁻¹=S*C) (k : ℕ) :
    A^k*C*(A^k)⁻¹=S^k*C := by
  let F := MulAut.conj A
  have hFS : F S=S := by change A*S*A⁻¹=S; rw [hAS.eq]; group
  have hFC : F C=S*C := hC
  induction k with
  | zero => simp
  | succ k ih =>
    have hh : A^(k+1)*C*(A^(k+1))⁻¹=F (A^k*C*(A^k)⁻¹) := by
      simp only [F, MulAut.conj_apply, pow_succ', mul_inv_rev]; group
    rw [hh, ih, map_mul, map_pow, hFS, hFC]
    simp only [← mul_assoc, ← pow_succ]

/-- The linear CZ correction under an arbitrary controlled-addition power. -/
theorem symplecticClassWord_CXpower_conjugate_CZ (i j : Fin n) (hij : i ≠ j)
    (k : ZMod d) :
    symplecticClassWord g (power (CX i j hij) k.val)*symplecticClassWord g [.CZ i j hij]*
      (symplecticClassWord g (power (CX i j hij) k.val))⁻¹ =
        symplecticClassWord g (Sexp i (-2*k))*symplecticClassWord g [.CZ i j hij] := by
  have hAS : Commute (symplecticClassWord g (CX i j hij))
      ((symplecticClassWord g [.S i])⁻¹^2) := by
    have h : Commute (symplecticClassWord g (CX i j hij)) (symplecticClassWord g [.S i]) :=
      congrArg (presentedToSymplectic g) (classWord_CX_commute_S_control g i j hij).eq
    exact h.inv_right.pow_right 2
  have he := conjugate_iterate _ _ _ hAS (symplecticClassWord_CX_conjugate_CZ g i j hij) k.val
  have hs := symplecticClassWord_Sexp_nsmul g i (-1) (2*k.val)
  rw [symplecticClassWord_Sexp_neg, symplecticClassWord_Sexp_one] at hs
  have hfield : ((2*k.val : ℕ) : ZMod d)*(-1)=-2*k := by
    simp only [Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val]; ring
  rw [hfield] at hs
  rw [symplecticClassWord_power, hs, pow_mul]
  exact he

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
/-- A Fourier gate commutes with an erased multiplier on a different wire,
by the multiplier's literal H/S expansion and structural interchange. -/
theorem symplecticClassWord_H_commute_multiplier_offwire (i j : Fin n) (hij : i ≠ j)
    (a : (ZMod d)ˣ) :
    Commute (symplecticClassWord g [.H j]) (symplecticClassWord g (multiplier i a)) := by
  have hh : Commute (symplecticClassWord g [.H j]) (symplecticClassWord g [.H i]) :=
    congrArg (presentedToSymplectic g)
      (classWord_disjoint g (.H j) (.H i) (by simpa [Gate.support] using hij)).eq
  have hs (b : ZMod d) : Commute (symplecticClassWord g [.H j]) (symplecticClassWord g (Sexp i b)) := by
    have ht := congrArg (presentedToSymplectic g)
      ((classWord_disjoint g (.H j) (.S i) (by simpa [Gate.support] using hij)).pow_right b.val).eq
    simpa only [map_mul, map_pow, presentedToSymplectic_classWord, Sexp,
      symplecticClassWord_replicate] using ht
  rw [symplecticClassWord_multiplier_expand]
  exact ((((hs _).mul_right hh).mul_right (hs _)).mul_right hh).mul_right (hs _) |>.mul_right hh

/-- Every expanded CX power is Fourier conjugation of the corresponding CZ power. -/
theorem symplecticClassWord_CXpower_expand (i j : Fin n) (hij : i ≠ j) (k : ℕ) :
    symplecticClassWord g (power (CX i j hij) k) =
      (symplecticClassWord g [.H j])⁻¹*symplecticClassWord g [.CZ i j hij] ^ k*
        symplecticClassWord g [.H j] := by
  have he := congrArg (presentedToSymplectic g) (classWord_CX_conjugate g i j hij)
  simp only [map_mul, map_inv, presentedToSymplectic_classWord] at he
  rw [symplecticClassWord_power, he]
  simpa only [inv_inv] using
    (conj_pow (a := (symplecticClassWord g [.H j])⁻¹) (b := symplecticClassWord g [.CZ i j hij]) (i := k))

/-- C9 for every unit and every power of the actual controlled-addition word. -/
theorem symplecticClassWord_CXpower_multiplier_control (i j : Fin n) (hij : i ≠ j)
    (a : (ZMod d)ˣ) (b : ZMod d) :
    symplecticClassWord g (power (CX i j hij) b.val)*symplecticClassWord g (multiplier i a) =
      symplecticClassWord g (multiplier i a)*
        symplecticClassWord g (power (CX i j hij) (b*(a : ZMod d)).val) := by
  let H := symplecticClassWord g [.H j]
  let C := symplecticClassWord g [.CZ i j hij]
  let M := symplecticClassWord g (multiplier i a)
  have hc : C^b.val*M=M*C^(b*(a : ZMod d)).val := by
    simpa only [map_mul, map_pow, presentedToSymplectic_classWord] using
      congrArg (presentedToSymplectic g) (classWord_CZpow_multiplier_left g Fact.out i j hij a b)
  have hh : Commute H M := symplecticClassWord_H_commute_multiplier_offwire g i j hij a
  simp only [symplecticClassWord_CXpower_expand]
  change H⁻¹*C^b.val*H*M=M*(H⁻¹*C^(b*(a : ZMod d)).val*H)
  calc
    _ = H⁻¹*C^b.val*(H*M) := by group
    _ = H⁻¹*C^b.val*(M*H) := by rw [hh.eq]
    _ = H⁻¹*(C^b.val*M)*H := by group
    _ = H⁻¹*(M*C^(b*(a : ZMod d)).val)*H := by rw [hc]
    _ = (H⁻¹*M)*C^(b*(a : ZMod d)).val*H := by group
    _ = _ := by rw [hh.inv_left.eq]; group

end QuditClifford.Circuit
namespace QuditClifford.NormalBoxes
open Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ)

/-- B with nonzero a absorbs S on its first wire by C1 exponent addition. -/
theorem derives_B_S_left_nonzero (a b : ZMod d) (ha : a ≠ 0)
    (i j : Fin n) (hij : i ≠ j) :
    Derives g (bWord a b i j hij ++ [.S i]) (bWord a (b-a) i j hij) := by
  have he : -b/a+1 = -(b-a)/a := by field_simp; ring
  have hr := (derives_Sexp_S g i (-b/a)).append_left
    (Circuit.SWAP (d := d) i j hij ++ Circuit.power (Circuit.CX i j hij) a.val ++ [.H i])
  rw [he] at hr
  simpa only [bWord, if_neg ha, List.append_assoc] using hr

/-- B with a=0 transports its control-wire S through CX powers and SWAP. -/
theorem derives_B_S_left_zero (b : ZMod d) (i j : Fin n) (hij : i ≠ j) :
    Derives g (bWord 0 b i j hij ++ [.S i]) ([.S j] ++ bWord 0 b i j hij) := by
  apply (classWord_eq_iff_derives g _ _).mp
  simp only [bWord, if_pos rfl, ↓reduceIte, classWord_append, classWord_power]
  have hc := ((classWord_CX_commute_S_control g i j hij).pow_left b.val).eq
  rw [mul_assoc, hc, ← mul_assoc, classWord_SWAP_S_left, mul_assoc]

/-- The B_00 SWAP transports S from the second wire to the first wire. -/
theorem derives_B_S_right_zero_zero (i j : Fin n) (hij : i ≠ j) :
    Derives g (bWord (0 : ZMod d) 0 i j hij ++ [.S j])
      ([.S i] ++ bWord (0 : ZMod d) 0 i j hij) := by
  apply (classWord_eq_iff_derives g _ _).mp
  simpa only [bWord, if_pos rfl, ZMod.val_zero, power_zero,
    List.append_nil, classWord_append] using classWord_SWAP_S_right g i j hij

/-- The B_00 SWAP transports H from the first wire to the second wire. -/
theorem derives_B_H_zero_zero (i j : Fin n) (hij : i ≠ j) :
    Derives g (bWord (0 : ZMod d) 0 i j hij ++ [.H i])
      ([.H j] ++ bWord (0 : ZMod d) 0 i j hij) := by
  apply (classWord_eq_iff_derives g _ _).mp
  simpa only [bWord, if_pos rfl, ZMod.val_zero, power_zero,
    List.append_nil, classWord_append] using classWord_SWAP_H_left g i j hij

/-- B_0b with b nonzero absorbs H by its literal Figure 6 expansion. -/
theorem derives_B_H_zero_nonzero (b : ZMod d) (hb : b ≠ 0)
    (i j : Fin n) (hij : i ≠ j) :
    Derives g (bWord 0 b i j hij ++ [.H i]) (bWord b 0 i j hij) := by
  simp only [bWord, if_pos rfl, if_neg hb, neg_zero, zero_div, Sexp,
    ZMod.val_zero, List.replicate_zero, List.append_nil]
  exact .refl _

variable [Fact (Odd d)] [Fact (orderOf g = d-1)]

/-- Target-wire S through the a=0 B branch; this includes b=0 and b≠0. -/
theorem symplecticDerives_B_S_right_zero (b : ZMod d)
    (i j : Fin n) (hij : i ≠ j) :
    SymplecticDerives g (bWord 0 b i j hij ++ [.S j])
      ([.S i] ++ Sexp j (b*b) ++ List.replicate (-b).val (.CZ i j hij) ++
        bWord 0 b i j hij) := by
  apply (symplecticClassWord_eq_iff_derives g _ _).mp
  let W := symplecticClassWord g (Circuit.SWAP (d := d) i j hij)
  have hT : W*symplecticClassWord g [.S j] = symplecticClassWord g [.S i]*W :=
    congrArg (presentedToSymplectic g) (classWord_SWAP_S_right g i j hij)
  have hS : W*symplecticClassWord g (Sexp i (b*b)) =
      symplecticClassWord g (Sexp j (b*b))*W := by
    have hh := congrArg (presentedToSymplectic g) (classWord_SWAP_S_left g i j hij)
    have hp := (show SemiconjBy W (symplecticClassWord g [.S i])
      (symplecticClassWord g [.S j]) from hh).pow_right (b*b).val
    simpa only [Sexp, symplecticClassWord_replicate] using hp
  have hC : W*symplecticClassWord g (List.replicate (-b).val (.CZ i j hij)) =
      symplecticClassWord g (List.replicate (-b).val (.CZ i j hij))*W := by
    have hh : Commute W (symplecticClassWord g [.CZ i j hij]) :=
      congrArg (presentedToSymplectic g) (classWord_SWAP_commute_CZ g i j hij).eq
    simpa only [symplecticClassWord_replicate] using (hh.pow_right (-b).val).eq
  simp only [bWord, if_pos rfl, ↓reduceIte, symplecticClassWord_append]
  change (W*symplecticClassWord g (Circuit.power (Circuit.CX i j hij) b.val))*
    symplecticClassWord g [.S j] = _
  rw [mul_assoc, symplecticClassWord_CXpower_S_target]
  simp only [← mul_assoc]
  rw [hT]
  simp only [mul_assoc]
  rw [← mul_assoc W, hS]
  simp only [mul_assoc]
  rw [← mul_assoc W, hC]
  simp only [mul_assoc]
  rfl

/-- Target-wire S through every nonzero-a B box. -/
theorem symplecticDerives_B_S_right_nonzero (a b : ZMod d) (ha : a ≠ 0)
    (i j : Fin n) (hij : i ≠ j) :
    SymplecticDerives g (bWord a b i j hij ++ [.S j])
      ([.S i] ++ Sexp j (a*a) ++ List.replicate (-a).val (.CZ i j hij) ++
        bWord a b i j hij) := by
  have ht : Commute (classWord g [.H i]*classWord g (Sexp i (-b/a))) (classWord g [.S j]) := by
    have hh := classWord_disjoint g (.H i) (.S j) (by simpa [Gate.support] using hij.symm)
    have hs := classWord_disjoint g (.S i) (.S j) (by simpa [Gate.support] using hij.symm)
    rw [Sexp, classWord_replicate]
    exact hh.mul_left (hs.pow_left _)
  have hs : symplecticClassWord g [.H i]*symplecticClassWord g (Sexp i (-b/a))*
      symplecticClassWord g [.S j] =
        symplecticClassWord g [.S j]*(symplecticClassWord g [.H i]*symplecticClassWord g (Sexp i (-b/a))) :=
    congrArg (presentedToSymplectic g) ht.eq
  have hb := (symplecticClassWord_eq_iff_derives g _ _).mpr
    (symplecticDerives_B_S_right_zero g a i j hij)
  simp only [bWord, if_pos rfl, ↓reduceIte, symplecticClassWord_append] at hb
  apply (symplecticClassWord_eq_iff_derives g _ _).mp
  simp only [bWord, if_neg ha, symplecticClassWord_append]
  calc
    _ = (symplecticClassWord g (Circuit.SWAP (d := d) i j hij)*
        symplecticClassWord g (Circuit.power (Circuit.CX i j hij) a.val))*
        ((symplecticClassWord g [.H i]*symplecticClassWord g (Sexp i (-b/a)))*symplecticClassWord g [.S j]) := by
      simp only [mul_assoc]
    _ = _ := by rw [hs]; simp only [← mul_assoc]; rw [hb]; simp only [mul_assoc]

/-- For b=0 and a nonzero, the B Fourier case follows from controlled-addition
inversion and the SWAP/H transport. This branch already holds exactly. -/
theorem derives_B_H_nonzero_zero (a : ZMod d) (ha : a ≠ 0)
    (i j : Fin n) (hij : i ≠ j) :
    Derives g (bWord a 0 i j hij ++ [.H i])
      ([.H j, .H j] ++ bWord 0 (-a) i j hij) := by
  apply (classWord_eq_iff_derives g _ _).mp
  have ht := (show SemiconjBy (classWord g (Circuit.SWAP (d := d) i j hij))
    (classWord g [.H i]) (classWord g [.H j]) from classWord_SWAP_H_left g i j hij).pow_right 2
  simp only [bWord, if_neg ha, if_pos rfl, neg_zero, zero_div, Sexp, ZMod.val_zero,
    List.replicate_zero, List.append_nil, classWord_append]
  change (classWord g (Circuit.SWAP (d := d) i j hij)*classWord g (Circuit.power (Circuit.CX i j hij) a.val)*
    classWord g [.H i])*classWord g [.H i] =
      (classWord g [.H j]*classWord g [.H j])*(classWord g (Circuit.SWAP (d := d) i j hij)*
        classWord g (Circuit.power (Circuit.CX i j hij) (-a).val))
  rw [mul_assoc, ← pow_two, mul_assoc, classWord_CXpower_H_sq_control,
    ← mul_assoc, ht]
  simp only [pow_two, mul_assoc]

/-- The remaining Fourier-through-B branch, with both coordinates nonzero.
The correction is written S(a/b) M(b/a), equivalent by C4 to the source's
M(b/a) S(b/a) in the selected raw-multiplier convention. -/
theorem symplecticDerives_B_H_nonzero_nonzero (a b : ZMod d) (ha : a ≠ 0) (hb : b ≠ 0)
    (i j : Fin n) (hij : i ≠ j) :
    SymplecticDerives g (bWord a b i j hij ++ [.H i])
      (Sexp j (a/b) ++ Circuit.multiplier j (Units.mk0 (b/a) (div_ne_zero hb ha)) ++
        bWord b (-a) i j hij) := by
  let x := Units.mk0 (-b/a) (div_ne_zero (neg_ne_zero.mpr hb) ha)
  let v := Units.mk0 (b/a) (div_ne_zero hb ha)
  let W := symplecticClassWord g (Circuit.SWAP (d := d) i j hij)
  let H := symplecticClassWord g [.H i]
  let A (r : ZMod d) := symplecticClassWord g (Circuit.power (Circuit.CX i j hij) r.val)
  let Si (r : ZMod d) := symplecticClassWord g (Sexp i r)
  let Sj (r : ZMod d) := symplecticClassWord g (Sexp j r)
  let Mi := symplecticClassWord g (Circuit.multiplier i v)
  let Mj := symplecticClassWord g (Circuit.multiplier j v)
  have hx : -x = v := by ext; dsimp [x, v]; ring
  have hxi : -(↑x⁻¹ : ZMod d) = a/b := by dsimp [x]; field_simp
  have hh : H*Si (-b/a)*H=Si (a/b)*Mi*H*Si (a/b) := by
    have ht := symplecticClassWord_H_Sexp_H g i x
    rw [hx, hxi] at ht
    exact ht
  have hs : W*Si (a/b)=Sj (a/b)*W := by
    exact (symplecticClassWord_eq_iff_derives g _ _).mpr
      (derives_symplectic g (derives_SWAP_Sexp_left g i j hij (a/b)))
  have hm : W*Mi=Mj*W := by
    exact (symplecticClassWord_eq_iff_derives g _ _).mpr
      (derives_symplectic g (derives_SWAP_multiplier_left g i j hij v))
  have hc : Commute (A a) (Si (a/b)) := by
    have ht := ((classWord_CX_commute_S_control g i j hij).pow_left a.val).pow_right (a/b).val
    simpa only [A, Si, Sexp, classWord_replicate, symplecticClassWord_replicate,
      symplecticClassWord_power, map_mul, map_pow, presentedToSymplectic_classWord] using
      congrArg (presentedToSymplectic g) ht.eq
  have hcm : A a*Mi=Mi*A b := by
    have ht := symplecticClassWord_CXpower_multiplier_control g i j hij v a
    have he : a*(v : ZMod d)=b := by dsimp [v]; field_simp
    rw [he] at ht
    exact ht
  have ht : W*A a*H*Si (-b/a)*H=Sj (a/b)*Mj*(W*A b*H*Si (a/b)) := by
    calc
      _ = W*A a*(H*Si (-b/a)*H) := by group
      _ = W*A a*(Si (a/b)*Mi*H*Si (a/b)) := by rw [hh]
      _ = W*(A a*Si (a/b))*Mi*H*Si (a/b) := by group
      _ = W*(Si (a/b)*A a)*Mi*H*Si (a/b) := by rw [hc.eq]
      _ = (W*Si (a/b))*(A a*Mi)*H*Si (a/b) := by group
      _ = (Sj (a/b)*W)*(Mi*A b)*H*Si (a/b) := by rw [hs, hcm]
      _ = Sj (a/b)*(W*Mi)*A b*H*Si (a/b) := by group
      _ = _ := by rw [hm]; group
  apply (symplecticClassWord_eq_iff_derives g _ _).mp
  simpa only [bWord, if_neg ha, if_neg hb, neg_neg, symplecticClassWord_append,
    W, A, H, Si, Sj, Mi, Mj, v] using ht

/-- The same final B case in the source's multiplier-before-S order, translated
from its inverse-scaling multiplier to the selected raw multiplier. -/
theorem symplecticDerives_B_H_nonzero_nonzero_source (a b : ZMod d) (ha : a ≠ 0) (hb : b ≠ 0)
    (i j : Fin n) (hij : i ≠ j) :
    SymplecticDerives g (bWord a b i j hij ++ [.H i])
      (Circuit.multiplier j (Units.mk0 (b/a) (div_ne_zero hb ha)) ++ Sexp j (b/a) ++
        bWord b (-a) i j hij) := by
  let v := Units.mk0 (b/a) (div_ne_zero hb ha)
  have hc := symplecticClassWord_multiplier_Sexp g Fact.out j v (b/a)
  have he : (b/a)*(↑v⁻¹ : ZMod d)^2 = a/b := by
    dsimp [v]
    field_simp
    ring
  rw [he] at hc
  have h := (symplecticClassWord_eq_iff_derives g _ _).mpr
    (symplecticDerives_B_H_nonzero_nonzero g a b ha hb i j hij)
  apply (symplecticClassWord_eq_iff_derives g _ _).mp
  simp only [symplecticClassWord_append] at h ⊢
  change _ = (symplecticClassWord g (Circuit.multiplier j v)*symplecticClassWord g (Sexp j (b/a)))*_
  rw [hc]
  exact h

end QuditClifford.NormalBoxes
