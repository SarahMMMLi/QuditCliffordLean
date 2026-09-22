import QuditClifford.SymplecticTwoWireA
import QuditClifford.SymplecticTwoWireB
import QuditClifford.RelabelRewrites

/-!
# A syntactic two-wire Bruhat relation

The proof uses the expanded SWAP involution, Fourier inversion, and the
all-unit multiplier/CZ rules. It takes place in the presented group.
-/

noncomputable section
namespace QuditClifford.Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

private abbrev H (i : Fin n) := symplecticClassWord g [.H i]
private abbrev C (i j : Fin n) (hij : i ≠ j) (t : ZMod d) :=
  symplecticClassWord g (List.replicate t.val (.CZ i j hij))
private abbrev M (i : Fin n) (a : (ZMod d)ˣ) :=
  symplecticClassWord g (multiplier i a)
private abbrev W (i j : Fin n) (hij : i ≠ j) :=
  symplecticClassWord g (SWAP (d := d) i j hij)

set_option linter.unusedSectionVars false in
private theorem H_commute (i j : Fin n) (hij : i ≠ j) : Commute (H g i) (H g j) :=
  congrArg (presentedToSymplectic g)
    (classWord_disjoint g (.H i) (.H j) (by simpa [Gate.support] using hij.symm)).eq

set_option linter.unusedSectionVars false in
private theorem C_one (i j : Fin n) (hij : i ≠ j) :
    C g i j hij 1 = symplecticClassWord g [.CZ i j hij] := by
  simp only [C, ZMod.val_one, List.replicate_succ, List.replicate_zero]

/-- Fourier-square inversion of every residue power of CZ. -/
theorem symplecticClassWord_H_sq_CZexp_left (i j : Fin n) (hij : i ≠ j) (t : ZMod d) :
    H g i ^2 * C g i j hij t = C g i j hij (-t) * H g i ^2 := by
  have h := congrArg (presentedToSymplectic g) (classWord_H_sq_conjugate_CZ_left g i j hij)
  simp only [map_mul, map_pow, map_inv, presentedToSymplectic_classWord] at h
  have h' : SemiconjBy (H g i ^2) (symplecticClassWord g [.CZ i j hij])
      (symplecticClassWord g [.CZ i j hij])⁻¹ := by
    change H g i ^2 * symplecticClassWord g [.CZ i j hij] * (H g i ^2)⁻¹ = _ at h
    calc
      _ = (H g i ^2 * symplecticClassWord g [.CZ i j hij] * (H g i ^2)⁻¹) * H g i ^2 := by group
      _ = _ := by rw [h]
  change _ = symplecticClassWord g (List.replicate (-t).val (.CZ i j hij)) * _
  rw [symplecticClassWord_CZexp_neg]
  simpa only [C, symplecticClassWord_replicate, inv_pow] using (h'.pow_right t.val).eq

theorem symplecticClassWord_H_sq_CZexp_right (i j : Fin n) (hij : i ≠ j) (t : ZMod d) :
    H g j ^2 * C g i j hij t = C g i j hij (-t) * H g j ^2 := by
  have h := congrArg (presentedToSymplectic g) (classWord_H_sq_conjugate_CZ_right g i j hij)
  simp only [map_mul, map_pow, map_inv, presentedToSymplectic_classWord] at h
  have h' : SemiconjBy (H g j ^2) (symplecticClassWord g [.CZ i j hij])
      (symplecticClassWord g [.CZ i j hij])⁻¹ := by
    change H g j ^2 * symplecticClassWord g [.CZ i j hij] * (H g j ^2)⁻¹ = _ at h
    calc
      _ = (H g j ^2 * symplecticClassWord g [.CZ i j hij] * (H g j ^2)⁻¹) * H g j ^2 := by group
      _ = _ := by rw [h]
  change _ = symplecticClassWord g (List.replicate (-t).val (.CZ i j hij)) * _
  rw [symplecticClassWord_CZexp_neg]
  simpa only [C, symplecticClassWord_replicate, inv_pow] using (h'.pow_right t.val).eq

private theorem four (i : Fin n) : H g i ^4=1 := by
  have he := (symplecticClassWord_eq_iff_derives g _ _).mpr
    (derives_symplectic g (derives_H_four Fact.out g Fact.out i))
  simpa only [H, symplecticClassWord_replicate, symplecticClassWord_nil] using he

/-- A rearrangement of the literal SWAP cube and its involution relation. -/
theorem symplecticClassWord_double_H_CZ_factor (i j : Fin n) (hij : i ≠ j) :
    (H g i * H g j) * C g i j hij 1 * (H g i * H g j) =
    H g i ^2 * C g i j hij 1 * (H g i * H g j) * C g i j hij 1 *
      H g j ^2 * W g i j hij := by
  let Q := H g i * H g j
  let Z := C g i j hij 1
  have hq2 : Q^2=H g i ^2*H g j ^2 := (H_commute g i j hij).mul_pow 2
  have hq4 : Q^4=1 := by rw [(H_commute g i j hij).mul_pow, four, four, one_mul]
  have hqinv : Q⁻¹=Q*Q^2 := by
    apply inv_eq_of_mul_eq_one_right
    calc
      _ = Q^4 := by group
      _ = 1 := hq4
  have hiZ := symplecticClassWord_H_sq_CZexp_left g i j hij (1 : ZMod d)
  have hjZ := symplecticClassWord_H_sq_CZexp_right g i j hij (1 : ZMod d)
  simp only [C, symplecticClassWord_CZexp_neg] at hiZ hjZ
  change H g i ^2*Z=Z⁻¹*H g i ^2 at hiZ
  change H g j ^2*Z=Z⁻¹*H g j ^2 at hjZ
  have hqZ : Commute (Q^2) Z := by
    rw [hq2]
    calc
      _ = H g i ^2*(H g j ^2*Z) := by group
      _ = (H g i ^2*Z⁻¹)*H g j ^2 := by rw [hjZ]; group
      _ = Z*(H g i ^2*H g j ^2) := by
        rw [(show SemiconjBy (H g i ^2) Z Z⁻¹ from hiZ).inv_right]
        simp only [inv_inv, mul_assoc]
  have hw : W g i j hij=(Z*Q)^3 := by
    simp only [W, SWAP, symplecticClassWord_append, symplecticClassWord_scalar,
      one_mul, symplecticClassWord_power, Z, C_one, Q, H, mul_assoc]
    rfl
  have hw2 : W g i j hij*W g i j hij=1 := by
    exact congrArg (presentedToSymplectic g) (classWord_SWAP_sq g i j hij)
  have hwinv : W g i j hij=(W g i j hij)⁻¹ :=
    (inv_eq_of_mul_eq_one_right hw2).symm
  have hfact : (Q*Z*Q)*W g i j hij=H g i ^2*Z*Q*Z*H g j ^2 := by
    calc
      _ = (Q*Z*Q)*((Z*Q)^3)⁻¹ := by rw [hwinv, ← hw]
      _ = Z⁻¹*Q⁻¹*Z⁻¹ := by simp only [pow_succ, pow_zero, one_mul]; group
      _ = Z⁻¹*Q*Z⁻¹*Q^2 := by
        rw [hqinv]
        simp only [mul_assoc]
        rw [hqZ.inv_right.eq]
      _ = (H g i ^2*Z)*Q*Z*H g j ^2 := by
        have hiQ : Commute (H g i ^2) Q :=
          (Commute.refl _).pow_left 2 |>.mul_right ((H_commute g i j hij).pow_left 2)
        symm
        calc
          _ = Z⁻¹*(H g i ^2*Q)*Z*H g j ^2 := by rw [hiZ]; group
          _ = Z⁻¹*Q*(H g i ^2*Z)*H g j ^2 := by rw [hiQ.eq]; group
          _ = Z⁻¹*Q*Z⁻¹*(H g i ^2*H g j ^2) := by rw [hiZ]; group
          _ = _ := by rw [hq2]
  calc
    _ = ((Q*Z*Q)*W g i j hij)*W g i j hij := by rw [mul_assoc (Q*Z*Q), hw2, mul_one]
    _ = _ := by rw [hfact]


/-- The two-wire Bruhat identity, with a unit witnessing `a = 1-y`. -/
theorem symplecticClassWord_double_H_CZexp_bruhat (i j : Fin n) (hij : i ≠ j)
    (y : ZMod d) (a : (ZMod d)ˣ) (ha : (a : ZMod d)=1-y) :
    (H g i*H g j)*C g i j hij 1*(H g i*H g j)*C g i j hij y =
    M g i a*C g i j hij y*((H g i*H g j)*C g i j hij 1*(H g i*H g j))*M g j a := by
  let Q := H g i*H g j
  let O := Q*C g i j hij 1*Q
  have hMiQ : M g i a*Q=Q*M g i a⁻¹ := by
    calc
      _ = (H g i*M g i a⁻¹)*H g j := by
        dsimp only [Q]
        rw [← mul_assoc, symplecticClassWord_multiplier_H]
      _ = _ := by
        rw [mul_assoc, (symplecticClassWord_H_commute_multiplier_offwire g i j hij a⁻¹).symm.eq]
        simp only [Q, H, M, mul_assoc]
  have hMc : M g i a*C g i j hij (a : ZMod d)=C g i j hij 1*M g i a := by
    have h := congrArg (presentedToSymplectic g)
      (classWord_multiplier_CZpow_left g Fact.out i j hij a (a : ZMod d))
    simpa only [map_mul, map_pow, presentedToSymplectic_classWord,
      Units.mul_inv, symplecticClassWord_replicate, C_one] using h
  have hMic : M g i a⁻¹*C g i j hij 1=C g i j hij (a : ZMod d)*M g i a⁻¹ := by
    have h := congrArg (presentedToSymplectic g)
      (classWord_multiplier_CZpow_left g Fact.out i j hij a⁻¹ (1 : ZMod d))
    simpa only [map_mul, map_pow, presentedToSymplectic_classWord,
      inv_inv, one_mul, symplecticClassWord_replicate, C] using h
  have hMiM : M g i a⁻¹*M g i a=1 := by
    rw [show M g i a⁻¹*M g i a = M g i (a⁻¹*a) from
      (symplecticClassWord_multiplier_mul g Fact.out i a⁻¹ a).symm, inv_mul_cancel]
    exact (symplecticClassWord_eq_iff_derives g _ _).mpr
      (derives_symplectic g (derives_multiplier_one g i))
  have haux : C g i j hij 1*Q*C g i j hij (1-y) =
      M g i a*C g i j hij (1-y)*Q*C g i j hij 1*M g i a := by
    rw [← ha]
    symm
    calc
      _ = C g i j hij 1*(M g i a*Q)*C g i j hij 1*M g i a := by rw [hMc]; group
      _ = C g i j hij 1*Q*(M g i a⁻¹*C g i j hij 1)*M g i a := by rw [hMiQ]; group
      _ = C g i j hij 1*Q*C g i j hij (a : ZMod d)*(M g i a⁻¹*M g i a) := by rw [hMic]; group
      _ = _ := by rw [hMiM, mul_one]
  have hIM : Commute (H g i ^2) (M g i a) := by
    change Commute (symplecticClassWord g [.H i] ^2) _
    rw [symplecticClassWord_H_sq]
    change _ * _ = _ * _
    rw [← symplecticClassWord_multiplier_mul g Fact.out,
      ← symplecticClassWord_multiplier_mul g Fact.out, mul_comm (-1) a]
  have hJM : Commute (H g j ^2) (M g i a) :=
    (symplecticClassWord_H_commute_multiplier_offwire g i j hij a).pow_left 2
  have hMW : M g i a*W g i j hij=W g i j hij*M g j a := by
    have hs := (symplecticClassWord_eq_iff_derives g _ _).mpr
      (derives_symplectic g (derives_SWAP_symmetry g i j hij))
    have hm := (symplecticClassWord_eq_iff_derives g _ _).mpr
      (derives_symplectic g (derives_SWAP_multiplier_left g j i hij.symm a))
    simp only [symplecticClassWord_append] at hm
    change W g i j hij = W g j i hij.symm at hs
    change W g j i hij.symm*M g j a=M g i a*W g j i hij.symm at hm
    rw [← hs] at hm
    exact hm.symm
  have hWC : Commute (W g i j hij) (C g i j hij y) := by
    have h := congrArg (presentedToSymplectic g)
      ((classWord_SWAP_commute_CZ g i j hij).pow_right y.val).eq
    simpa only [map_mul, map_pow, presentedToSymplectic_classWord, C,
      symplecticClassWord_replicate] using h
  have hfactor : O=H g i ^2*C g i j hij 1*Q*C g i j hij 1*H g j ^2*W g i j hij :=
    symplecticClassWord_double_H_CZ_factor g i j hij
  have hcadd : C g i j hij 1*C g i j hij (-y)=C g i j hij (1-y) := by
    simpa only [sub_eq_add_neg] using (symplecticClassWord_CZexp_add g i j hij 1 (-y)).symm
  have hcadd' : C g i j hij (1-y)=C g i j hij (-y)*C g i j hij 1 := by
    rw [show 1-y = -y+1 by ring]
    exact symplecticClassWord_CZexp_add g i j hij (-y) 1
  have hI : H g i ^2*C g i j hij (-y)=C g i j hij y*H g i ^2 := by
    simpa only [neg_neg] using symplecticClassWord_H_sq_CZexp_left g i j hij (-y)
  change O*C g i j hij y=M g i a*C g i j hij y*O*M g j a
  calc
    _ = (H g i ^2*C g i j hij 1*Q*C g i j hij 1)*(H g j ^2*C g i j hij y)*W g i j hij := by
      rw [hfactor]
      simp only [mul_assoc]
      rw [hWC.eq]
    _ = H g i ^2*(C g i j hij 1*Q*C g i j hij (1-y))*H g j ^2*W g i j hij := by
      rw [symplecticClassWord_H_sq_CZexp_right]
      simp only [mul_assoc]
      rw [← hcadd]
      group
    _ = (H g i ^2*M g i a)*C g i j hij (1-y)*Q*C g i j hij 1*(M g i a*H g j ^2)*W g i j hij := by
      rw [haux]
      group
    _ = M g i a*(H g i ^2*C g i j hij (-y))*C g i j hij 1*Q*C g i j hij 1*H g j ^2*(M g i a*W g i j hij) := by
      rw [hIM.eq, hJM.symm.eq, hcadd']
      group
    _ = M g i a*C g i j hij y*(H g i ^2*C g i j hij 1*Q*C g i j hij 1*H g j ^2*W g i j hij)*M g j a := by
      rw [hI, hMW]
      group
    _ = _ := by rw [← hfactor]


/-- The same Bruhat relation in controlled-addition coordinates. -/
theorem symplecticClassWord_CX_gaussian_one (i j : Fin n) (hij : i ≠ j)
    (y : ZMod d) (a : (ZMod d)ˣ) (ha : (a : ZMod d)=1-y) :
    (H g j)⁻¹*C g i j hij 1*H g j*((H g i)⁻¹*C g i j hij (-y)*H g i) =
    M g i a⁻¹*((H g i)⁻¹*C g i j hij (-y)*H g i)*
      ((H g j)⁻¹*C g i j hij 1*H g j)*M g j a := by
  let Q := H g i*H g j
  let P := (H g j)⁻¹*Q⁻¹
  let O := Q*C g i j hij 1*Q
  have hIJ := H_commute g i j hij
  have hi : H g i ^2*H g i=(H g i)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    calc
      _ = H g i ^4 := by group
      _ = 1 := four g i
  have hj : H g j ^2*H g j=(H g j)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    calc
      _ = H g j ^4 := by group
      _ = 1 := four g j
  have hj2 : ((H g j)⁻¹)^2=H g j ^2 := by
    apply (mul_left_cancel_iff (a := H g j ^2)).mp
    calc
      H g j ^2*((H g j)⁻¹)^2 = 1 := by group
      _ = H g j ^2*H g j ^2 := by rw [← pow_add]; exact (four g j).symm
  have hP : P=(H g i)⁻¹*H g j ^2 := by
    dsimp only [P, Q]
    rw [mul_inv_rev]
    calc
      _ = (H g i)⁻¹*((H g j)⁻¹)^2 := by
        rw [hIJ.inv_inv.symm.eq, ← mul_assoc, hIJ.inv_inv.symm.eq]
        group
      _ = _ := by rw [hj2]
  have hQI : Q*(H g i)⁻¹=H g j := by
    dsimp only [Q]
    rw [hIJ.eq]
    group
  have hJQ : H g j ^2*Q=H g i*(H g j)⁻¹ := by
    dsimp only [Q]
    rw [← mul_assoc, (hIJ.pow_right 2).symm.eq, mul_assoc, hj]
  have hleft : (H g j)⁻¹*C g i j hij 1*H g j*((H g i)⁻¹*C g i j hij (-y)*H g i) =
      P*(O*C g i j hij y)*(H g i)⁻¹ := by
    calc
      _ = (H g j)⁻¹*C g i j hij 1*(H g j*H g i)*(H g i ^2*C g i j hij (-y))*H g i := by
        rw [← hi]
        group
      _ = (H g j)⁻¹*C g i j hij 1*Q*C g i j hij y*(H g i ^2*H g i) := by
        rw [hIJ.symm.eq, symplecticClassWord_H_sq_CZexp_left, neg_neg]
        dsimp only [Q]
        group
      _ = _ := by rw [hi]; dsimp only [P, O]; group
  have hright : P*C g i j hij y*O*(H g i)⁻¹ =
      ((H g i)⁻¹*C g i j hij (-y)*H g i)*((H g j)⁻¹*C g i j hij 1*H g j) := by
    calc
      _ = (H g i)⁻¹*(H g j ^2*C g i j hij y)*Q*C g i j hij 1*(Q*(H g i)⁻¹) := by
        rw [hP]
        dsimp only [O]
        group
      _ = (H g i)⁻¹*C g i j hij (-y)*(H g j ^2*Q)*C g i j hij 1*H g j := by
        rw [symplecticClassWord_H_sq_CZexp_right, hQI]
        group
      _ = _ := by rw [hJQ]; group
  have hPM : P*M g i a=M g i a⁻¹*P := by
    have hIm : (H g i)⁻¹*M g i a=M g i a⁻¹*(H g i)⁻¹ := by
      have hh := symplecticClassWord_multiplier_H g i a
      change M g i a*H g i=H g i*M g i a⁻¹ at hh
      calc
        _ = (H g i)⁻¹*(M g i a*H g i)*(H g i)⁻¹ := by group
        _ = _ := by rw [hh]; group
    rw [hP]
    calc
      _ = ((H g i)⁻¹*M g i a)*H g j ^2 := by
        rw [mul_assoc, ((symplecticClassWord_H_commute_multiplier_offwire g i j hij a).pow_left 2).eq]
        group
      _ = _ := by rw [hIm]; group
  have hJM : Commute (M g j a) ((H g i)⁻¹) :=
    (symplecticClassWord_H_commute_multiplier_offwire g j i hij.symm a).symm.inv_right
  calc
    _ = P*(O*C g i j hij y)*(H g i)⁻¹ := hleft
    _ = (P*M g i a)*C g i j hij y*O*(M g j a*(H g i)⁻¹) := by
      rw [show O*C g i j hij y=M g i a*C g i j hij y*O*M g j a from
        symplecticClassWord_double_H_CZexp_bruhat g i j hij y a ha]
      group
    _ = M g i a⁻¹*(P*C g i j hij y*O*(H g i)⁻¹)*M g j a := by
      rw [hPM, hJM.eq]
      group
    _ = _ := by rw [hright]; group


set_option linter.unusedSectionVars false in
private theorem M_commute (i : Fin n) (a b : (ZMod d)ˣ) : Commute (M g i a) (M g i b) := by
  change _*_=_*_
  rw [← symplecticClassWord_multiplier_mul g Fact.out,
    ← symplecticClassWord_multiplier_mul g Fact.out, mul_comm a b]

set_option linter.unusedSectionVars false in
/-- Expanded multipliers on different wires commute by structural interchange. -/
theorem symplecticClassWord_multiplier_commute_offwire (i j : Fin n) (hij : i ≠ j)
    (a b : (ZMod d)ˣ) : Commute (M g i a) (M g j b) := by
  have he : Commute (classWord g (multiplier j b)) (classWord g (multiplier i a)) := by
    apply classWord_commute_multiplier_of_avoids
    intro k hk
    have hr : relabel (singleWireEmbedding j) (multiplier (0 : Fin 1) b)=multiplier j b := by
      simp only [relabel_multiplier, singleWireEmbedding, Function.Embedding.coeFn_mk]
    rw [← hr] at hk
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hk
    cases q with
    | scalar => simp [Gate.relabel, Gate.support]
    | H k => simpa [Gate.relabel, Gate.support, singleWireEmbedding] using hij
    | S k => simpa [Gate.relabel, Gate.support, singleWireEmbedding] using hij
    | CZ k l hkl => exact (hkl (Subsingleton.elim _ _)).elim
  exact congrArg (presentedToSymplectic g) he.symm.eq

private theorem M_root_control (i j : Fin n) (hij : i ≠ j) (u : (ZMod d)ˣ) (t : ZMod d) :
    M g i u*((H g j)⁻¹*C g i j hij t*H g j) =
      ((H g j)⁻¹*C g i j hij (t*↑u⁻¹)*H g j)*M g i u := by
  have hH := (symplecticClassWord_H_commute_multiplier_offwire g i j hij u).symm
  have hC : M g i u*C g i j hij t=C g i j hij (t*↑u⁻¹)*M g i u := by
    simpa only [map_mul, map_pow, presentedToSymplectic_classWord, C, symplecticClassWord_replicate] using
      congrArg (presentedToSymplectic g) (classWord_multiplier_CZpow_left g Fact.out i j hij u t)
  calc
    _ = (H g j)⁻¹*(M g i u*C g i j hij t)*H g j := by
      simp only [← mul_assoc]
      rw [hH.inv_right.eq]
    _ = (H g j)⁻¹*C g i j hij (t*↑u⁻¹)*(M g i u*H g j) := by rw [hC]; group
    _ = _ := by rw [hH.eq]; group

private theorem M_root_target (i j : Fin n) (hij : i ≠ j) (u : (ZMod d)ˣ) (t : ZMod d) :
    M g i u*((H g i)⁻¹*C g i j hij t*H g i) =
      ((H g i)⁻¹*C g i j hij (t*↑u)*H g i)*M g i u := by
  have hH : M g i u⁻¹*H g i=H g i*M g i u := by
    simpa only [inv_inv] using symplecticClassWord_multiplier_H g i u⁻¹
  have hHi : M g i u*(H g i)⁻¹=(H g i)⁻¹*M g i u⁻¹ := by
    calc
      _ = (H g i)⁻¹*(H g i*M g i u)*(H g i)⁻¹ := by group
      _ = _ := by rw [← hH]; group
  have hC : M g i u⁻¹*C g i j hij t=C g i j hij (t*↑u)*M g i u⁻¹ := by
    simpa only [map_mul, map_pow, presentedToSymplectic_classWord, C, inv_inv,
      symplecticClassWord_replicate] using
      congrArg (presentedToSymplectic g) (classWord_multiplier_CZpow_left g Fact.out i j hij u⁻¹ t)
  calc
    _ = (H g i)⁻¹*(M g i u⁻¹*C g i j hij t)*H g i := by simp only [← mul_assoc]; rw [hHi]
    _ = (H g i)⁻¹*C g i j hij (t*↑u)*(M g i u⁻¹*H g i) := by rw [hC]; group
    _ = _ := by rw [hH]; group

/-- Gaussian elimination for two opposite controlled-addition roots. -/
theorem symplecticClassWord_CX_gaussian (i j : Fin n) (hij : i ≠ j)
    (c a : (ZMod d)ˣ) (t : ZMod d) (ha : (a : ZMod d)=1+(c : ZMod d)*t) :
    ((H g j)⁻¹*C g i j hij (c : ZMod d)*H g j)*((H g i)⁻¹*C g i j hij t*H g i) =
    M g i a⁻¹*((H g i)⁻¹*C g i j hij t*H g i)*
      ((H g j)⁻¹*C g i j hij (c : ZMod d)*H g j)*M g j a := by
  let K (u : ZMod d) := (H g j)⁻¹*C g i j hij u*H g j
  let L (u : ZMod d) := (H g i)⁻¹*C g i j hij u*H g i
  let N := M g i c⁻¹
  have hNK : N*K 1=K (c : ZMod d)*N := by
    simpa only [inv_inv, one_mul] using M_root_control g i j hij c⁻¹ 1
  have ht : -(-(c : ZMod d)*t)*(↑c⁻¹ : ZMod d)=t := by
    simp only [neg_mul, neg_neg, Units.val_inv_eq_inv_val]
    field_simp
  have hNL : N*L (-(-(c : ZMod d)*t))=L t*N := by
    simpa only [ht] using M_root_target g i j hij c⁻¹ (-(-(c : ZMod d)*t))
  have he : K 1*L (-(-(c : ZMod d)*t))=M g i a⁻¹*L (-(-(c : ZMod d)*t))*K 1*M g j a :=
    symplecticClassWord_CX_gaussian_one g i j hij (-(c : ZMod d)*t) a (by rw [ha]; ring)
  have hNM : Commute N (M g i a⁻¹) := M_commute g i c⁻¹ a⁻¹
  have hNM' : Commute N (M g j a) := symplecticClassWord_multiplier_commute_offwire g i j hij c⁻¹ a
  apply (mul_right_cancel_iff (a := N)).mp
  change (K (c : ZMod d)*L t)*N=(M g i a⁻¹*L t*K (c : ZMod d)*M g j a)*N
  calc
    _ = (N*K 1)*L (-(-(c : ZMod d)*t)) := by rw [hNK]; simp only [mul_assoc]; rw [hNL]
    _ = N*(M g i a⁻¹*L (-(-(c : ZMod d)*t))*K 1*M g j a) := by rw [mul_assoc, he]
    _ = M g i a⁻¹*(N*L (-(-(c : ZMod d)*t)))*K 1*M g j a := by
      rw [← mul_assoc N, ← mul_assoc N, ← mul_assoc N, hNM.eq]
      group
    _ = M g i a⁻¹*L t*(N*K 1)*M g j a := by rw [hNL]; group
    _ = _ := by rw [hNK]; simp only [mul_assoc]; rw [hNM'.eq]

end QuditClifford.Circuit
