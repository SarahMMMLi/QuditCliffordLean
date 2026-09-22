import QuditClifford.SymplecticTwoWireAB
import QuditClifford.SymplecticTwoWireDCZ

/-! # The nonzero/nonzero A-B controlled-phase pivot -/
noncomputable section
namespace QuditClifford.Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

/-- The quadratic CX phase relation gives a CZ-H-CZ pivot at arbitrary
residue exponents, with a nonzero first exponent. -/
theorem symplecticClassWord_CZexp_H_CZexp (i j : Fin n) (hij : i ≠ j)
    (u v : ZMod d) (hu : u ≠ 0) :
    symplecticClassWord g (List.replicate u.val (.CZ i j hij)) *
        symplecticClassWord g [.H j] * symplecticClassWord g (List.replicate v.val (.CZ i j hij)) =
      symplecticClassWord g [.H j] * symplecticClassWord g (Sexp i (-u*v)) *
        symplecticClassWord g (Sexp j (v/u)) *
          symplecticClassWord g (power (CX i j hij) u.val) * symplecticClassWord g (Sexp j (-v/u)) := by
  let H := symplecticClassWord g [.H j]
  let C := symplecticClassWord g (List.replicate v.val (.CZ i j hij))
  let A := symplecticClassWord g (power (CX i j hij) u.val)
  let S := symplecticClassWord g (Sexp i (-u*v))
  let T := symplecticClassWord g (Sexp j (-v/u))
  have hSS : A*T*A⁻¹ = T*S*C := by
    have ht := symplecticClassWord_CXpower_conjugate_Sexp g i j hij u (-v/u)
    have h1 : (-v/u)*(u*u) = -u*v := by field_simp; ring
    have h2 : (-v/u)*(-u) = v := by field_simp
    simpa only [h1, h2] using ht
  have hCC : A*C*A⁻¹ = S*S*C := by
    have ht := symplecticClassWord_CXpower_CZexp g i j hij u v
    have he : -2*u*v = -u*v + -u*v := by ring
    rw [he, symplecticClassWord_Sexp_add] at ht
    have hh := congrArg (fun q => q*A⁻¹) ht
    simpa only [A, C, S, mul_assoc, mul_inv_cancel, mul_one] using hh
  have he : A*C = S*T⁻¹*A*T := by
    calc
      _ = S*S*C*A := by
        have hh := congrArg (fun q => q*A) hCC
        simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh
      _ = S*T⁻¹*(A*T*A⁻¹)*A := by rw [hSS]; group
      _ = _ := by group
  have hA := symplecticClassWord_CXpower_expand_residue g i j hij u
  change A = H⁻¹*symplecticClassWord g (List.replicate u.val (.CZ i j hij))*H at hA
  have hn : symplecticClassWord g (Sexp j (v/u)) = T⁻¹ := by
    simpa only [T, neg_neg, neg_div] using symplecticClassWord_Sexp_neg g j (-v/u)
  rw [hn]
  change _ * H * C = H*S*T⁻¹*A*T
  calc
    _ = H*(A*C) := by rw [show A = _ from hA]; group
    _ = _ := by rw [he]; group

/-- H and H inverse give the same phase conjugation after explicit Z erasure. -/
theorem symplecticClassWord_phase_fourier_conj (i : Fin n) (a : ZMod d) :
    symplecticClassWord g [.H i] * symplecticClassWord g (Sexp i a) *
        (symplecticClassWord g [.H i])⁻¹ =
      (symplecticClassWord g [.H i])⁻¹ * symplecticClassWord g (Sexp i a) *
        symplecticClassWord g [.H i] := by
  let H := symplecticClassWord g [.H i]
  let S := symplecticClassWord g (Sexp i a)
  have hc : Commute (H^2) S := symplecticClassWord_H_sq_commute_Sexp g i a
  change H*S*H⁻¹ = H⁻¹*S*H
  calc
    _ = H⁻¹*(H^2*S)*H⁻¹ := by rw [pow_two]; group
    _ = H⁻¹*(S*H^2)*H⁻¹ := by rw [hc.eq]
    _ = _ := by rw [pow_two]; group

set_option linter.unusedSectionVars false in
private theorem sh_commute (i j : Fin n) (hij : i ≠ j) (a : ZMod d) :
    Commute (symplecticClassWord g (Sexp i a)) (symplecticClassWord g [.H j]) := by
  have h := congrArg (presentedToSymplectic g)
    ((classWord_disjoint g (.S i) (.H j) (by simp [Gate.support, hij, hij.symm])).pow_left a.val).eq
  simpa only [map_mul, map_pow, presentedToSymplectic_classWord, Sexp,
    symplecticClassWord_replicate] using h

/-- A controlled-addition/Fourier pivot, derived from the quadratic phase law. -/
theorem symplecticClassWord_CX_H_CX_pivot (i j : Fin n) (hij : i ≠ j)
    (a c : ZMod d) (hc : c ≠ 0) :
    symplecticClassWord g (power (CX i j hij) c.val) * symplecticClassWord g [.H i] *
        symplecticClassWord g (power (CX i j hij) (-a).val) =
      (symplecticClassWord g [.H i])⁻¹ * symplecticClassWord g (Sexp i (-a/c)) *
        symplecticClassWord g [.H i] * symplecticClassWord g (power (CX i j hij) c.val) *
          symplecticClassWord g [.H i] * symplecticClassWord g (Sexp i (a/c)) *
            ((symplecticClassWord g [.H j])⁻¹ * symplecticClassWord g (Sexp j (a*c)) *
              symplecticClassWord g [.H j]) := by
  let Hi := symplecticClassWord g [.H i]
  let Hj := symplecticClassWord g [.H j]
  let C (x : ZMod d) := symplecticClassWord g (List.replicate x.val (.CZ i j hij))
  let X (x : ZMod d) := symplecticClassWord g (power (CX i j hij) x.val)
  let Si (x : ZMod d) := symplecticClassWord g (Sexp i x)
  let Sj (x : ZMod d) := symplecticClassWord g (Sexp j x)
  have hH : Commute Hi Hj := congrArg (presentedToSymplectic g)
    (classWord_disjoint g (.H i) (.H j) (by simp [Gate.support, hij, hij.symm])).eq
  have hex (x : ZMod d) : X x = Hj⁻¹*C x*Hj := symplecticClassWord_CXpower_expand_residue g i j hij x
  have hp : C c*Hi*C (-a) = Hi*Sj (a*c)*Si (-a/c)*(Hi⁻¹*C c*Hi)*Si (a/c) := by
    have ht := symplecticClassWord_CZexp_H_CZexp g j i hij.symm c (-a) hc
    have hcz := congrArg (presentedToSymplectic g) (classWord_CZ_symmetry g i j hij)
    simp only [presentedToSymplectic_classWord] at hcz
    rw [symplecticClassWord_CXpower_expand_residue] at ht
    simp only [symplecticClassWord_replicate, ← hcz] at ht
    have he : -c * -a = a*c := by ring
    simpa only [Hi, C, Si, Sj, symplecticClassWord_replicate, he, neg_neg] using ht
  have hiSj : Commute Hi (Sj (a*c)) := (sh_commute g j i hij.symm (a*c)).symm
  have hjSi : Commute Hj (Si (-a/c)) := (sh_commute g i j hij (-a/c)).symm
  have sjC : Commute (Sj (a*c)) (C c) := by
    have ht := congrArg (presentedToSymplectic g)
      (((classWord_CZ_commute_S_right g i j hij).symm.pow_left (a*c).val).pow_right c.val).eq
    simpa only [Sj, C, Sexp, symplecticClassWord_replicate, map_mul, map_pow,
      presentedToSymplectic_classWord, Commute, SemiconjBy] using ht
  have sjSi (t : ZMod d) : Commute (Sj (a*c)) (Si t) := by
    have ht := congrArg (presentedToSymplectic g)
      (((classWord_disjoint g (.S j) (.S i) (by simp [Gate.support, hij, hij.symm])).pow_left (a*c).val).pow_right t.val).eq
    simpa only [Sj, Si, Sexp, symplecticClassWord_replicate, map_mul, map_pow,
      presentedToSymplectic_classWord, Commute, SemiconjBy] using ht
  have hP : Hi*Si (-a/c)*Hi⁻¹ = Hi⁻¹*Si (-a/c)*Hi :=
    symplecticClassWord_phase_fourier_conj g i (-a/c)
  let P := Hi⁻¹*Si (-a/c)*Hi
  have hPH : Commute P Hj :=
    ((hH.inv_left.mul_left hjSi.symm).mul_left hH)
  have hrest : Commute (Sj (a*c)) (C c*Hi*Si (a/c)) :=
    (sjC.mul_right hiSj.symm).mul_right (sjSi _)
  have hPS : Commute P (Sj (a*c)) :=
    (hiSj.inv_left.mul_left (sjSi _).symm).mul_left hiSj
  have hHiSi : Commute (Hi*Si (a/c)) Hj := hH.mul_left (sh_commute g i j hij (a/c))
  change X c*Hi*X (-a) = P*X c*Hi*Si (a/c)*(Hj⁻¹*Sj (a*c)*Hj)
  calc
    _ = Hj⁻¹*C c*(Hj*Hi*Hj⁻¹)*C (-a)*Hj := by rw [hex c, hex (-a)]; group
    _ = Hj⁻¹*(C c*Hi*C (-a))*Hj := by rw [hH.symm.eq]; group
    _ = Hj⁻¹*(Hi*Sj (a*c)*Si (-a/c)*(Hi⁻¹*C c*Hi)*Si (a/c))*Hj := by rw [hp]
    _ = Hj⁻¹*(Sj (a*c)*(Hi*Si (-a/c)*Hi⁻¹)*(C c*Hi*Si (a/c)))*Hj := by rw [hiSj.eq]; group
    _ = Hj⁻¹*(Sj (a*c)*P*(C c*Hi*Si (a/c)))*Hj := by rw [hP]
    _ = P*Hj⁻¹*(Sj (a*c)*(C c*Hi*Si (a/c)))*Hj := by
      rw [hPS.symm.eq]
      calc
        _ = (Hj⁻¹*P)*(Sj (a*c)*(C c*Hi*Si (a/c)))*Hj := by group
        _ = _ := by rw [hPH.inv_right.symm.eq]
    _ = P*Hj⁻¹*(C c*Hi*Si (a/c))*(Sj (a*c)*Hj) := by rw [hrest.eq]; group
    _ = _ := by
      rw [hex c]
      calc
        _ = P*Hj⁻¹*C c*((Hi*Si (a/c))*Hj)*Hj⁻¹*(Sj (a*c)*Hj) := by group
        _ = _ := by rw [hHiSi.eq]; group

end QuditClifford.Circuit

namespace QuditClifford.NormalBoxes
open Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

/-- The surviving A label in the nonzero/nonzero controlled-phase pivot. -/
def ABox.nonzeroDifferenceStep (A : ABox (ZMod d)) (ha : A.a ≠ 0) (c : ZMod d) :
    ABox (ZMod d) := ⟨A.a, A.b-c, fun h => ha (congrArg Prod.snd h)⟩

/-- The final nonzero/nonzero AB/CZ branch of Appendix F. The inverse H word
is the literal three-H expansion, and the multiplier convention is Figure 1. -/
theorem symplecticDerives_AB_CZ_nonzero (A : ABox (ZMod d)) (ha : A.a ≠ 0)
    (c k : ZMod d) (hc : c ≠ 0) (i j : Fin n) (hij : i ≠ j) :
    SymplecticDerives g (bWord c k i j hij ++ A.toWord j ++ [.CZ i j hij])
      (inverseWord d [.H j] ++ Sexp j (-A.a/c) ++ [.H j] ++
        bWord c (k-A.a) i j hij ++ (A.nonzeroDifferenceStep ha c).toWord j) := by
  let a : (ZMod d)ˣ := Units.mk0 A.a ha
  let H := symplecticClassWord g [.H i]
  let J := symplecticClassWord g [.H j]
  let W := symplecticClassWord g (Circuit.SWAP (d := d) i j hij)
  let X (t : ZMod d) := symplecticClassWord g (power (Circuit.CX i j hij) t.val)
  let Si (t : ZMod d) := symplecticClassWord g (Sexp i t)
  let Sj (t : ZMod d) := symplecticClassWord g (Sexp j t)
  let M := symplecticClassWord g (Circuit.multiplier j a)
  let N := symplecticClassWord g (Circuit.multiplier j a⁻¹)
  let U := symplecticClassWord g (A.toWord j)
  let U' := symplecticClassWord g ((A.nonzeroDifferenceStep ha c).toWord j)
  let P := H⁻¹*Si (-A.a/c)*H
  let D := J⁻¹*Sj (-A.a/c)*J
  let R := J⁻¹*Sj (A.a*c)*J
  let T := Si (-k/c)
  have hAC : U*symplecticClassWord g [.CZ i j hij]=X (-A.a)*U := by
    have hh := (symplecticClassWord_eq_iff_derives g _ _).mpr
      (symplecticDerives_AB_CZ_zero_nonzero g A ha 0 i j hij)
    simp only [bWord, ↓reduceIte, zero_sub, symplecticClassWord_append,
      symplecticClassWord_power, ZMod.val_zero, pow_zero, mul_one] at hh
    apply (mul_left_cancel_iff (a := W)).mp
    simpa only [W, U, X, symplecticClassWord_power, mul_assoc] using hh
  have hTX : Commute T (X (-A.a)) := by
    have hh := congrArg (presentedToSymplectic g)
      (((classWord_CX_commute_S_control g i j hij).symm.pow_left (-k/c).val).pow_right (-A.a).val).eq
    simpa only [T, Si, X, Sexp, symplecticClassWord_replicate, symplecticClassWord_power,
      map_mul, map_pow, presentedToSymplectic_classWord] using hh
  have hp : X c*H*X (-A.a)=P*X c*H*Si (A.a/c)*R :=
    symplecticClassWord_CX_H_CX_pivot g i j hij A.a c hc
  have hWP : W*P=D*W := by
    have hH : SemiconjBy W H J :=
      congrArg (presentedToSymplectic g) (classWord_SWAP_H_left g i j hij)
    have hS : SemiconjBy W (Si (-A.a/c)) (Sj (-A.a/c)) :=
      (symplecticClassWord_eq_iff_derives g _ _).mpr
        (derives_symplectic g (derives_SWAP_Sexp_left g i j hij (-A.a/c)))
    exact (hH.inv_right.mul_right hS).mul_right hH
  have hTR : Commute T R := by
    have hJ : Commute T J := by
      have he := congrArg (presentedToSymplectic g)
        ((classWord_disjoint g (.S i) (.H j) (by simp [Gate.support, hij, hij.symm])).pow_left (-k/c).val).eq
      simpa only [T, Si, J, Sexp, symplecticClassWord_replicate, map_mul, map_pow,
        presentedToSymplectic_classWord] using he
    have hS : Commute T (Sj (A.a*c)) := by
      have he := congrArg (presentedToSymplectic g)
        (((classWord_disjoint g (.S i) (.S j) (by simp [Gate.support, hij, hij.symm])).pow_left (-k/c).val).pow_right (A.a*c).val).eq
      simpa only [T, Si, Sj, Sexp, symplecticClassWord_replicate, map_mul, map_pow,
        presentedToSymplectic_classWord] using he
    exact (hJ.inv_right.mul_right hS).mul_right hJ
  have hMJ : M*J=J*N := symplecticClassWord_multiplier_H g j a
  have hU : U=J*N*Sj (-A.b/A.a) := by
    change symplecticClassWord g (A.toWord j)=_
    simp only [ABox.toWord, dif_neg ha, symplecticClassWord_append]
    change M*J*Sj (-A.b/A.a)=_
    rw [hMJ]
  have hU' : U'=J*N*Sj (-(A.b-c)/A.a) := by
    change symplecticClassWord g ((A.nonzeroDifferenceStep ha c).toWord j)=_
    simp only [ABox.toWord, ABox.nonzeroDifferenceStep, dif_neg ha,
      symplecticClassWord_append]
    change M*J*Sj (-(A.b-c)/A.a)=_
    rw [hMJ]
  have hNS : N*Sj (c/A.a)=Sj (A.a*c)*N := by
    have he := symplecticClassWord_multiplier_Sexp g Fact.out j a⁻¹ (c/A.a)
    have hf : (c/A.a)*A.a^2=A.a*c := by field_simp; ring
    simpa only [inv_inv, a, Units.val_mk0, hf] using he
  have hRU : R*U=U' := by
    have hR : R=J*Sj (A.a*c)*J⁻¹ :=
      (symplecticClassWord_phase_fourier_conj g j (A.a*c)).symm
    have hf : c/A.a+(-A.b/A.a)=-(A.b-c)/A.a := by ring
    calc
      _ = J*(Sj (A.a*c)*N)*Sj (-A.b/A.a) := by rw [hR, hU]; group
      _ = J*N*(Sj (c/A.a)*Sj (-A.b/A.a)) := by rw [← hNS]; group
      _ = J*N*Sj (-(A.b-c)/A.a) := by
        rw [show Sj (c/A.a)*Sj (-A.b/A.a)=Sj (c/A.a+(-A.b/A.a)) from
          (symplecticClassWord_Sexp_add g j _ _).symm, hf]
      _ = _ := hU'.symm
  have hST : Si (A.a/c)*T=Si (-(k-A.a)/c) := by
    have hf : A.a/c+(-k/c)=-(k-A.a)/c := by ring
    change Si (A.a/c)*Si (-k/c)=_
    rw [show Si (A.a/c)*Si (-k/c)=Si (A.a/c+(-k/c)) from
      (symplecticClassWord_Sexp_add g i _ _).symm, hf]
  have hB (t : ZMod d) : symplecticClassWord g (bWord c t i j hij)=W*X c*H*Si (-t/c) := by
    simp only [bWord, if_neg hc, symplecticClassWord_append]
    rfl
  apply (symplecticClassWord_eq_iff_derives g _ _).mp
  simp only [symplecticClassWord_append, symplecticClassWord_inverseWord, hB]
  change (W*X c*H*T)*U*symplecticClassWord g [.CZ i j hij]=D*(W*X c*H*Si (-(k-A.a)/c))*U'
  calc
    _ = W*X c*H*T*(X (-A.a)*U) := by rw [mul_assoc (_*T), hAC]
    _ = W*(X c*H*X (-A.a))*T*U := by
      simp only [mul_assoc]
      rw [← mul_assoc T, hTX.eq]
      group
    _ = (W*P)*X c*H*(Si (A.a/c)*T)*(R*U) := by
      rw [hp]
      simp only [mul_assoc]
      rw [← mul_assoc R, hTR.symm.eq]
      group
    _ = _ := by rw [hWP, hST, hRU]; group

end QuditClifford.NormalBoxes
