import QuditClifford.SymplecticTwoWireDCZ
import QuditClifford.SymplecticThreeWireB
import QuditClifford.DDPermutation

/-!
# Three-wire D-D controlled-phase rewrites

The source's lower D box acts on `(j,k)` and its shifted upper D box on
`(i,j)`. Every theorem below is a derivation for the expanded primitive words.
-/
noncomputable section
namespace QuditClifford.NormalBoxes
open Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

/-- The zero/zero D-D branch of the three-wire CZ family holds exactly. -/
theorem derives_DD_CZ_zero_zero (b e : ZMod d) (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    Derives g (dWord 0 b j k hjk ++ dWord 0 e i j hij ++ [.CZ j k hjk])
      ([.CZ i j hij] ++ dWord 0 b j k hjk ++ dWord 0 e i j hij) := by
  apply (classWord_eq_iff_derives g _ _).mp
  let T := classWord g (Circuit.SWAP (d := d) j k hjk)
  let U := classWord g (Circuit.SWAP (d := d) i j hij)
  let Q := classWord g [.CZ j k hjk]
  let R := classWord g [.CZ i j hij]
  have hT : Commute T (Q^(-b).val) := (classWord_SWAP_commute_CZ g j k hjk).pow_right _
  have hQR : Commute Q R := classWord_CZ_commute_overlap g i j k hij hjk hik
  have hR : Commute (R^(-e).val) Q := hQR.symm.pow_left _
  have hb : Commute (Q^(-b).val) R := hQR.pow_left _
  have hTU : T*U*Q = R*T*U := classWord_SWAP_SWAP_CZ g i j k hij hjk hik
  have he : T*Q^(-b).val*(U*R^(-e).val)*Q = R*(T*Q^(-b).val)*(U*R^(-e).val) := by
    calc
      _ = (T*Q^(-b).val)*U*(R^(-e).val*Q) := by group
      _ = (Q^(-b).val*T)*U*(Q*R^(-e).val) := by rw [hT.eq, hR.eq]
      _ = Q^(-b).val*(T*U*Q)*R^(-e).val := by group
      _ = Q^(-b).val*(R*T*U)*R^(-e).val := by rw [hTU]
      _ = (Q^(-b).val*R)*T*U*R^(-e).val := by group
      _ = (R*Q^(-b).val)*T*U*R^(-e).val := by rw [hb.eq]
      _ = R*(Q^(-b).val*T)*(U*R^(-e).val) := by group
      _ = _ := by rw [← hT.eq]
  simpa only [dWord, if_pos rfl, ↓reduceIte, classWord_append, classWord_replicate,
    T, U, Q, R, mul_assoc] using he

end QuditClifford.NormalBoxes

namespace QuditClifford.NormalBoxes
open Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

/-- The zero/nonzero D-D branch is already an exact Figure 1 rewrite. -/
theorem derives_DD_CZ_zero_nonzero (b c e : ZMod d) (hc : c ≠ 0)
    (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    Derives g (dWord 0 b j k hjk ++ dWord c e i j hij ++ [.CZ j k hjk])
      ([.H i, .CZ i j hij] ++ inverseWord d [.H i] ++
        dWord 0 (b-c) j k hjk ++ dWord c e i j hij) := by
  let T := classWord g (Circuit.SWAP (d := d) j k hjk)
  let U := classWord g (Circuit.SWAP (d := d) i j hij)
  let Q := classWord g [.CZ j k hjk]
  let R := classWord g [.CZ i j hij]
  let N := classWord g (Circuit.CIZ (d := d) i j k hij hjk hik)
  let H := classWord g [.H j]
  let Hi := classWord g [.H i]
  let A := classWord g (Circuit.CX i j hij)^(-c).val
  let S := classWord g (Sexp j (-e/c))
  have hS : Commute S Q := by
    simpa only [S, Sexp, classWord_replicate] using
      (classWord_CZ_commute_S_first g j k hjk).symm.pow_left (-e/c).val
  have hQ : Commute T (Q^(-b).val) := (classWord_SWAP_commute_CZ g j k hjk).pow_right _
  have hR : Commute (Q^(-b).val) R := (classWord_CZ_commute_overlap g i j k hij hjk hik).pow_left _
  have hTU : T*U*Q = R*T*U := classWord_SWAP_SWAP_CZ g i j k hij hjk hik
  have hbase : T*Q^(-b).val*U*Q = R*T*Q^(-b).val*U := by
    calc
      _ = Q^(-b).val*(T*U*Q) := by rw [hQ.eq]; group
      _ = Q^(-b).val*(R*T*U) := by rw [hTU]
      _ = R*(Q^(-b).val*T)*U := by rw [← mul_assoc, ← mul_assoc, hR.eq]; group
      _ = _ := by rw [← hQ.eq]; group
  have hU : U*H = Hi*U := classWord_SWAP_H_right g i j hij
  have hHiT : Commute Hi T := by
    have hJ := classWord_disjoint g (.H i) (.H j) (by simp [Gate.support, hij, hij.symm])
    have hK := classWord_disjoint g (.H i) (.H k) (by simp [Gate.support, hik, hik.symm])
    have hC := classWord_disjoint g (.H i) (.CZ j k hjk) (by simp [Gate.support, hij, hik, hij.symm, hik.symm])
    have hsc : Commute Hi (classWord g (scalar (n := n) (d*((d-1)/2)))) :=
      ((classWord_eq_iff_derives g _ _).mpr
        (derives_scalar_commute g (d*((d-1)/2)) [.H i])).symm
    change Commute Hi (classWord g (Circuit.SWAP (d := d) j k hjk))
    simp only [Circuit.SWAP, classWord_append, classWord_power]
    exact hsc.mul_right (((hC.mul_right hJ).mul_right hK).pow_right 3)
  have hHiQ : Commute Hi (Q^(-b).val) :=
    (classWord_disjoint g (.H i) (.CZ j k hjk) (by simp [Gate.support, hij, hik, hij.symm, hik.symm])).pow_right _
  have hNH : N = U*Q*U⁻¹ := classWord_CIZ_other_conjugate g i j k hij hjk hik
  have hN : U*N^c.val = Q^c.val*U := by
    have hu : U⁻¹=U := classWord_SWAP_inv Fact.out g Fact.out i j hij
    rw [hNH, conj_pow]
    rw [hu]
    have huu : U*U=1 := classWord_SWAP_sq g i j hij
    simp only [← mul_assoc, huu, one_mul]
  have hNneg : (N⁻¹)^(-c).val = N^c.val := by
    rw [inv_pow, hNH, conj_pow, conj_pow]
    have hn := classWord_CZexp_neg g j k hjk c
    change Q^(-c).val = (Q^c.val)⁻¹ at hn
    rw [hn]
    simp only [mul_inv_rev, inv_inv, mul_assoc]
  have hAQ : A*Q=Q*N^c.val*A := by
    have ht := classWord_CXpow_CZ_overlap g i j k hij hjk hik (-c).val
    rw [show (classWord g (Circuit.CIZ (d := d) i j k hij hjk hik))⁻¹^(-c).val = N^c.val from hNneg] at ht
    exact ht
  have hA : A=H⁻¹*R^(-c).val*H := by
    dsimp [A]
    rw [classWord_CX_conjugate]
    simpa only [H, R, inv_inv] using
      (conj_pow (a := H⁻¹) (b := R) (i := (-c).val))
  have hpow : Q^(-b).val*Q^c.val=Q^(-(b-c)).val := by
    have ht := (classWord_eq_iff_derives g _ _).mpr (derives_CZexp_add g j k hjk (-b) c)
    have he : -b+c=-(b-c) := by ring
    simpa only [classWord_append, classWord_replicate, he] using ht
  have hHiQ' : Commute Hi (Q^(-(b-c)).val) :=
    (classWord_disjoint g (.H i) (.CZ j k hjk) (by simp [Gate.support, hij, hik, hij.symm, hik.symm])).pow_right _
  have hUi : U*H⁻¹=Hi⁻¹*U := (show SemiconjBy U H Hi from hU).inv_right
  have he : T*Q^(-b).val*(U*R^(-c).val*H*S)*Q =
      Hi*R*Hi⁻¹*(T*Q^(-(b-c)).val)*(U*R^(-c).val*H*S) := by
    calc
      _ = T*Q^(-b).val*U*(R^(-c).val*H)*(S*Q) := by group
      _ = T*Q^(-b).val*U*(H*A)*(Q*S) := by rw [hS.eq, hA]; group
      _ = (T*Q^(-b).val)*(U*H)*(A*Q)*S := by group
      _ = (T*Q^(-b).val)*(Hi*U)*(Q*N^c.val*A)*S := by rw [hU, hAQ]
      _ = Hi*(T*Q^(-b).val*U*Q)*N^c.val*A*S := by
        rw [← mul_assoc (T*Q^(-b).val) Hi U, ((hHiT.mul_right hHiQ).symm).eq]; group
      _ = Hi*(R*T*Q^(-b).val*U)*N^c.val*A*S := by rw [hbase]
      _ = Hi*R*T*Q^(-b).val*(U*N^c.val)*A*S := by group
      _ = Hi*R*T*(Q^(-b).val*Q^c.val)*U*A*S := by rw [hN]; group
      _ = Hi*R*T*Q^(-(b-c)).val*U*(H⁻¹*R^(-c).val*H)*S := by rw [hpow, hA]
      _ = Hi*R*(T*Q^(-(b-c)).val)*(U*H⁻¹)*R^(-c).val*H*S := by group
      _ = Hi*R*(T*Q^(-(b-c)).val)*(Hi⁻¹*U)*R^(-c).val*H*S := by rw [hUi]
      _ = _ := by
        rw [← mul_assoc (Hi*R*(T*Q^(-(b-c)).val)) Hi⁻¹ U,
          mul_assoc (Hi*R) (T*Q^(-(b-c)).val) Hi⁻¹,
          ((hHiT.mul_right hHiQ').symm.inv_right).eq]
        group
  apply (classWord_eq_iff_derives g _ _).mp
  have hpair : classWord g [.H i, .CZ i j hij] = classWord g [.H i]*classWord g [.CZ i j hij] := rfl
  simpa only [dWord, if_pos rfl, ↓reduceIte, if_neg hc, classWord_append, hpair,
    classWord_replicate, classWord_inverseWord, classWord_nil, mul_one,
    T, U, Q, R, H, Hi, S, mul_assoc] using he

/-- Exchanging the two D labels gives the nonzero/zero branch exactly. -/
theorem derives_DD_CZ_nonzero_zero (a b e : ZMod d) (ha : a ≠ 0)
    (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    Derives g (dWord a b j k hjk ++ dWord 0 e i j hij ++ [.CZ j k hjk])
      ([.H j, .CZ i j hij] ++ inverseWord d [.H j] ++
        dWord a b j k hjk ++ dWord 0 (e-a) i j hij) := by
  let U := classWord g (Circuit.SWAP (d := d) i j hij)
  let T := classWord g (Circuit.SWAP (d := d) j k hjk)
  let Q := classWord g [.CZ j k hjk]
  let R := classWord g [.CZ i j hij]
  let Hi := classWord g [.H i]
  let Hj := classWord g [.H j]
  let X := classWord g (dWord a b j k hjk ++ dWord 0 e i j hij)
  let Y := classWord g (dWord 0 e j k hjk ++ dWord a b i j hij)
  let X' := classWord g (dWord a b j k hjk ++ dWord 0 (e-a) i j hij)
  let Y' := classWord g (dWord 0 (e-a) j k hjk ++ dWord a b i j hij)
  have hu : U*U=1 := classWord_SWAP_sq g i j hij
  have ht : T*T=1 := classWord_SWAP_sq g j k hjk
  have hp : U*X*T=Y := classWord_DD_permute g a b 0 e i j k hij hjk hik
  have hp' : U*X'*T=Y' := classWord_DD_permute g a b 0 (e-a) i j k hij hjk hik
  have hX : X=U*Y*T := by
    rw [← hp]
    simp only [← mul_assoc, hu, one_mul]
    simp only [mul_assoc, ht, mul_one]
  have hY' : U*Y'*T=X' := by
    rw [← hp']
    simp only [← mul_assoc, hu, one_mul]
    simp only [mul_assoc, ht, mul_one]
  have hTQ : Commute T Q := classWord_SWAP_commute_CZ g j k hjk
  have hUR : Commute U R := classWord_SWAP_commute_CZ g i j hij
  have hUH : U*Hi=Hj*U := classWord_SWAP_H_left g i j hij
  have hUHi : U*Hi⁻¹=Hj⁻¹*U := (show SemiconjBy U Hi Hj from hUH).inv_right
  have hdirty : U*(Hi*R*Hi⁻¹)=(Hj*R*Hj⁻¹)*U := by
    calc
      _ = (U*Hi)*R*Hi⁻¹ := by group
      _ = Hj*(U*R)*Hi⁻¹ := by rw [hUH]; group
      _ = Hj*R*(U*Hi⁻¹) := by rw [hUR.eq]; group
      _ = _ := by rw [hUHi]; group
  have hY : Y*Q=(Hi*R*Hi⁻¹)*Y' := by
    have h := (classWord_eq_iff_derives g _ _).mpr
      (derives_DD_CZ_zero_nonzero g e a b ha i j k hij hjk hik)
    simpa only [Y, Y', Q, Hi, R, classWord_append, classWord_inverseWord, mul_assoc] using h
  have he : X*Q=(Hj*R*Hj⁻¹)*X' := by
    calc
      _ = U*Y*(T*Q) := by rw [hX]; group
      _ = U*(Y*Q)*T := by rw [hTQ.eq]; group
      _ = U*((Hi*R*Hi⁻¹)*Y')*T := by rw [hY]
      _ = (U*(Hi*R*Hi⁻¹))*Y'*T := by group
      _ = (Hj*R*Hj⁻¹)*(U*Y'*T) := by rw [hdirty]; group
      _ = _ := by rw [hY']
  apply (classWord_eq_iff_derives g _ _).mp
  simpa only [X, X', Q, Hj, R, classWord_append, classWord_inverseWord, mul_assoc] using he

end QuditClifford.NormalBoxes
