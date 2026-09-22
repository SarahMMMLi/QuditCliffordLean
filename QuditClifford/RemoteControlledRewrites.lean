import QuditClifford.SymplecticTwoWireDCZ
import QuditClifford.SymplecticThreeWireB
import QuditClifford.QuadraticBoxAlgebra

/-!
# Remote quadratic controlled-addition rewrites

The remote controlled addition is the literal SWAP conjugate of an adjacent
one. Its identities below are transported Figure 1 derivations.
-/
noncomputable section
namespace QuditClifford.Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

/-- A controlled-addition power conjugates an arbitrary CZ exponent. -/
theorem symplecticClassWord_CXpower_conjugate_CZexp (i j : Fin n) (hij : i ≠ j)
    (a b : ZMod d) :
    symplecticClassWord g (power (CX i j hij) a.val) *
        symplecticClassWord g (List.replicate b.val (.CZ i j hij)) *
          (symplecticClassWord g (power (CX i j hij) a.val))⁻¹ =
      symplecticClassWord g (Sexp i (-2*a*b)) *
        symplecticClassWord g (List.replicate b.val (.CZ i j hij)) := by
  let A := symplecticClassWord g (power (CX i j hij) a.val)
  let C := symplecticClassWord g [.CZ i j hij]
  let S := symplecticClassWord g (Sexp i (-2*a))
  have h : A*C*A⁻¹=S*C := symplecticClassWord_CXpower_conjugate_CZ g i j hij a
  have hs : Commute S C := by
    have he := congrArg (presentedToSymplectic g)
      ((classWord_CZ_commute_S_first g i j hij).symm.pow_left (-2*a).val).eq
    simpa only [map_mul, map_pow, presentedToSymplectic_classWord, S, C, Sexp,
      symplecticClassWord_replicate] using he
  have hp := congrArg (fun x => x^b.val) h
  dsimp only at hp
  rw [conj_pow, hs.mul_pow] at hp
  have hS : S^b.val = symplecticClassWord g (Sexp i (-2*a*b)) := by
    rw [← symplecticClassWord_Sexp_nsmul]
    congr 2
    simp only [ZMod.natCast_zmod_val]
    ring
  rw [hS] at hp
  simpa only [symplecticClassWord_replicate] using hp

/-- C15 in residue-exponent form, with its remote correction retained. -/
theorem symplecticClassWord_CXpower_CZ_overlap (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a : ZMod d) :
    symplecticClassWord g (power (CX i j hij) a.val) * symplecticClassWord g [.CZ j k hjk] =
      symplecticClassWord g [.CZ j k hjk] *
        symplecticClassWord g (power (CIZ (d := d) i j k hij hjk hik) (-a).val) *
          symplecticClassWord g (power (CX i j hij) a.val) := by
  let T := symplecticClassWord g (SWAP (d := d) j k hjk)
  let R := symplecticClassWord g [.CZ i j hij]
  let N := symplecticClassWord g (CIZ (d := d) i j k hij hjk hik)
  have hn : N=T*R*T⁻¹ := congrArg (presentedToSymplectic g)
    (classWord_CIZ_conjugate g i j k hij hjk hik)
  have hneg : (N⁻¹)^a.val=N^(-a).val := by
    rw [inv_pow, hn, conj_pow, conj_pow]
    have hr := symplecticClassWord_CZexp_neg g i j hij a
    simp only [symplecticClassWord_replicate] at hr
    change R^(-a).val=(R^a.val)⁻¹ at hr
    rw [hr]
    simp only [mul_inv_rev, inv_inv, mul_assoc]
  have h := congrArg (presentedToSymplectic g)
    (classWord_CXpow_CZ_overlap g i j k hij hjk hik a.val)
  simpa only [map_mul, map_pow, map_inv, presentedToSymplectic_classWord,
    symplecticClassWord_power, hneg, N] using h

/-- A SWAP conjugation leaves a phase on the third wire fixed. -/
theorem symplecticClassWord_SWAP_conj_Sexp_offwire (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a : ZMod d) :
    MulAut.conj (symplecticClassWord g (SWAP (d := d) j k hjk))
      (symplecticClassWord g (Sexp i a)) = symplecticClassWord g (Sexp i a) := by
  have hHj := classWord_disjoint g (.S i) (.H j) (by simp [Gate.support, hij, hij.symm])
  have hHk := classWord_disjoint g (.S i) (.H k) (by simp [Gate.support, hik, hik.symm])
  have hC := classWord_disjoint g (.S i) (.CZ j k hjk)
    (by simp [Gate.support, hij, hik, hij.symm, hik.symm])
  have hscalar : Commute (classWord g [.S i])
      (classWord g (scalar (n := n) (d*((d-1)/2)))) :=
    ((classWord_eq_iff_derives g _ _).mpr
      (derives_scalar_commute g (d*((d-1)/2)) [.S i])).symm
  have hswap : Commute (classWord g [.S i]) (classWord g (SWAP (d := d) j k hjk)) := by
    simp only [SWAP, classWord_append, classWord_power]
    exact hscalar.mul_right (((hC.mul_right hHj).mul_right hHk).pow_right 3)
  have he := congrArg (presentedToSymplectic g) (hswap.pow_left a.val).symm.eq
  simp only [map_mul, map_pow, presentedToSymplectic_classWord] at he
  simp only [MulAut.conj_apply, Sexp, symplecticClassWord_replicate]
  rw [he]
  group

/-- The two nonzero shears satisfy the quadratic identity used by the D-D rule.
The remote factors are explicit SWAP-conjugated adjacent factors. -/
theorem symplecticClassWord_remote_quadratic_pivot (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a c : ZMod d) (ha : a ≠ 0) (hc : c ≠ 0) :
    let N := symplecticClassWord g (CIZ (d := d) i j k hij hjk hik)
    let Hj := symplecticClassWord g [.H j]
    let Hk := symplecticClassWord g [.H k]
    let R := symplecticClassWord g [.CZ i j hij]
    let Q := symplecticClassWord g [.CZ j k hjk]
    let X := Hj⁻¹*R^(-c).val*Hj
    let Y := Hk⁻¹*N^(-a).val*Hk
    N^(-a).val*Hk*R^(-c).val*Hj*Q =
      Hk*Hj*Q*symplecticClassWord g (Sexp k (-c/a))*Y*
        symplecticClassWord g (Sexp k (c/a))*symplecticClassWord g (Sexp j (-a/c))*X*
          symplecticClassWord g (Sexp j (a/c)) := by
  dsimp only
  let T := symplecticClassWord g (SWAP (d := d) j k hjk)
  let φ := MulAut.conj T
  let N := symplecticClassWord g (CIZ (d := d) i j k hij hjk hik)
  let Hj := symplecticClassWord g [.H j]
  let Hk := symplecticClassWord g [.H k]
  let R := symplecticClassWord g [.CZ i j hij]
  let Q := symplecticClassWord g [.CZ j k hjk]
  let X := Hj⁻¹*R^(-c).val*Hj
  let Y := Hk⁻¹*N^(-a).val*Hk
  let Si (r : ZMod d) := symplecticClassWord g (Sexp i r)
  let Sj (r : ZMod d) := symplecticClassWord g (Sexp j r)
  let Sk (r : ZMod d) := symplecticClassWord g (Sexp k r)
  let A (r : ZMod d) := symplecticClassWord g (power (CX i j hij) (-r).val)
  have hTT : T*T=1 := congrArg (presentedToSymplectic g) (classWord_SWAP_sq g j k hjk)
  have hφφ (x : PresentedSymplectic g n) : φ (φ x)=x := by
    change T*(T*x*T⁻¹)*T⁻¹=x
    rw [inv_eq_of_mul_eq_one_right hTT]
    calc
      _ = (T*T)*x*(T*T) := by group
      _ = x := by rw [hTT]; simp
  have hφR : φ R=N := (congrArg (presentedToSymplectic g)
    (classWord_CIZ_conjugate g i j k hij hjk hik)).symm
  have hφN : φ N=R := by rw [← hφR, hφφ]
  have hφQ : φ Q=Q := by
    have ht : Commute T Q := congrArg (presentedToSymplectic g)
      (classWord_SWAP_commute_CZ g j k hjk).eq
    change T*Q*T⁻¹=Q
    rw [ht.eq]; group
  have hφHj : φ Hj=Hk := by
    have ht : T*Hj=Hk*T := congrArg (presentedToSymplectic g)
      (classWord_SWAP_H_left g j k hjk)
    change T*Hj*T⁻¹=Hk
    rw [ht]; group
  have hφSi (r : ZMod d) : φ (Si r)=Si r :=
    symplecticClassWord_SWAP_conj_Sexp_offwire g i j k hij hjk hik r
  have hφSj (r : ZMod d) : φ (Sj r)=Sk r := by
    have ht : T*Sj r=Sk r*T := congrArg (presentedToSymplectic g)
      ((classWord_eq_iff_derives g _ _).mpr (derives_SWAP_Sexp_left g j k hjk r))
    change T*Sj r*T⁻¹=Sk r
    rw [ht]; group
  have hA (r : ZMod d) : A r=Hj⁻¹*R^(-r).val*Hj :=
    symplecticClassWord_CXpower_expand g i j hij (-r).val
  have hAX : A c=X := hA c
  have hφA : φ (A a)=Y := by rw [hA, map_mul, map_mul, map_inv, map_pow, hφHj, hφR]
  have hAQ (r : ZMod d) : A r*Q=Q*N^r.val*A r := by
    have he := symplecticClassWord_CXpower_CZ_overlap g i j k hij hjk hik (-r)
    simpa only [neg_neg, symplecticClassWord_power, A, Q, N] using he
  have hXQ : X*Q=Q*N^c.val*X := by rw [← hAX]; exact hAQ c
  have hYQ : Y*Q=Q*R^a.val*Y := by
    have he := congrArg φ (hAQ a)
    simpa only [map_mul, map_pow, hφQ, hφA, hφN] using he
  have hYV : Y*N^c.val=(Si (a*c))^2*N^c.val*Y := by
    have he := symplecticClassWord_CXpower_conjugate_CZexp g i j hij (-a) c
    have hfield : -2 * -a * c=a*c+a*c := by ring
    rw [hfield, symplecticClassWord_Sexp_add] at he
    have he' : A a*R^c.val*(A a)⁻¹=Si (a*c)*Si (a*c)*R^c.val := by
      simpa only [symplecticClassWord_replicate] using he
    have he'' := congrArg φ he'
    simp only [map_mul, map_inv, map_pow, hφR, hφA, hφSi] at he''
    calc
      _ = (Y*N^c.val*Y⁻¹)*Y := by group
      _ = _ := by rw [he'']; simp only [pow_two, mul_assoc]
  have hphase (r t : ZMod d) (hr : r ≠ 0) :
      Sj (-t/r)*A r*(Sj (-t/r))⁻¹=Si (r*t)*R^t.val*A r := by
    have he := symplecticClassWord_CXpower_conjugate_Sexp g i j hij (-r) (t/r)
    have h1 : t/r*(-r * -r)=r*t := by field_simp; ring
    have h2 : t/r*(- -r)=t := by field_simp
    rw [h1, h2] at he
    have he' : A r*Sj (t/r)*(A r)⁻¹=Sj (t/r)*Si (r*t)*R^t.val := by
      simpa only [symplecticClassWord_replicate] using he
    have hs : Sj (-t/r)=(Sj (t/r))⁻¹ := by
      dsimp only [Sj]
      rw [neg_div, symplecticClassWord_Sexp_neg]
    rw [hs, inv_inv]
    calc
      _ = (Sj (t/r))⁻¹*(A r*Sj (t/r)*(A r)⁻¹)*A r := by group
      _ = _ := by rw [he']; group
  have hs : Sj (-a/c)*X*(Sj (-a/c))⁻¹=Si (a*c)*R^a.val*X := by
    simpa only [hAX, mul_comm c a] using hphase c a hc
  have ht : Sk (-c/a)*Y*(Sk (-c/a))⁻¹=Si (a*c)*N^c.val*Y := by
    have he := congrArg φ (hphase a c ha)
    simpa only [map_mul, map_inv, map_pow, hφA, hφSj, hφSi, hφR] using he
  have hAS (r t : ZMod d) : Commute (A r) (Si t) := by
    have he := congrArg (presentedToSymplectic g)
      (((classWord_CX_commute_S_control g i j hij).pow_left (-r).val).pow_right t.val).eq
    simpa only [map_mul, map_pow, presentedToSymplectic_classWord,
      A, Si, Sexp, symplecticClassWord_power, symplecticClassWord_replicate] using he
  have hYF : Commute Y (Si (a*c)) := by
    have he := congrArg φ (hAS a (a*c)).eq
    simpa only [map_mul, hφA, hφSi] using he
  have hYU : Commute Y (R^a.val) := by
    have he := congrArg (presentedToSymplectic g)
      (((classWord_CX_commute_CIZ g i j k hij hjk hik).pow_left (-a).val).pow_right a.val).eq
    have he' : Commute (A a) (N^a.val) := by
      simpa only [map_mul, map_pow, presentedToSymplectic_classWord,
        A, N, symplecticClassWord_power] using he
    have he'' := congrArg φ he'.eq
    simpa only [map_mul, map_pow, hφA, hφN] using he''
  have hRS (r t : ZMod d) : Commute (R^r.val) (Si t) := by
    have he := congrArg (presentedToSymplectic g)
      (((classWord_CZ_commute_S_first g i j hij).pow_left r.val).pow_right t.val).eq
    simpa only [map_mul, map_pow, presentedToSymplectic_classWord,
      R, Si, Sexp, symplecticClassWord_replicate] using he
  have hUV : Commute (R^a.val) (N^c.val) := by
    have he := congrArg (presentedToSymplectic g)
      (((classWord_CZ_first_commute_CIZ g i j k hij hjk hik).pow_left a.val).pow_right c.val).eq
    simpa only [map_mul, map_pow, presentedToSymplectic_classWord] using he
  have hVF : Commute (N^c.val) (Si (a*c)) := by
    have he := congrArg φ (hRS c (a*c)).eq
    simpa only [map_mul, map_pow, hφR, hφSi] using he
  have hp := quadratic_box_pivot X Y Q (R^a.val) (N^c.val) (Si (a*c))
    (Sk (-c/a)) (Sj (-a/c)) hXQ hYQ hYV ht hs hYF hYU (hRS a (a*c)) hUV hVF
  have hHN : Commute Hj (N^(-a).val) := by
    have he := congrArg (presentedToSymplectic g)
      ((classWord_H_middle_commute_CIZ g i j k hij hjk hik).pow_right (-a).val).eq
    simpa only [map_mul, map_pow, presentedToSymplectic_classWord] using he
  have hHH : Commute Hj Hk := congrArg (presentedToSymplectic g)
    (classWord_disjoint g (.H j) (.H k) (by simp [Gate.support, hjk, hjk.symm])).eq
  have hHY : Commute Hj Y := (hHH.inv_right.mul_right hHN).mul_right hHH
  have hSk : (Sk (-c/a))⁻¹=Sk (c/a) := by
    dsimp only [Sk]
    rw [neg_div, symplecticClassWord_Sexp_neg, inv_inv]
  have hSj : (Sj (-a/c))⁻¹=Sj (a/c) := by
    dsimp only [Sj]
    rw [neg_div, symplecticClassWord_Sexp_neg, inv_inv]
  change N^(-a).val*Hk*R^(-c).val*Hj*Q =
    Hk*Hj*Q*Sk (-c/a)*Y*Sk (c/a)*Sj (-a/c)*X*Sj (a/c)
  calc
    _ = Hk*Y*Hj*X*Q := by dsimp [Y, X]; group
    _ = Hk*Hj*(Y*X*Q) := by rw [mul_assoc Hk Y Hj, hHY.symm.eq]; group
    _ = _ := by rw [hp, hSk, hSj]; group

end QuditClifford.Circuit
