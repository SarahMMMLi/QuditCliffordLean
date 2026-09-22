import QuditClifford.SymplecticThreeWireDD
import QuditClifford.RemoteControlledRewrites

/-! # The D-D controlled-phase rewrite with both pivots nonzero -/
noncomputable section
namespace QuditClifford.NormalBoxes
open Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

set_option linter.unusedSectionVars false in
private theorem single_commute (i : Fin n) (u : Word n) (v : Word 1)
    (hu : ∀ x ∈ u, i ∉ x.support) :
    Commute (symplecticClassWord g (relabel (singleWireEmbedding i) v))
      (symplecticClassWord g u) :=
  congrArg (presentedToSymplectic g) (classWord_commute_singleWire g i u v hu).symm.eq

set_option linter.unusedSectionVars false in
private theorem swap_avoids (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ∀ x ∈ Circuit.SWAP (d := d) i j hij, k ∉ x.support := by
  intro x hx
  simp only [Circuit.SWAP, List.mem_append, scalar, List.mem_replicate, power, List.mem_flatten] at hx
  rcases hx with ⟨_, rfl⟩ | ⟨w, ⟨_, rfl⟩, hx⟩
  · simp [Gate.support]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [Gate.support, hik.symm, hjk.symm]

private theorem H_commute_word (i : Fin n) (u : Word n)
    (hu : ∀ x ∈ u, i ∉ x.support) :
    Commute (symplecticClassWord g [.H i]) (symplecticClassWord g u) :=
  single_commute g i u [.H 0] hu

private theorem S_commute_word (i : Fin n) (u : Word n) (a : ZMod d)
    (hu : ∀ x ∈ u, i ∉ x.support) :
    Commute (symplecticClassWord g (Sexp i a)) (symplecticClassWord g u) := by
  simpa only [relabel_Sexp, singleWireEmbedding, Function.Embedding.coeFn_mk] using
    single_commute g i u (Sexp 0 a) hu

/-- Two nonzero D boxes expose the adjacent and remote quadratic core. -/
theorem symplecticClassWord_DD_gather (a b c e : ZMod d) (ha : a ≠ 0) (hc : c ≠ 0)
    (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    symplecticClassWord g (dWord a b j k hjk ++ dWord c e i j hij) =
      symplecticClassWord g (Circuit.SWAP (d := d) j k hjk) *
        symplecticClassWord g (Circuit.SWAP (d := d) i j hij) *
          symplecticClassWord g (Circuit.CIZ (d := d) i j k hij hjk hik)^(-a).val *
            symplecticClassWord g [.H k] * symplecticClassWord g [.CZ i j hij] ^(-c).val *
              symplecticClassWord g [.H j] * symplecticClassWord g (Sexp k (-b/a)) *
                symplecticClassWord g (Sexp j (-e/c)) := by
  let U := symplecticClassWord g (Circuit.SWAP (d := d) i j hij)
  let T := symplecticClassWord g (Circuit.SWAP (d := d) j k hjk)
  let Q := symplecticClassWord g [.CZ j k hjk]
  let R := symplecticClassWord g [.CZ i j hij]
  let N := symplecticClassWord g (Circuit.CIZ (d := d) i j k hij hjk hik)
  let Hk := symplecticClassWord g [.H k]
  let Hj := symplecticClassWord g [.H j]
  let Sk := symplecticClassWord g (Sexp k (-b/a))
  let Sj := symplecticClassWord g (Sexp j (-e/c))
  have hu : U*U=1 := congrArg (presentedToSymplectic g) (classWord_SWAP_sq g i j hij)
  have hn : N=U*Q*U⁻¹ := congrArg (presentedToSymplectic g)
    (classWord_CIZ_other_conjugate g i j k hij hjk hik)
  have hQU : Q^(-a).val*U=U*N^(-a).val := by
    rw [hn, conj_pow, inv_eq_of_mul_eq_one_right hu]
    simp only [← mul_assoc, hu, one_mul]
  have hHU : Commute Hk U := H_commute_word g k _ (swap_avoids i j k hij hjk hik)
  have hSU : Commute Sk U := S_commute_word g k _ _ (swap_avoids i j k hij hjk hik)
  have hSR : Commute Sk (R^(-c).val) := by
    apply Commute.pow_right
    apply S_commute_word
    intro x hx
    have hx' : x = .CZ i j hij := by simpa using hx
    subst x
    simp [Gate.support, hik.symm, hjk.symm]
  have hSH : Commute Sk Hj := by
    apply S_commute_word
    intro x hx
    have hx' : x = .H j := by simpa using hx
    subst x
    simp [Gate.support, hjk.symm]
  simp only [symplecticClassWord_append, dWord, if_neg ha, if_neg hc,
    symplecticClassWord_replicate]
  change T*Q^(-a).val*Hk*Sk*(U*R^(-c).val*Hj*Sj) =
    T*U*N^(-a).val*Hk*R^(-c).val*Hj*Sk*Sj
  calc
    _ = T*Q^(-a).val*((Hk*Sk)*U)*R^(-c).val*Hj*Sj := by group
    _ = T*(Q^(-a).val*U)*Hk*Sk*R^(-c).val*Hj*Sj := by rw [(hHU.mul_left hSU).eq]; group
    _ = T*U*N^(-a).val*Hk*(Sk*(R^(-c).val*Hj))*Sj := by rw [hQU]; group
    _ = _ := by rw [(hSR.mul_right hSH).eq]; group

/-- The fourth D-D branch has precisely the source's two inverse-Fourier
corrections and the updated labels `(a,b-c)` and `(c,e-a)`. -/
theorem symplectic_DD_CZ_nonzero_nonzero (a b c e : ZMod d) (ha : a ≠ 0) (hc : c ≠ 0)
    (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    SymplecticDerives g (dWord a b j k hjk ++ dWord c e i j hij ++ [.CZ j k hjk])
      ([.H j, .H i, .CZ i j hij] ++ Sexp j (-c/a) ++ inverseWord d [.H j] ++
        Sexp i (-a/c) ++ inverseWord d [.H i] ++
          dWord a (b-c) j k hjk ++ dWord c (e-a) i j hij) := by
  let T := symplecticClassWord g (Circuit.SWAP (d := d) j k hjk)
  let U := symplecticClassWord g (Circuit.SWAP (d := d) i j hij)
  let P := T*U
  let N := symplecticClassWord g (Circuit.CIZ (d := d) i j k hij hjk hik)
  let R := symplecticClassWord g [.CZ i j hij]
  let Q := symplecticClassWord g [.CZ j k hjk]
  let Hi := symplecticClassWord g [.H i]
  let Hj := symplecticClassWord g [.H j]
  let Hk := symplecticClassWord g [.H k]
  let Si (r : ZMod d) := symplecticClassWord g (Sexp i r)
  let Sj (r : ZMod d) := symplecticClassWord g (Sexp j r)
  let Sk (r : ZMod d) := symplecticClassWord g (Sexp k r)
  let X := Hj⁻¹*R^(-c).val*Hj
  let Y := Hk⁻¹*N^(-a).val*Hk
  let K := Sk (-c/a)*Hk⁻¹*Sj (-a/c)*Hj⁻¹
  let L := Sj (-c/a)*Hj⁻¹*Si (-a/c)*Hi⁻¹
  have hHkU : Commute Hk U := H_commute_word g k _ (swap_avoids i j k hij hjk hik)
  have hHiT : Commute Hi T := H_commute_word g i _ (swap_avoids j k i hjk hik.symm hij.symm)
  have hSkU (r : ZMod d) : Commute (Sk r) U := S_commute_word g k _ r (swap_avoids i j k hij hjk hik)
  have hSiT (r : ZMod d) : Commute (Si r) T := S_commute_word g i _ r (swap_avoids j k i hjk hik.symm hij.symm)
  have hTH : T*Hk=Hj*T := congrArg (presentedToSymplectic g) (classWord_SWAP_H_right g j k hjk)
  have hUH : U*Hj=Hi*U := congrArg (presentedToSymplectic g) (classWord_SWAP_H_right g i j hij)
  have hPHk : SemiconjBy P Hk Hj := by
    change T*U*Hk=Hj*(T*U)
    rw [mul_assoc, hHkU.symm.eq, ← mul_assoc, hTH, mul_assoc]
  have hPHj : SemiconjBy P Hj Hi := by
    change T*U*Hj=Hi*(T*U)
    rw [mul_assoc, hUH, ← mul_assoc, hHiT.symm.eq, mul_assoc]
  have hPSk (r : ZMod d) : SemiconjBy P (Sk r) (Sj r) := by
    have ht : T*Sk r=Sj r*T := congrArg (presentedToSymplectic g)
      (classWord_SWAP_Sexp_right g j k hjk r)
    change T*U*Sk r=Sj r*(T*U)
    rw [mul_assoc, (hSkU r).symm.eq, ← mul_assoc, ht, mul_assoc]
  have hPSj (r : ZMod d) : SemiconjBy P (Sj r) (Si r) := by
    have hu : U*Sj r=Si r*U := congrArg (presentedToSymplectic g)
      (classWord_SWAP_Sexp_right g i j hij r)
    change T*U*Sj r=Si r*(T*U)
    rw [mul_assoc, hu, ← mul_assoc, (hSiT r).symm.eq, mul_assoc]
  have hPK : P*K=L*P :=
    (((hPSk (-c/a)).mul_right hPHk.inv_right).mul_right (hPSj (-a/c))).mul_right hPHj.inv_right
  have hPQ : P*Q=R*P := by
    simpa only [P, mul_assoc] using congrArg (presentedToSymplectic g)
      (classWord_SWAP_SWAP_CZ g i j k hij hjk hik)
  have hfront : P*Hk*Hj*Q=Hj*Hi*R*P := by
    calc
      _ = Hj*(P*Hj)*Q := by rw [hPHk.eq]; group
      _ = Hj*Hi*(P*Q) := by rw [hPHj.eq]; group
      _ = _ := by rw [hPQ]; group
  have hSkiHj (r : ZMod d) : Commute (Sk r) Hj := by
    apply S_commute_word
    intro x hx
    have hx' : x = .H j := by simpa using hx
    subst x
    simp [Gate.support, hjk.symm]
  have hSkiR (r : ZMod d) : Commute (Sk r) R := by
    apply S_commute_word
    intro x hx
    have hx' : x = .CZ i j hij := by simpa using hx
    subst x
    simp [Gate.support, hjk.symm, hik.symm]
  have hSS (r t : ZMod d) : Commute (Sk r) (Sj t) := by
    apply S_commute_word
    intro x hx
    have hx' : x = .S j := (List.mem_replicate.mp hx).2
    subst x
    simp [Gate.support, hjk.symm]
  have hSX (r : ZMod d) : Commute (Sk r) X :=
    (((hSkiHj r).inv_right).mul_right ((hSkiR r).pow_right _)).mul_right (hSkiHj r)
  have hSjHk (r : ZMod d) : Commute (Sj r) Hk := by
    apply S_commute_word
    intro x hx
    have hx' : x = .H k := by simpa using hx
    subst x
    simp [Gate.support, hjk]
  have hSjN (r : ZMod d) : Commute (Sj r) N := by
    have hn : N=T*R*T⁻¹ := congrArg (presentedToSymplectic g)
      (classWord_CIZ_conjugate g i j k hij hjk hik)
    have hs : T*Sk r*T⁻¹=Sj r := by
      have he : T*Sk r=Sj r*T := congrArg (presentedToSymplectic g)
        (classWord_SWAP_Sexp_right g j k hjk r)
      rw [he]; group
    have he := congrArg (MulAut.conj T) (hSkiR r).eq
    simp only [map_mul] at he
    change Commute _ _
    rw [hn, ← hs]
    exact he
  have hHN : Commute Hj (N^(-a).val) := by
    have he := congrArg (presentedToSymplectic g)
      ((classWord_H_middle_commute_CIZ g i j k hij hjk hik).pow_right (-a).val).eq
    simpa only [map_mul, map_pow, presentedToSymplectic_classWord] using he
  have hHH : Commute Hj Hk := congrArg (presentedToSymplectic g)
    (classWord_disjoint g (.H j) (.H k) (by simp [Gate.support, hjk, hjk.symm])).eq
  have hcore : Sk (-c/a)*Y*Sj (-a/c)*X=K*(N^(-a).val*Hk*R^(-c).val*Hj) := by
    have he : Commute (N^(-a).val*Hk) (Sj (-a/c)*Hj⁻¹) :=
      ((((hSjN _).pow_right _).mul_right (hSjHk _)).symm).mul_right
        ((hHN.mul_right hHH).symm.inv_right)
    change Sk (-c/a)*(Hk⁻¹*N^(-a).val*Hk)*Sj (-a/c)*(Hj⁻¹*R^(-c).val*Hj)=
      (Sk (-c/a)*Hk⁻¹*Sj (-a/c)*Hj⁻¹)*(N^(-a).val*Hk*R^(-c).val*Hj)
    calc
      _ = Sk (-c/a)*Hk⁻¹*((N^(-a).val*Hk)*(Sj (-a/c)*Hj⁻¹))*R^(-c).val*Hj := by group
      _ = _ := by rw [he.eq]; group
  have htail : Sk (c/a)*Sj (-a/c)*X*Sj (a/c)*Sk (-b/a)*Sj (-e/c) =
      Sj (-a/c)*X*Sk (-(b-c)/a)*Sj (-(e-a)/c) := by
    have hk : Sk (c/a)*Sk (-b/a)=Sk (-(b-c)/a) := by
      dsimp only [Sk]
      rw [← symplecticClassWord_Sexp_add]
      congr 2
      ring
    have hj : Sj (a/c)*Sj (-e/c)=Sj (-(e-a)/c) := by
      dsimp only [Sj]
      rw [← symplecticClassWord_Sexp_add]
      congr 2
      ring
    calc
      _ = (Sk (c/a)*(Sj (-a/c)*X))*(Sj (a/c)*Sk (-b/a))*Sj (-e/c) := by group
      _ = ((Sj (-a/c)*X)*Sk (c/a))*(Sk (-b/a)*Sj (a/c))*Sj (-e/c) := by
        rw [((hSS _ _).mul_right (hSX _)).eq, (hSS _ _).symm.eq]
      _ = (Sj (-a/c)*X)*(Sk (c/a)*Sk (-b/a))*(Sj (a/c)*Sj (-e/c)) := by group
      _ = _ := by rw [hk, hj]
  have hSQ : Commute (Sk (-b/a)*Sj (-e/c)) Q := by
    have hk := congrArg (presentedToSymplectic g)
      ((classWord_CZ_commute_S_right g j k hjk).symm.pow_left (-b/a).val).eq
    have hj := congrArg (presentedToSymplectic g)
      ((classWord_CZ_commute_S_first g j k hjk).symm.pow_left (-e/c).val).eq
    have hk' : Commute (Sk (-b/a)) Q := by
      simpa only [map_mul, map_pow, presentedToSymplectic_classWord, Sk, Q, Sexp,
        symplecticClassWord_replicate] using hk
    have hj' : Commute (Sj (-e/c)) Q := by
      simpa only [map_mul, map_pow, presentedToSymplectic_classWord, Sj, Q, Sexp,
        symplecticClassWord_replicate] using hj
    exact hk'.mul_left hj'
  have hp : N^(-a).val*Hk*R^(-c).val*Hj*Q=
      Hk*Hj*Q*Sk (-c/a)*Y*Sk (c/a)*Sj (-a/c)*X*Sj (a/c) :=
    symplecticClassWord_remote_quadratic_pivot g i j k hij hjk hik a c ha hc
  have he : P*N^(-a).val*Hk*R^(-c).val*Hj*Sk (-b/a)*Sj (-e/c)*Q =
      Hj*Hi*R*L*(P*N^(-a).val*Hk*R^(-c).val*Hj*Sk (-(b-c)/a)*Sj (-(e-a)/c)) := by
    calc
      _ = P*(N^(-a).val*Hk*R^(-c).val*Hj)*(Sk (-b/a)*Sj (-e/c)*Q) := by group
      _ = P*(N^(-a).val*Hk*R^(-c).val*Hj*Q)*Sk (-b/a)*Sj (-e/c) := by rw [hSQ.eq]; group
      _ = (P*Hk*Hj*Q)*Sk (-c/a)*Y*(Sk (c/a)*Sj (-a/c)*X*Sj (a/c)*Sk (-b/a)*Sj (-e/c)) := by rw [hp]; group
      _ = (Hj*Hi*R*P)*Sk (-c/a)*Y*(Sj (-a/c)*X*Sk (-(b-c)/a)*Sj (-(e-a)/c)) := by rw [hfront, htail]
      _ = Hj*Hi*R*P*(Sk (-c/a)*Y*Sj (-a/c)*X)*Sk (-(b-c)/a)*Sj (-(e-a)/c) := by group
      _ = Hj*Hi*R*(P*K)*(N^(-a).val*Hk*R^(-c).val*Hj)*Sk (-(b-c)/a)*Sj (-(e-a)/c) := by rw [hcore]; group
      _ = _ := by rw [hPK]; group
  apply (symplecticClassWord_eq_iff_derives g _ _).mp
  have htriple : symplecticClassWord g [.H j, .H i, .CZ i j hij] = Hj*Hi*R := rfl
  have hin := symplecticClassWord_DD_gather g a b c e ha hc i j k hij hjk hik
  have hout := symplecticClassWord_DD_gather g a (b-c) c (e-a) ha hc i j k hij hjk hik
  simp only [symplecticClassWord_append] at hin hout ⊢
  have he' :
      (symplecticClassWord g (dWord a b j k hjk)*symplecticClassWord g (dWord c e i j hij))*Q =
        Hj*Hi*R*L*(symplecticClassWord g (dWord a (b-c) j k hjk)*
          symplecticClassWord g (dWord c (e-a) i j hij)) := by
    rw [hin, hout]
    exact he
  simpa only [symplecticClassWord_inverseWord, htriple, Hi, Hj, R, Q, L, Sj, Si,
    mul_assoc] using he'

end QuditClifford.NormalBoxes
