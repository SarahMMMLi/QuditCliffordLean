import QuditClifford.SymplecticTwoWireA
import QuditClifford.SymplecticTwoWireB
import QuditClifford.SymplecticTwoWireBruhat

/-!
# Controlled-phase pushing through consecutive A and B boxes

These statements use the Figure 6 words in matrix order, B followed by A.
The proofs use syntactic controlled-addition and controlled-phase relations.
-/

noncomputable section
namespace QuditClifford.Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

/-- Two independent residue powers in the CX/CZ transport identity. -/
theorem symplecticClassWord_CXpower_CZexp (i j : Fin n) (hij : i ≠ j) (k l : ZMod d) :
    symplecticClassWord g (power (Circuit.CX i j hij) k.val) *
      symplecticClassWord g (List.replicate l.val (.CZ i j hij)) =
    symplecticClassWord g (Sexp i (-2*k*l)) *
      symplecticClassWord g (List.replicate l.val (.CZ i j hij)) *
      symplecticClassWord g (power (Circuit.CX i j hij) k.val) := by
  have hsc : Commute (symplecticClassWord g (Sexp i (-2*k)))
      (symplecticClassWord g [.CZ i j hij]) := by
    have h := congrArg (presentedToSymplectic g)
      ((classWord_CZ_commute_S_first g i j hij).symm.pow_left (-2*k).val).eq
    simpa only [map_mul, map_pow, presentedToSymplectic_classWord,
      Sexp, symplecticClassWord_replicate] using h
  have he := congrArg (fun q : PresentedSymplectic g n => q^l.val)
    (symplecticClassWord_CXpower_conjugate_CZ g i j hij k)
  dsimp only at he
  rw [conj_pow, hsc.mul_pow, ← symplecticClassWord_Sexp_nsmul,
    ZMod.natCast_zmod_val] at he
  have hf : l*(-2*k) = -2*k*l := by ring
  rw [hf] at he
  apply (mul_right_cancel_iff
    (a := (symplecticClassWord g (power (Circuit.CX i j hij) k.val))⁻¹)).mp
  simpa only [symplecticClassWord_replicate, mul_assoc, mul_inv_cancel, mul_one] using he

end QuditClifford.Circuit

namespace QuditClifford.NormalBoxes
open Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

set_option linter.unusedSectionVars false in
private theorem AWord_commute_H_offwire (A : ABox (ZMod d))
    (i j : Fin n) (hij : i ≠ j) :
    Commute (symplecticClassWord g (A.toWord i)) (symplecticClassWord g [.H j]) := by
  have hH : Commute (symplecticClassWord g [.H i]) (symplecticClassWord g [.H j]) :=
    congrArg (presentedToSymplectic g)
      (classWord_disjoint g (.H i) (.H j) (by simpa [Gate.support] using hij.symm)).eq
  have hS (t : ZMod d) : Commute (symplecticClassWord g (Sexp i t))
      (symplecticClassWord g [.H j]) := by
    have h := congrArg (presentedToSymplectic g)
      ((classWord_disjoint g (.S i) (.H j) (by simpa [Gate.support] using hij.symm)).pow_left t.val).eq
    simpa only [map_mul, map_pow, presentedToSymplectic_classWord,
      Sexp, symplecticClassWord_replicate] using h
  by_cases ha : A.a=0
  · rw [ABox.toWord, dif_pos ha]
    exact (symplecticClassWord_H_commute_multiplier_offwire g i j hij _).symm
  · rw [ABox.toWord, dif_neg ha, symplecticClassWord_append, symplecticClassWord_append]
    exact ((symplecticClassWord_H_commute_multiplier_offwire g i j hij _).symm.mul_left hH).mul_left (hS _)

/-- If the B label has first parameter zero and the A label has nonzero first
parameter, CZ is absorbed by subtracting that A parameter from the B label. -/
theorem symplecticDerives_AB_CZ_zero_nonzero (A : ABox (ZMod d)) (ha : A.a ≠ 0)
    (k : ZMod d) (i j : Fin n) (hij : i ≠ j) :
    SymplecticDerives g (bWord 0 k i j hij ++ A.toWord j ++ [.CZ i j hij])
      (bWord 0 (k-A.a) i j hij ++ A.toWord j) := by
  let M := symplecticClassWord g (Circuit.multiplier j (Units.mk0 A.a ha))
  let H := symplecticClassWord g [.H j]
  let C := symplecticClassWord g [.CZ i j hij]
  let K (a : ZMod d) := symplecticClassWord g (power (Circuit.CX i j hij) a.val)
  let S := symplecticClassWord g (Sexp j (-A.b/A.a))
  have hHC : H*C=(symplecticClassWord g (Circuit.CX i j hij))⁻¹*H := by
    have hh := symplecticClassWord_H_CZ_Hinv g i j hij
    change H*C*H⁻¹=(symplecticClassWord g (Circuit.CX i j hij))⁻¹ at hh
    calc
      _ = (H*C*H⁻¹)*H := by group
      _ = _ := by rw [hh]
  have hMK : M*(symplecticClassWord g (Circuit.CX i j hij))⁻¹=(K A.a)⁻¹*M := by
    have hm := symplecticClassWord_multiplier_CX_target g i j hij (Units.mk0 A.a ha)
    have hm' : SemiconjBy M (symplecticClassWord g (Circuit.CX i j hij)) (K A.a) := by
      simpa only [M, K, symplecticClassWord_power] using hm
    exact hm'.inv_right
  have hSC : Commute S C := by
    have hc := congrArg (presentedToSymplectic g)
      ((classWord_CZ_commute_S_right g i j hij).symm.pow_left (-A.b/A.a).val).eq
    simpa only [map_mul, map_pow, presentedToSymplectic_classWord, S, C,
      Sexp, symplecticClassWord_replicate] using hc
  have hK : K (k-A.a)=K k*(K A.a)⁻¹ := by
    have h := congrArg (presentedToSymplectic g) (classWord_CXpower_add g i j hij k (-A.a))
    have hn := congrArg (presentedToSymplectic g) (classWord_CXpower_neg g i j hij A.a)
    simp only [map_mul, map_inv, presentedToSymplectic_classWord] at h hn
    simpa only [sub_eq_add_neg, hn] using h
  have hA : M*H*S*C=(K A.a)⁻¹*(M*H*S) := by
    calc
      _ = M*(H*C)*S := by rw [mul_assoc (M*H), hSC.eq]; group
      _ = (K A.a)⁻¹*(M*H*S) := by
        rw [hHC, ← mul_assoc M, hMK]
        group
  apply (symplecticClassWord_eq_iff_derives g _ _).mp
  simp only [bWord, if_pos rfl, ABox.toWord, dif_neg ha,
    symplecticClassWord_append]
  change (symplecticClassWord g (Circuit.SWAP (d := d) i j hij)*K k)*(M*H*S)*C =
    (symplecticClassWord g (Circuit.SWAP (d := d) i j hij)*K (k-A.a))*(M*H*S)
  have hA' : M*H*S*C=(K A.a)⁻¹*(M*H*S) := hA
  calc
    _ = (symplecticClassWord g (Circuit.SWAP (d := d) i j hij)*K k)*(M*H*S*C) := by group
    _ = _ := by rw [hA', hK]; group

/-- The zero-first-parameter AB/CZ case, including both zero and nonzero
second B parameters in one formula. The scalar-and-Pauli-erased correction
is S_j^(-2 k/b) CZ^(1/b). -/
theorem symplecticDerives_AB_CZ_zero_zero (A : ABox (ZMod d)) (ha : A.a = 0)
    (k : ZMod d) (i j : Fin n) (hij : i ≠ j) :
    SymplecticDerives g (bWord 0 k i j hij ++ A.toWord j ++ [.CZ i j hij])
      (Sexp j (-2*k*A.b⁻¹) ++ List.replicate A.b⁻¹.val (.CZ i j hij) ++
        bWord 0 k i j hij ++ A.toWord j) := by
  let W := symplecticClassWord g (Circuit.SWAP (d := d) i j hij)
  let K := symplecticClassWord g (power (Circuit.CX i j hij) k.val)
  let M := symplecticClassWord g (Circuit.multiplier j (Units.mk0 A.b (A.b_ne_zero ha)))
  let C := symplecticClassWord g [.CZ i j hij]
  let P := symplecticClassWord g (List.replicate A.b⁻¹.val (.CZ i j hij))
  let T := symplecticClassWord g (Sexp i (-2*k*A.b⁻¹))
  let T' := symplecticClassWord g (Sexp j (-2*k*A.b⁻¹))
  have hMC : M*C=P*M := by
    have h := congrArg (presentedToSymplectic g)
      (classWord_multiplier_CZpow_right g Fact.out i j hij
        (Units.mk0 A.b (A.b_ne_zero ha)) (1 : ZMod d))
    simpa only [map_mul, map_pow, presentedToSymplectic_classWord, ZMod.val_one,
      one_mul, pow_one, Units.val_inv_eq_inv_val, Units.val_mk0,
      symplecticClassWord_replicate, M, C, P] using h
  have hKP : K*P=T*P*K := symplecticClassWord_CXpower_CZexp g i j hij k A.b⁻¹
  have hWT : W*T=T'*W := by
    exact congrArg (presentedToSymplectic g)
      ((classWord_eq_iff_derives g _ _).mpr
        (derives_SWAP_Sexp_left g i j hij (-2*k*A.b⁻¹)))
  have hWP : Commute W P := by
    have h := congrArg (presentedToSymplectic g)
      ((classWord_SWAP_commute_CZ g i j hij).pow_right A.b⁻¹.val).eq
    simpa only [map_mul, map_pow, presentedToSymplectic_classWord,
      symplecticClassWord_replicate, W, P] using h
  apply (symplecticClassWord_eq_iff_derives g _ _).mp
  simp only [bWord, if_pos rfl, ABox.toWord, dif_pos ha, symplecticClassWord_append]
  change W*K*M*C=T'*P*(W*K)*M
  calc
    _ = W*(K*(M*C)) := by group
    _ = W*(K*P)*M := by rw [hMC]; group
    _ = (W*T)*P*K*M := by rw [hKP]; group
    _ = T'*P*(W*K)*M := by
      rw [hWT]
      simp only [mul_assoc]
      rw [← mul_assoc W, hWP.eq]
      group

/-- The shorter one-A label when the two first-wire exponents cancel. -/
def ABox.collisionStep (A : ABox (ZMod d)) (ha : A.a=0) (k : ZMod d) : ABox (ZMod d) :=
  ⟨A.b, k, fun h => A.b_ne_zero ha (congrArg Prod.snd h)⟩

/-- The collision branch `a=0, c=b`: the two-box chain shortens to a single
A box on the first wire. This follows by reversing the nonzero A/CZ rewrite. -/
theorem symplecticDerives_AB_CZ_collision (A : ABox (ZMod d)) (ha : A.a=0)
    (k : ZMod d) (i j : Fin n) (hij : i ≠ j) :
    SymplecticDerives g (bWord A.b k i j hij ++ A.toWord j ++ [.CZ i j hij])
      (inverseWord d ([.H j] ++ List.replicate A.b⁻¹.val (.CZ i j hij) ++
        List.replicate 3 (.H j)) ++ [.H j, .H j] ++ (A.collisionStep ha k).toWord i) := by
  let N := A.collisionStep ha k
  have hn : N.a ≠ 0 := A.b_ne_zero ha
  let u : (ZMod d)ˣ := Units.mk0 A.b (A.b_ne_zero ha)
  let B := symplecticClassWord g (bWord A.b k i j hij)
  let U := symplecticClassWord g (N.toWord i)
  let H := symplecticClassWord g [.H j]
  let C := symplecticClassWord g [.CZ i j hij]
  let M := symplecticClassWord g (Circuit.multiplier j u)
  let Mneg := symplecticClassWord g (Circuit.multiplier j (-u))
  let dir : Circuit.Word n := [.H j] ++ List.replicate A.b⁻¹.val (.CZ i j hij) ++
    List.replicate 3 (.H j)
  let D := symplecticClassWord g dir
  have hneg : (N.controlledPhaseStep hn).toWord j = Circuit.multiplier j (-u) := by
    simp only [ABox.toWord, ABox.controlledPhaseStep, ↓reduceDIte]
    congr 1
    exact Units.ext rfl
  have hF : U*C=D*B*Mneg := by
    have h := (symplecticClassWord_eq_iff_derives g _ _).mpr
      (symplecticDerives_A_CZ_nonzero g N hn i j hij)
    rw [hneg] at h
    simpa only [symplecticClassWord_append] using h
  have hNM : Mneg*H^2=M := by
    change symplecticClassWord g (Circuit.multiplier j (-u)) * symplecticClassWord g [.H j] ^2 = _
    rw [symplecticClassWord_H_sq, ← symplecticClassWord_multiplier_mul g Fact.out]
    simp only [neg_mul_neg, mul_one]
    rfl
  have hHC : C*H^2=H^2*C⁻¹ := by
    have h := congrArg (presentedToSymplectic g) (classWord_H_sq_conjugate_CZ_right g i j hij)
    change H^2*C*(H^2)⁻¹=C⁻¹ at h
    have hh : H^4=1 := by
      have h4 := (symplecticClassWord_eq_iff_derives g _ _).mpr
        (derives_symplectic g (derives_H_four Fact.out g Fact.out j))
      simpa only [symplecticClassWord_replicate, symplecticClassWord_nil] using h4
    have hi : (H^2)⁻¹=H^2 := by
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_add]
      exact hh
    rw [← h, hi]
    calc
      _ = (H^2*H^2)*C*H^2 := by rw [← pow_add, hh, one_mul]
      _ = _ := by group
  have hHU : Commute U (H^2) := (AWord_commute_H_offwire g N i j hij).pow_right 2
  have he : D*(B*M*C)=H^2*U := by
    calc
      _ = (D*B*Mneg)*H^2*C := by rw [← hNM]; group
      _ = U*(C*H^2)*C := by rw [← hF]; group
      _ = U*H^2 := by rw [hHC]; group
      _ = _ := hHU.eq
  have hA : symplecticClassWord g (A.toWord j)=M := by
    simp only [ABox.toWord, dif_pos ha]
    rfl
  apply (symplecticClassWord_eq_iff_derives g _ _).mp
  simp only [symplecticClassWord_append, symplecticClassWord_inverseWord, hA]
  change B*M*C=D⁻¹*(H*H)*U
  calc
    _ = D⁻¹*(D*(B*M*C)) := by group
    _ = _ := by rw [he]; simp only [pow_two, mul_assoc]


/-- The remaining A label in the noncolliding zero-first-parameter case. -/
def ABox.zeroDifferenceStep (A : ABox (ZMod d)) (c : ZMod d) (hbc : A.b-c ≠ 0) :
    ABox (ZMod d) := ⟨0, A.b-c, fun h => hbc (congrArg Prod.fst h)⟩

/-- The noncolliding zero-first-parameter AB/CZ branch, with the paper's
multiplier and Fourier-conjugated CZ correction. The inverse H word is the
literal three-H expansion. -/
theorem symplecticDerives_AB_CZ_zero_distinct (A : ABox (ZMod d)) (ha : A.a=0)
    (c k : ZMod d) (hc : c ≠ 0) (hbc : A.b-c ≠ 0)
    (i j : Fin n) (hij : i ≠ j) :
    SymplecticDerives g (bWord c k i j hij ++ A.toWord j ++ [.CZ i j hij])
      (Circuit.multiplier j ((Units.mk0 (A.b-c) hbc / Units.mk0 A.b (A.b_ne_zero ha))⁻¹) ++
        [.H j] ++ List.replicate A.b⁻¹.val (.CZ i j hij) ++ inverseWord d [.H j] ++
        bWord c k i j hij ++ (A.zeroDifferenceStep c hbc).toWord j) := by
  let b : (ZMod d)ˣ := Units.mk0 A.b (A.b_ne_zero ha)
  let r : (ZMod d)ˣ := Units.mk0 (A.b-c) hbc
  let v : (ZMod d)ˣ := r/b
  let H := symplecticClassWord g [.H i]
  let J := symplecticClassWord g [.H j]
  let C (t : ZMod d) := symplecticClassWord g (List.replicate t.val (.CZ i j hij))
  let W := symplecticClassWord g (Circuit.SWAP (d := d) i j hij)
  let K := J⁻¹*C c*J
  let L := H⁻¹*C (-A.b⁻¹)*H
  let D := J*C A.b⁻¹*J⁻¹
  let T := symplecticClassWord g (Sexp i (-k/c))
  let M (a : (ZMod d)ˣ) := symplecticClassWord g (Circuit.multiplier j a)
  let N := symplecticClassWord g (Circuit.multiplier i v⁻¹)
  have hmc : M b*symplecticClassWord g [.CZ i j hij]=C A.b⁻¹*M b := by
    have h := congrArg (presentedToSymplectic g)
      (classWord_multiplier_CZpow_right g Fact.out i j hij b (1 : ZMod d))
    simpa only [map_mul, map_pow, presentedToSymplectic_classWord, ZMod.val_one,
      one_mul, pow_one, Units.val_inv_eq_inv_val, Units.val_mk0, b, C, M,
      symplecticClassWord_replicate] using h
  have hTC : Commute T (C A.b⁻¹) := by
    have h := congrArg (presentedToSymplectic g)
      (((classWord_CZ_commute_S_first g i j hij).symm.pow_left (-k/c).val).pow_right A.b⁻¹.val).eq
    simpa only [map_mul, map_pow, presentedToSymplectic_classWord, Sexp,
      symplecticClassWord_replicate, T, C] using h
  have hHC : H*C A.b⁻¹=L*H := by
    have h := symplecticClassWord_H_sq_CZexp_left g i j hij A.b⁻¹
    change H^2*C A.b⁻¹=C (-A.b⁻¹)*H^2 at h
    calc
      _ = H⁻¹*(H^2*C A.b⁻¹) := by group
      _ = _ := by rw [h]; dsimp only [L]; simp only [pow_two, mul_assoc]
  have hv : (v : ZMod d)=1+c*(-A.b⁻¹) := by
    dsimp [v, r, b]
    simp only [Units.val_div_eq_div_val, Units.val_mk0]
    field_simp [A.b_ne_zero ha]
    ring
  have hG : K*L=N*L*K*M v := by
    exact symplecticClassWord_CX_gaussian g i j hij (Units.mk0 c hc) v (-A.b⁻¹) hv
  have hWN : W*N=M v⁻¹*W := by
    exact (symplecticClassWord_eq_iff_derives g _ _).mpr
      (derives_symplectic g (derives_SWAP_multiplier_left g i j hij v⁻¹))
  have hWH : SemiconjBy W H J := by
    exact congrArg (presentedToSymplectic g) (classWord_SWAP_H_left g i j hij)
  have hWC : Commute W (C (-A.b⁻¹)) := by
    have h := congrArg (presentedToSymplectic g)
      ((classWord_SWAP_commute_CZ g i j hij).pow_right (-A.b⁻¹).val).eq
    simpa only [map_mul, map_pow, presentedToSymplectic_classWord, C,
      symplecticClassWord_replicate] using h
  have hflip : J⁻¹*C (-A.b⁻¹)*J=D := by
    have hf := symplecticClassWord_H_sq_CZexp_right g i j hij A.b⁻¹
    change J^2*C A.b⁻¹=C (-A.b⁻¹)*J^2 at hf
    calc
      _ = J⁻¹*(C (-A.b⁻¹)*J^2)*J⁻¹ := by group
      _ = J⁻¹*(J^2*C A.b⁻¹)*J⁻¹ := by rw [← hf]
      _ = _ := by dsimp only [D]; group
  have hWL : W*L=D*W := by
    dsimp only [L]
    calc
      _ = J⁻¹*(W*C (-A.b⁻¹))*H := by
        simp only [← mul_assoc]
        rw [hWH.inv_right]
      _ = J⁻¹*C (-A.b⁻¹)*(W*H) := by rw [hWC.eq]; group
      _ = (J⁻¹*C (-A.b⁻¹)*J)*W := by rw [hWH.eq]; group
      _ = _ := by rw [hflip]
  have hHT : Commute (H*T) (M v) := by
    have hH : Commute H (M v) := symplecticClassWord_H_commute_multiplier_offwire g j i hij.symm v
    have hT : Commute T (M v) := by
      have he : Commute (classWord g (Sexp i (-k/c))) (classWord g (Circuit.multiplier j v)) := by
        apply classWord_commute_multiplier_of_avoids
        intro q hq
        have hh : q=.S i := (List.mem_replicate.mp hq).2
        subst q
        simpa only [Gate.support, Finset.mem_singleton] using hij.symm
      exact congrArg (presentedToSymplectic g) he.eq
    exact hH.mul_left hT
  have hMb : M v*M b=M r := by
    change symplecticClassWord g (Circuit.multiplier j v) *
      symplecticClassWord g (Circuit.multiplier j b) = _
    rw [← symplecticClassWord_multiplier_mul g Fact.out]
    have hu : v*b=r := by simp only [v, div_eq_mul_inv, mul_assoc, inv_mul_cancel, mul_one]
    rw [hu]
  have hA : symplecticClassWord g (A.toWord j)=M b := by
    simp only [ABox.toWord, dif_pos ha]
    rfl
  have hA' : symplecticClassWord g ((A.zeroDifferenceStep c hbc).toWord j)=M r := by
    simp only [ABox.toWord, ABox.zeroDifferenceStep, ↓reduceDIte]
    rfl
  have hB : symplecticClassWord g (bWord c k i j hij)=W*K*H*T := by
    simp only [bWord, if_neg hc, symplecticClassWord_append,
      symplecticClassWord_CXpower_expand]
    simp only [W, K, J, C, H, T, symplecticClassWord_replicate]
  apply (symplecticClassWord_eq_iff_derives g _ _).mp
  simp only [symplecticClassWord_append, symplecticClassWord_inverseWord, hA, hA', hB]
  change (W*K*H*T)*M b*symplecticClassWord g [.CZ i j hij]=
    M v⁻¹*J*C A.b⁻¹*J⁻¹*(W*K*H*T)*M r
  calc
    _ = W*K*(H*C A.b⁻¹)*T*M b := by
      simp only [mul_assoc]
      rw [hmc, ← mul_assoc T, hTC.eq]
      group
    _ = W*(K*L)*(H*T)*M b := by rw [hHC]; group
    _ = (W*N)*L*K*(M v*(H*T))*M b := by rw [hG]; group
    _ = M v⁻¹*(W*L)*K*(H*T)*(M v*M b) := by
      rw [hWN, hHT.symm.eq]
      group
    _ = _ := by rw [hWL, hMb]; dsimp only [D]; group

end QuditClifford.NormalBoxes
