import QuditClifford.ControlledZInversion

/-!
# Exact Pauli X pushing through controlled Z

The proof conjugates the exact C12 rule by H squared on the opposite wire,
then follows the six primitive letters in the definition of X. All equalities
are established inside the genuine syntactic quotient.
-/

noncomputable section
namespace QuditClifford.Circuit

private theorem conjugation_fixed {G : Type*} [Group G] {a b : G}
    (hc : Commute a b) : MulAut.conj a b = b := by
  rw [MulAut.conj_apply, hc.eq]
  group

/-- The group calculation underlying controlled-Z pushing, with all its
local rewrite dependencies stated explicitly. -/
private theorem controlled_X_algebra {G : Type*} [Group G] (h s t c a z : G)
    (hHc : MulAut.conj h c = a⁻¹) (hHa : MulAut.conj h a = c)
    (hHt : Commute h t) (hHz : Commute h z)
    (hSc : Commute s c) (hSt : Commute s t) (hSz : Commute s z)
    (hCt : Commute c t) (hCz : Commute c z) (hTz : Commute t z)
    (hA : a⁻¹*s*a = s*t*c) (hF : a*s*a⁻¹ = s*t*z*c⁻¹) :
    c*(h*s*h^2*s⁻¹*h) = (h*s*h^2*s⁻¹*h)*z*c := by
  let H := MulAut.conj h
  let S := MulAut.conj s
  have Hc : H c = a⁻¹ := hHc
  have Ha : H a = c := hHa
  have Ht : H t = t := conjugation_fixed hHt
  have Sc : S c = c := conjugation_fixed hSc
  have St : S t = t := conjugation_fixed hSt
  have Sa : S a = a*t*c := by
    change s*a*s⁻¹ = _
    calc
      _ = a*(a⁻¹*s*a)*s⁻¹ := by group
      _ = a*(s*t*c)*s⁻¹ := by rw [hA]
      _ = a*(t*c)*s*s⁻¹ := by
        simpa only [mul_assoc] using congrArg (fun q : G => a*q*s⁻¹) (hSt.mul_right hSc).eq
      _ = _ := by group
  have Si : S⁻¹ a⁻¹ = t*c*a⁻¹ := by
    change s⁻¹*a⁻¹*s = _
    calc
      _ = s⁻¹*(a⁻¹*s*a)*a⁻¹ := by group
      _ = _ := by rw [hA]; group
  have Fi : a*s⁻¹*a⁻¹ = c*z⁻¹*t⁻¹*s⁻¹ := by
    have he := congrArg (fun q : G => q⁻¹) hF
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using he
  have step : MulAut.conj (h*s*h^2*s⁻¹*h) c =
      H (S (H (H (S⁻¹ (H c))))) := by
    simp only [MulAut.conj_apply, MulAut.conj_inv_apply, H, S, pow_two]
    group
  have chain : MulAut.conj (h*s*h^2*s⁻¹*h) c = t*a*c*t*a⁻¹ := by
    rw [step]
    simp only [Hc, Si, map_mul, map_inv, Ht, Ha, inv_inv, St, Sc, Sa, mul_assoc]
  have collapse : t*a*c*t*a⁻¹ = z⁻¹*c := by
    have sunfold : a*t*c = s*a*s⁻¹ := Sa.symm
    calc
      _ = t*(a*t*c)*a⁻¹ := by
        simpa only [mul_assoc] using congrArg (fun q : G => t*a*q*a⁻¹) hCt.eq
      _ = t*s*(a*s⁻¹*a⁻¹) := by rw [sunfold]; group
      _ = t*s*(c*z⁻¹*t⁻¹*s⁻¹) := by rw [Fi]
      _ = (c*z⁻¹)*(t*s*t⁻¹*s⁻¹) := by
        have hc := (hCt.symm.mul_right hTz.inv_right).mul_left
          (hSc.mul_right hSz.inv_right)
        simpa only [mul_assoc] using congrArg (fun q : G => q*t⁻¹*s⁻¹) hc.eq
      _ = _ := by
        rw [hSt.symm.eq]
        simp only [mul_assoc, mul_inv_cancel, inv_mul_cancel, mul_one, one_mul]
        exact hCz.inv_right.eq
  have he : (h*s*h^2*s⁻¹*h)*c*(h*s*h^2*s⁻¹*h)⁻¹ = z⁻¹*c :=
    chain.trans collapse
  have hxz : Commute (h*s*h^2*s⁻¹*h) z :=
    (((hHz.mul_left hSz).mul_left (hHz.pow_left 2)).mul_left hSz.inv_left).mul_left hHz
  calc
    _ = z*((h*s*h^2*s⁻¹*h)*c*(h*s*h^2*s⁻¹*h)⁻¹)*(h*s*h^2*s⁻¹*h) := by rw [he]; group
    _ = z*(h*s*h^2*s⁻¹*h)*c := by group
    _ = _ := by rw [hxz.symm.eq]

variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

private abbrev h (i : Fin n) : PresentedCircuit g n := classWord g [.H i]
private abbrev s (i : Fin n) : PresentedCircuit g n := classWord g [.S i]
private abbrev z (i : Fin n) : PresentedCircuit g n := classWord g (Z (d := d) i)
private abbrev c (i j : Fin n) (hij : i ≠ j) : PresentedCircuit g n := classWord g [.CZ i j hij]
private abbrev a (i j : Fin n) (hij : i ≠ j) : PresentedCircuit g n := classWord g (CX i j hij)

set_option linter.unusedSectionVars false in
private theorem gate_commute (a b : Gate n) (hd : Disjoint a.support b.support) :
    Commute (classWord g [a]) (classWord g [b]) :=
  (classWord_eq_iff_derives g _ _).mpr (.rule (Or.inl (Structural.disjoint a b hd)))

private theorem HH_commute (i j : Fin n) (hij : i ≠ j) : Commute (h g i) (h g j) := by
  apply gate_commute
  simpa [Gate.support] using hij.symm

private theorem HS_commute (i j : Fin n) (hij : i ≠ j) : Commute (h g i) (s g j) := by
  apply gate_commute
  simpa [Gate.support] using hij.symm

private theorem SS_commute (i j : Fin n) (hij : i ≠ j) : Commute (s g i) (s g j) := by
  apply gate_commute
  simpa [Gate.support] using hij.symm

private theorem h_four (i : Fin n) : h g i^4 = 1 := by
  have he := (classWord_eq_iff_derives g (List.replicate 4 (.H i)) []).mpr
    (derives_H_four Fact.out g Fact.out i)
  simpa only [classWord_replicate, classWord_nil] using he

private theorem h_inv (i : Fin n) : (h g i)⁻¹ = h g i^3 := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ', h_four]

private theorem h_sq_inv (i : Fin n) : (h g i^2)⁻¹ = h g i^2 := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_add]
  exact h_four g i

/-- Expanded Z as a group product, using the actual S inverse derivation. -/
theorem classWord_Z_expand (i : Fin n) :
    classWord g (Z (d := d) i) =
      classWord g [.H i] ^ 2 * classWord g [.S i] * classWord g [.H i] ^ 2 * (classWord g [.S i])⁻¹ := by
  change (h g i * h g i * s g i * h g i * h g i) *
    classWord g (Sexp i (-1 : ZMod d)) = _
  rw [classWord_Sexp_neg_one]
  simp only [pow_two, mul_assoc, h, s]

/-- Expanded X as a group product, using the actual S inverse derivation. -/
theorem classWord_X_expand (i : Fin n) :
    classWord g (X (d := d) i) = classWord g [.H i] * classWord g [.S i] *
      classWord g [.H i] ^ 2 * (classWord g [.S i])⁻¹ * classWord g [.H i] := by
  change (h g i * s g i * h g i * h g i) *
    classWord g (Sexp i (-1 : ZMod d)) * h g i = _
  rw [classWord_Sexp_neg_one]
  simp only [pow_two, mul_assoc, h, s]

private theorem HZ_disjoint (i j : Fin n) (hij : i ≠ j) : Commute (h g i) (z g j) := by
  simp only [z]
  rw [classWord_Z_expand]
  exact ((((HH_commute g i j hij).pow_right 2).mul_right (HS_commute g i j hij)).mul_right
    ((HH_commute g i j hij).pow_right 2)).mul_right (HS_commute g i j hij).inv_right

private theorem SZ_disjoint (i j : Fin n) (hij : i ≠ j) : Commute (s g i) (z g j) := by
  simp only [z]
  rw [classWord_Z_expand]
  exact ((((HS_commute g j i hij.symm).symm.pow_right 2).mul_right (SS_commute g i j hij)).mul_right
    ((HS_commute g j i hij.symm).symm.pow_right 2)).mul_right (SS_commute g i j hij).inv_right

/-- T5 is exactly Fourier conjugation of CZ in the word quotient. -/
theorem classWord_CX_conjugate (i j : Fin n) (hij : i ≠ j) :
    classWord g (CX i j hij) =
      (classWord g [.H j])⁻¹ * classWord g [.CZ i j hij] * classWord g [.H j] := by
  change h g j*h g j*h g j*c g i j hij*h g j = (h g j)⁻¹*c g i j hij*h g j
  rw [h_inv]
  simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc]

/-- The actual CX word inherits its d-th order from C6 by conjugation. -/
theorem classWord_CX_order (i j : Fin n) (hij : i ≠ j) :
    classWord g (CX i j hij)^d = 1 := by
  rw [classWord_CX_conjugate]
  have he := conj_pow (a := (classWord g [.H j])⁻¹) (b := classWord g [.CZ i j hij]) (i := d)
  simp only [inv_inv, classWord_CZ_order, mul_one, inv_mul_cancel] at he
  exact he

private theorem a_pred (i j : Fin n) (hij : i ≠ j) : a g i j hij^(d-1) = (a g i j hij)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))]
  exact classWord_CX_order g i j hij

/-- C12 in conjugation form, with its primitive CX and S words reduced by
previously derived inverse rules. -/
theorem classWord_CX_inv_conjugate_S (i j : Fin n) (hij : i ≠ j) :
    (classWord g (CX i j hij))⁻¹ * classWord g [.S j] *
      classWord g (CX i j hij) =
      classWord g [.S j] * classWord g [.S i] * classWord g [.CZ i j hij] := by
  have he := (classWord_eq_iff_derives g _ _).mpr
    (show Derives g (Sexp i (-1 : ZMod d) ++ Sexp j (-1 : ZMod d) ++
      power (CX i j hij) (d-1) ++ [.S j] ++ CX i j hij) [.CZ i j hij] from
      .rule (Or.inr (Figure1Rule.C12 i j hij)))
  simp only [classWord_append, classWord_Sexp_neg_one, classWord_power] at he
  change (s g i)⁻¹*(s g j)⁻¹*a g i j hij^(d-1)*s g j*a g i j hij = c g i j hij at he
  rw [a_pred] at he
  have he' := congrArg (fun q : PresentedCircuit g n => s g j*s g i*q) he
  change (a g i j hij)⁻¹*s g j*a g i j hij = s g j*s g i*c g i j hij
  simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left] using he'

private theorem h_sq_conjugate_s (i : Fin n) :
    MulAut.conj (h g i^2) (s g i) = s g i*z g i := by
  rw [MulAut.conj_apply, h_sq_inv]
  have he : z g i*s g i = h g i^2*s g i*h g i^2 := by
    change classWord g (Z (d := d) i)*s g i = _
    rw [classWord_Z_expand]
    change (h g i^2*s g i*h g i^2*(s g i)⁻¹)*s g i = _
    group
  exact he.symm.trans (classWord_Z_commute_S g i).eq

/-- Conjugating C12 by H squared on the opposite wire gives its reverse
controlled-addition form and the exact extra Z. -/
theorem classWord_CX_conjugate_S (i j : Fin n) (hij : i ≠ j) :
    classWord g (CX i j hij) * classWord g [.S j] *
      (classWord g (CX i j hij))⁻¹ =
      classWord g [.S j] * classWord g [.S i] * classWord g (Z (d := d) i) *
        (classWord g [.CZ i j hij])⁻¹ := by
  let U := MulAut.conj (h g i^2)
  have Uc : U (c g i j hij) = (c g i j hij)⁻¹ :=
    classWord_H_sq_conjugate_CZ_left g i j hij
  have Uh : U (h g j) = h g j := conjugation_fixed ((HH_commute g i j hij).pow_left 2)
  have Us : U (s g j) = s g j := conjugation_fixed ((HS_commute g i j hij).pow_left 2)
  have Ut : U (s g i) = s g i*z g i := h_sq_conjugate_s g i
  have Ua : U (a g i j hij) = (a g i j hij)⁻¹ := by
    simp only [a, classWord_CX_conjugate]
    change U ((h g j)⁻¹*c g i j hij*h g j) = ((h g j)⁻¹*c g i j hij*h g j)⁻¹
    rw [map_mul, map_mul, map_inv, Uh, Uc]
    group
  have he := congrArg U (classWord_CX_inv_conjugate_S g i j hij)
  change U ((a g i j hij)⁻¹*s g j*a g i j hij) = U (s g j*s g i*c g i j hij) at he
  simp only [map_mul, map_inv, Ua, Us, Ut, Uc, inv_inv, mul_assoc] at he
  exact he

/-- The remaining exact CZ Pauli pushing rule on its second wire, derived
from C12, scalar coherence, C9 and the already proved local relations. -/
theorem classWord_CZ_X_right (i j : Fin n) (hij : i ≠ j) :
    classWord g [.CZ i j hij] * classWord g (X (d := d) j) =
      classWord g (X (d := d) j) * classWord g (Z (d := d) i) * classWord g [.CZ i j hij] := by
  have Hc : MulAut.conj (h g j) (c g i j hij) = (a g i j hij)⁻¹ := by
    rw [MulAut.conj_apply]
    have hsq := classWord_H_sq_conjugate_CZ_right g i j hij
    change h g j^2*c g i j hij*(h g j^2)⁻¹ = (c g i j hij)⁻¹ at hsq
    calc
      _ = (h g j)⁻¹*(h g j^2*c g i j hij*(h g j^2)⁻¹)*h g j := by
        simp only [pow_two]
        group
      _ = (h g j)⁻¹*(c g i j hij)⁻¹*h g j := by rw [hsq]
      _ = _ := by
        simp only [a, classWord_CX_conjugate]
        change (h g j)⁻¹*(c g i j hij)⁻¹*h g j = ((h g j)⁻¹*c g i j hij*h g j)⁻¹
        group
  have Ha : MulAut.conj (h g j) (a g i j hij) = c g i j hij := by
    simp only [a, classWord_CX_conjugate, MulAut.conj_apply]
    change h g j*((h g j)⁻¹*c g i j hij*h g j)*(h g j)⁻¹ = c g i j hij
    group
  have CS : Commute (c g i j hij) (s g j) := by
    change Commute (classWord g [.CZ i j hij]) (classWord g [.S j])
    rw [classWord_CZ_symmetry g i j hij]
    exact classWord_CZ_commute_S_left g j i hij.symm
  have he := controlled_X_algebra (h g j) (s g j) (s g i) (c g i j hij) (a g i j hij) (z g i)
    Hc Ha (HS_commute g j i hij.symm) (HZ_disjoint g j i hij.symm)
    CS.symm (SS_commute g j i hij.symm) (SZ_disjoint g j i hij.symm)
    (classWord_CZ_commute_S_left g i j hij) (classWord_CZ_commute_Z_left g i j hij)
    (classWord_Z_commute_S g i).symm
    (classWord_CX_inv_conjugate_S g i j hij) (classWord_CX_conjugate_S g i j hij)
  simpa only [classWord_X_expand] using he

/-- The corresponding exact first-wire pushing rule follows by structural CZ symmetry. -/
theorem classWord_CZ_X_left (i j : Fin n) (hij : i ≠ j) :
    classWord g [.CZ i j hij] * classWord g (X (d := d) i) =
      classWord g (X (d := d) i) * classWord g (Z (d := d) j) * classWord g [.CZ i j hij] := by
  rw [classWord_CZ_symmetry g i j hij]
  exact classWord_CZ_X_right g j i hij.symm

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
/-- Actual Figure 1 derivation of CZ pushing through first-wire X. -/
theorem derives_CZ_X_left (hd : Odd d) (hg : orderOf g = d-1)
    (i j : Fin n) (hij : i ≠ j) :
    Derives g ([.CZ i j hij] ++ X (d := d) i)
      (X (d := d) i ++ Z (d := d) j ++ [.CZ i j hij]) := by
  letI : Fact (Odd d) := ⟨hd⟩
  letI : Fact (orderOf g = d-1) := ⟨hg⟩
  apply (classWord_eq_iff_derives g _ _).mp
  simpa only [classWord_append] using classWord_CZ_X_left g i j hij

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
/-- Actual Figure 1 derivation of CZ pushing through second-wire X. -/
theorem derives_CZ_X_right (hd : Odd d) (hg : orderOf g = d-1)
    (i j : Fin n) (hij : i ≠ j) :
    Derives g ([.CZ i j hij] ++ X (d := d) j)
      (X (d := d) j ++ Z (d := d) i ++ [.CZ i j hij]) := by
  letI : Fact (Odd d) := ⟨hd⟩
  letI : Fact (orderOf g = d-1) := ⟨hg⟩
  apply (classWord_eq_iff_derives g _ _).mp
  simpa only [classWord_append] using classWord_CZ_X_right g i j hij

end QuditClifford.Circuit
