import QuditClifford.SymplecticTwoWireB

/-!
# The nonzero-a controlled-phase D-box rewrite

The final D case uses the explicitly derived quadratic CX conjugation laws.
It remains a syntactic symplectic rewrite, never a matrix-equality shortcut.
-/
noncomputable section
namespace QuditClifford.Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

/-- Expanded controlled addition is the syntactic H conjugate of CZ. -/
theorem symplecticClassWord_CX_expand (i j : Fin n) (hij : i ≠ j) :
    symplecticClassWord g (CX i j hij) =
      (symplecticClassWord g [.H j])⁻¹ * symplecticClassWord g [.CZ i j hij] *
        symplecticClassWord g [.H j] := by
  have hh := congrArg (presentedToSymplectic g)
    ((classWord_eq_iff_derives g _ _).mpr (derives_H_four Fact.out g Fact.out j))
  have hi : (symplecticClassWord g [.H j])⁻¹ = symplecticClassWord g [.H j] ^3 := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ']
    simpa only [presentedToSymplectic_classWord, symplecticClassWord_replicate,
      symplecticClassWord_nil] using hh
  rw [hi]
  change symplecticClassWord g [.H j] * symplecticClassWord g [.H j] *
    symplecticClassWord g [.H j] * symplecticClassWord g [.CZ i j hij] *
      symplecticClassWord g [.H j] = _
  simp only [pow_succ, pow_zero, one_mul]


/-- Residue-word form of the powered Fourier conjugation identity. -/
theorem symplecticClassWord_CXpower_expand_residue (i j : Fin n) (hij : i ≠ j) (a : ZMod d) :
    symplecticClassWord g (power (CX i j hij) a.val) =
      (symplecticClassWord g [.H j])⁻¹ *
        symplecticClassWord g (List.replicate a.val (.CZ i j hij)) * symplecticClassWord g [.H j] := by
  simpa only [symplecticClassWord_replicate] using
    symplecticClassWord_CXpower_expand g i j hij a.val

end QuditClifford.Circuit

namespace QuditClifford.Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

/-- The quadratic CX law solves the nonzero controlled-phase/H pivot. -/
theorem symplecticClassWord_CZexp_H_CZ (i j : Fin n) (hij : i ≠ j)
    (a : ZMod d) (ha : a ≠ 0) :
    symplecticClassWord g (List.replicate (-a).val (.CZ i j hij)) *
        symplecticClassWord g [.H j] * symplecticClassWord g [.CZ i j hij] =
      symplecticClassWord g [.H j] * symplecticClassWord g (Sexp i a) *
        symplecticClassWord g (Sexp j (-a⁻¹)) *
          symplecticClassWord g (power (CX i j hij) (-a).val) *
            symplecticClassWord g (Sexp j a⁻¹) := by
  let H := symplecticClassWord g [.H j]
  let C := symplecticClassWord g [.CZ i j hij]
  let A := symplecticClassWord g (power (CX i j hij) (-a).val)
  let Si := symplecticClassWord g (Sexp i a)
  let Sj := symplecticClassWord g (Sexp j a⁻¹)
  have hSS : A * Sj * A⁻¹ = Sj * Si * C := by
    have ht := symplecticClassWord_CXpower_conjugate_Sexp g i j hij (-a) a⁻¹
    have h1 : a⁻¹ * (-a * -a) = a := by field_simp
    have h2 : a⁻¹ * -(-a) = 1 := by simpa only [neg_neg] using inv_mul_cancel₀ ha
    rw [h1, h2, ZMod.val_one, List.replicate_one] at ht
    exact ht
  have hCC : A * C * A⁻¹ = Si * Si * C := by
    have ht := symplecticClassWord_CXpower_conjugate_CZ g i j hij (-a)
    have he : -2 * -a = a+a := by ring
    rw [he, symplecticClassWord_Sexp_add] at ht
    exact ht
  have he : A*C = Si*Sj⁻¹*A*Sj := by
    calc
      _ = Si*Si*C*A := by
        have ht := congrArg (fun t => t*A) hCC
        simpa only [mul_assoc, inv_mul_cancel, mul_one] using ht
      _ = Si*Sj⁻¹*(A*Sj*A⁻¹)*A := by rw [hSS]; group
      _ = _ := by group
  have hA : A = H⁻¹ * symplecticClassWord g (List.replicate (-a).val (.CZ i j hij)) * H :=
    symplecticClassWord_CXpower_expand_residue g i j hij (-a)
  rw [symplecticClassWord_Sexp_neg]
  change _ * H * C = H * Si * Sj⁻¹ * A * Sj
  calc
    _ = H * (A*C) := by rw [hA]; group
    _ = _ := by rw [he]; group

end QuditClifford.Circuit
namespace QuditClifford.NormalBoxes
open Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

/-- The ninth D-box case: a nonzero-a D box absorbs CZ and emits the source's
phase on the second wire and H-S-H-inverse correction on the first wire. -/
theorem symplectic_D_CZ_nonzero (a b : ZMod d) (ha : a ≠ 0)
    (i j : Fin n) (hij : i ≠ j) :
    SymplecticDerives g (dWord a b i j hij ++ [.CZ i j hij])
      (Sexp j a ++ [.H i] ++ Sexp i (-a⁻¹) ++ inverseWord d [.H i] ++
        dWord a (b-1) i j hij) := by
  let W := symplecticClassWord g (Circuit.SWAP (d := d) i j hij)
  let H := symplecticClassWord g [.H j]
  let Hi := symplecticClassWord g [.H i]
  let C := symplecticClassWord g [.CZ i j hij]
  let Cp := symplecticClassWord g (List.replicate (-a).val (.CZ i j hij))
  let A := symplecticClassWord g (power (Circuit.CX i j hij) (-a).val)
  let Si (r : ZMod d) := symplecticClassWord g (Sexp i r)
  let Sj (r : ZMod d) := symplecticClassWord g (Sexp j r)
  have hc : Commute (Sj (-b/a)) C := by
    have ht := (classWord_CZ_commute_S_right g i j hij).symm.pow_left (-b/a).val
    simpa only [Sj, C, Sexp, symplecticClassWord_replicate, Commute, SemiconjBy,
      map_mul, map_pow, presentedToSymplectic_classWord] using
      congrArg (presentedToSymplectic g) ht.eq
  have hh : Cp*H*C = H*Si a*Sj (-a⁻¹)*A*Sj a⁻¹ :=
    symplecticClassWord_CZexp_H_CZ g i j hij a ha
  have hA : A = H⁻¹*Cp*H := symplecticClassWord_CXpower_expand_residue g i j hij (-a)
  have hHS : Commute H (Si a) := by
    have ht := (classWord_disjoint g (.H j) (.S i)
      (by simpa [Gate.support] using hij)).pow_right a.val
    simpa only [H, Si, Sexp, symplecticClassWord_replicate, Commute, SemiconjBy,
      map_mul, map_pow, presentedToSymplectic_classWord] using
      congrArg (presentedToSymplectic g) ht.eq
  have hWS : W*Si a = Sj a*W := by
    have ht := (classWord_eq_iff_derives g _ _).mpr (derives_SWAP_Sexp_left g i j hij a)
    exact congrArg (presentedToSymplectic g) ht
  have hWH : SemiconjBy W H Hi :=
    congrArg (presentedToSymplectic g) (classWord_SWAP_H_right g i j hij)
  have hWS' : SemiconjBy W (Sj (-a⁻¹)) (Si (-a⁻¹)) :=
    congrArg (presentedToSymplectic g) (classWord_SWAP_Sexp_right g i j hij (-a⁻¹))
  have hWconj : W*(H*Sj (-a⁻¹)*H⁻¹) = (Hi*Si (-a⁻¹)*Hi⁻¹)*W :=
    (hWH.mul_right hWS').mul_right hWH.inv_right
  have hexp : a⁻¹ + -b/a = -(b-1)/a := by field_simp; ring
  have hadd : Sj a⁻¹ * Sj (-b/a) = Sj (-(b-1)/a) := by
    rw [← symplecticClassWord_Sexp_add, hexp]
  have ht : W*Cp*H*Sj (-b/a)*C =
      Sj a*Hi*Si (-a⁻¹)*Hi⁻¹*(W*Cp*H*Sj (-(b-1)/a)) := by
    calc
      _ = W*Cp*H*(Sj (-b/a)*C) := by group
      _ = W*Cp*H*(C*Sj (-b/a)) := by rw [hc.eq]
      _ = W*(Cp*H*C)*Sj (-b/a) := by group
      _ = W*(H*Si a*Sj (-a⁻¹)*A*Sj a⁻¹)*Sj (-b/a) := by rw [hh]
      _ = W*(H*Si a)*Sj (-a⁻¹)*A*(Sj a⁻¹*Sj (-b/a)) := by group
      _ = W*(Si a*H)*Sj (-a⁻¹)*(H⁻¹*Cp*H)*Sj (-(b-1)/a) := by rw [hHS.eq, hA, hadd]
      _ = (W*Si a)*(H*Sj (-a⁻¹)*H⁻¹)*Cp*H*Sj (-(b-1)/a) := by group
      _ = (Sj a*W)*(H*Sj (-a⁻¹)*H⁻¹)*Cp*H*Sj (-(b-1)/a) := by rw [hWS]
      _ = Sj a*(W*(H*Sj (-a⁻¹)*H⁻¹))*Cp*H*Sj (-(b-1)/a) := by group
      _ = _ := by rw [hWconj]; group
  apply (symplecticClassWord_eq_iff_derives g _ _).mp
  simpa only [dWord, if_neg ha, symplecticClassWord_append, symplecticClassWord_inverseWord,
    W, H, Hi, C, Cp, Si, Sj, mul_assoc] using ht

end QuditClifford.NormalBoxes
