import QuditClifford.SymplecticTwoWireB

/-!
# Exact local duality of B and D boxes

Fourier conjugation and a reversal of the two named wires relate the literal
B and D words. Adjacent Fourier factors cancel along a two-box chain, giving
a short exact version of the duality used in the source's BB/CZ argument.
-/

noncomputable section
namespace QuditClifford.Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

/-- Exact Fourier-conjugate expansion for any power of the actual CX word. -/
theorem classWord_CXpower_fourier (i j : Fin n) (hij : i ≠ j) (k : ℕ) :
    classWord g (power (CX i j hij) k) =
      (classWord g [.H j])⁻¹ * classWord g [.CZ i j hij] ^k * classWord g [.H j] := by
  rw [classWord_power, classWord_CX_conjugate]
  simpa only [inv_inv] using
    (conj_pow (a := (classWord g [.H j])⁻¹) (b := classWord g [.CZ i j hij]) (i := k))

/-- Reversing the Fourier direction negates the controlled-phase exponent. -/
theorem classWord_H_CZneg_Hinv (i j : Fin n) (hij : i ≠ j) (a : ZMod d) :
    classWord g [.H j] * classWord g [.CZ i j hij] ^(-a).val * (classWord g [.H j])⁻¹ =
      classWord g (power (CX i j hij) a.val) := by
  let H := classWord g [.H j]
  let C := classWord g [.CZ i j hij]
  have h : C^a.val * H^2 = H^2 * C^(-a).val := by
    simpa only [neg_neg] using classWord_CZexp_H_sq_right g i j hij (-a)
  rw [classWord_CXpower_fourier]
  change H*C^(-a).val*H⁻¹=H⁻¹*C^a.val*H
  calc
    _ = H⁻¹*(H^2*C^(-a).val)*H⁻¹ := by group
    _ = H⁻¹*(C^a.val*H^2)*H⁻¹ := by rw [← h]
    _ = _ := by group

end QuditClifford.Circuit
namespace QuditClifford.NormalBoxes
open Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

private theorem B_zero_dual (b : ZMod d) (i j : Fin n) (hij : i ≠ j) :
    classWord g (bWord 0 b i j hij) =
      classWord g [.H i]*classWord g (dWord 0 b j i hij.symm)*(classWord g [.H j])⁻¹ := by
  have hw := (classWord_eq_iff_derives g _ _).mpr (derives_SWAP_symmetry g i j hij)
  simp only [bWord, dWord, if_pos rfl, ↓reduceIte, classWord_append, classWord_replicate]
  rw [← hw, ← classWord_CZ_symmetry g i j hij]
  symm
  calc
    _ = (classWord g [.H i]*classWord g (Circuit.SWAP (d := d) i j hij))*
        classWord g [.CZ i j hij] ^(-b).val*(classWord g [.H j])⁻¹ := by group
    _ = (classWord g (Circuit.SWAP (d := d) i j hij)*classWord g [.H j])*
        classWord g [.CZ i j hij] ^(-b).val*(classWord g [.H j])⁻¹ := by
      rw [← classWord_SWAP_H_right]
    _ = classWord g (Circuit.SWAP (d := d) i j hij)*
        (classWord g [.H j]*classWord g [.CZ i j hij] ^(-b).val*(classWord g [.H j])⁻¹) := by group
    _ = _ := by rw [classWord_H_CZneg_Hinv]

/-- The literal B word is a Fourier sandwich of D with its two named wires
reversed. This is equality in the genuine Figure 1 presentation. -/
theorem classWord_B_dual_D (a b : ZMod d) (i j : Fin n) (hij : i ≠ j) :
    classWord g (bWord a b i j hij) =
      classWord g [.H i]*classWord g (dWord a b j i hij.symm)*(classWord g [.H j])⁻¹ := by
  by_cases ha : a = 0
  · subst a
    exact B_zero_dual g b i j hij
  · have hb : classWord g (bWord a b i j hij) =
        classWord g (bWord 0 a i j hij)*(classWord g [.H i]*classWord g (Sexp i (-b/a))) := by
      simp only [bWord, if_neg ha, if_pos rfl, ↓reduceIte, classWord_append, mul_assoc]
    have hd : classWord g (dWord a b j i hij.symm) =
        classWord g (dWord 0 a j i hij.symm)*(classWord g [.H i]*classWord g (Sexp i (-b/a))) := by
      simp only [dWord, if_neg ha, if_pos rfl, ↓reduceIte, classWord_append, mul_assoc]
    have hh := classWord_disjoint g (.H j) (.H i) (by simpa [Gate.support] using hij)
    have hs := (classWord_disjoint g (.H j) (.S i) (by simpa [Gate.support] using hij)).pow_right (-b/a).val
    have ht : Commute (classWord g [.H j])
        (classWord g [.H i]*classWord g (Sexp i (-b/a))) := by
      simpa only [Sexp, classWord_replicate] using hh.mul_right hs
    rw [hb, hd, B_zero_dual]
    calc
      _ = classWord g [.H i]*classWord g (dWord 0 a j i hij.symm)*
          ((classWord g [.H j])⁻¹*(classWord g [.H i]*classWord g (Sexp i (-b/a)))) := by group
      _ = _ := by rw [ht.inv_left.eq]; group

/-- Two adjacent B boxes are a D chain on reversed named edges, with only
one Fourier factor at each end. -/
theorem classWord_BB_dual_DD (a b c e : ZMod d) (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) :
    classWord g (bWord a b i j hij ++ bWord c e j k hjk) =
      classWord g [.H i]*classWord g (dWord a b j i hij.symm ++ dWord c e k j hjk.symm)*
        (classWord g [.H k])⁻¹ := by
  simp only [classWord_append, classWord_B_dual_D]
  group

/-- The same exact duality in the explicitly Pauli-erased presentation. -/
theorem symplecticClassWord_BB_dual_DD (a b c e : ZMod d) (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) :
    symplecticClassWord g (bWord a b i j hij ++ bWord c e j k hjk) =
      symplecticClassWord g [.H i]*
        symplecticClassWord g (dWord a b j i hij.symm ++ dWord c e k j hjk.symm)*
          (symplecticClassWord g [.H k])⁻¹ := by
  simpa only [map_mul, map_inv, presentedToSymplectic_classWord] using
    congrArg (presentedToSymplectic g) (classWord_BB_dual_DD g a b c e i j k hij hjk)

end QuditClifford.NormalBoxes
