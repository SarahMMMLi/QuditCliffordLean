import QuditClifford.BoxDuality
import QuditClifford.SymplecticThreeWireDD
import QuditClifford.SymplecticThreeWireDDNonzero

/-!
# Three-wire B-B controlled-phase rewrites by exact Fourier duality

The explicit local B/D duality transfers the D-D rewrite families to B-B
on reversed named wires. This transport concerns generated syntactic
congruences only; no equality of matrices is used to manufacture a rewrite.
-/

noncomputable section
namespace QuditClifford.NormalBoxes
open Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

/-- A concrete D-D derivation on reversed edges transfers to B-B whenever
its dirty output is supported away from the first wire. -/
theorem derives_BB_CZ_of_DD (a b c e a' b' c' e' : ZMod d)
    (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (dirty : Word n)
    (hdirt : Commute (classWord g [.H i]) (classWord g dirty))
    (hDD : Derives g
      (dWord a b j i hij.symm ++ dWord c e k j hjk.symm ++ [.CZ j i hij.symm])
      (dirty ++ dWord a' b' j i hij.symm ++ dWord c' e' k j hjk.symm)) :
    Derives g (bWord a b i j hij ++ bWord c e j k hjk ++ [.CZ i j hij])
      (dirty ++ bWord a' b' i j hij ++ bWord c' e' j k hjk) := by
  let Hi := classWord g [.H i]
  let Hk := classWord g [.H k]
  let C := classWord g [.CZ i j hij]
  let D := classWord g (dWord a b j i hij.symm ++ dWord c e k j hjk.symm)
  let D' := classWord g (dWord a' b' j i hij.symm ++ dWord c' e' k j hjk.symm)
  let B := classWord g (bWord a b i j hij ++ bWord c e j k hjk)
  let B' := classWord g (bWord a' b' i j hij ++ bWord c' e' j k hjk)
  let Q := classWord g dirty
  have hB : B=Hi*D*Hk⁻¹ := classWord_BB_dual_DD g a b c e i j k hij hjk
  have hB' : B'=Hi*D'*Hk⁻¹ := classWord_BB_dual_DD g a' b' c' e' i j k hij hjk
  have hC : Commute Hk C := by
    exact classWord_disjoint g (.H k) (.CZ i j hij)
      (by simp [Gate.support, hik, hjk, hik.symm, hjk.symm])
  have hD : D*C=Q*D' := by
    have h := (classWord_eq_iff_derives g _ _).mpr hDD
    have hcz := classWord_CZ_symmetry g i j hij
    simp only [classWord_append] at h
    rw [← hcz] at h
    simpa only [D, D', Q, C, classWord_append, mul_assoc] using h
  have he : B*C=Q*B' := by
    rw [hB, hB']
    calc
      _ = Hi*D*(Hk⁻¹*C) := by group
      _ = Hi*D*(C*Hk⁻¹) := by rw [hC.inv_left.eq]
      _ = Hi*(D*C)*Hk⁻¹ := by group
      _ = Hi*(Q*D')*Hk⁻¹ := by rw [hD]
      _ = (Hi*Q)*D'*Hk⁻¹ := by group
      _ = _ := by rw [hdirt.eq]; dsimp [Hi, Q]; group
  apply (classWord_eq_iff_derives g _ _).mp
  simpa only [B, B', Q, C, classWord_append, mul_assoc] using he

/-- The zero/zero B-B branch is obtained from the exact D-D zero/zero rule. -/
theorem derives_BB_CZ_zero_zero (b e : ZMod d) (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    Derives g (bWord 0 b i j hij ++ bWord 0 e j k hjk ++ [.CZ i j hij])
      ([.CZ k j hjk.symm] ++ bWord 0 b i j hij ++ bWord 0 e j k hjk) := by
  apply derives_BB_CZ_of_DD g 0 b 0 e 0 b 0 e i j k hij hjk hik [.CZ k j hjk.symm]
  · exact (classWord_disjoint g (.H i) (.CZ k j hjk.symm)
        (by simp [Gate.support, hik, hij, hik.symm, hij.symm])).eq
  · exact (derives_DD_CZ_zero_zero g b e k j i hjk.symm hij.symm hik.symm)

/-- The zero/nonzero B-B branch transfers the exact D-D branch under Fourier duality. -/
theorem derives_BB_CZ_zero_nonzero (b c e : ZMod d) (hc : c ≠ 0)
    (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    Derives g (bWord 0 b i j hij ++ bWord c e j k hjk ++ [.CZ i j hij])
      ([.H k, .CZ k j hjk.symm] ++ inverseWord (d := d) [.H k] ++
        bWord 0 (b-c) i j hij ++ bWord c e j k hjk) := by
  apply derives_BB_CZ_of_DD g 0 b c e 0 (b-c) c e i j k hij hjk hik
    (([.H k, .CZ k j hjk.symm] : Word n) ++ inverseWord (d := d) [.H k])
  · have hh : Commute (classWord g [.H i]) (classWord g [.H k]) :=
      (classWord_disjoint g (.H i) (.H k) (by simpa [Gate.support] using hik.symm)).eq
    have hq : Commute (classWord g [.H i])
        (classWord g [.CZ k j hjk.symm]) :=
      (classWord_disjoint g (.H i) (.CZ k j hjk.symm)
          (by simp [Gate.support, hik, hij, hik.symm, hij.symm])).eq
    have h := (hh.mul_right hq).mul_right hh.inv_right
    simpa only [classWord_append, classWord_inverseWord] using h
  · exact (derives_DD_CZ_zero_nonzero g b c e hc k j i hjk.symm hij.symm hik.symm)

/-- The nonzero/zero B-B branch comes from the exact permuted D-D branch. -/
theorem derives_BB_CZ_nonzero_zero (a b e : ZMod d) (ha : a ≠ 0)
    (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    Derives g (bWord a b i j hij ++ bWord 0 e j k hjk ++ [.CZ i j hij])
      ([.H j, .CZ k j hjk.symm] ++ inverseWord (d := d) [.H j] ++
        bWord a b i j hij ++ bWord 0 (e-a) j k hjk) := by
  apply derives_BB_CZ_of_DD g a b 0 e a b 0 (e-a) i j k hij hjk hik
    (([.H j, .CZ k j hjk.symm] : Word n) ++ inverseWord (d := d) [.H j])
  · have hh : Commute (classWord g [.H i]) (classWord g [.H j]) :=
      (classWord_disjoint g (.H i) (.H j) (by simpa [Gate.support] using hij.symm)).eq
    have hq : Commute (classWord g [.H i])
        (classWord g [.CZ k j hjk.symm]) :=
      (classWord_disjoint g (.H i) (.CZ k j hjk.symm)
          (by simp [Gate.support, hik, hij, hik.symm, hij.symm])).eq
    have h := (hh.mul_right hq).mul_right hh.inv_right
    simpa only [classWord_append, classWord_inverseWord] using h
  · exact (derives_DD_CZ_nonzero_zero g a b e ha k j i hjk.symm hij.symm hik.symm)

/-- A concrete D-D derivation on reversed edges transfers to B-B whenever
its dirty output is supported away from the first wire. -/
theorem symplecticDerives_BB_CZ_of_DD (a b c e a' b' c' e' : ZMod d)
    (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (dirty : Word n)
    (hdirt : Commute (symplecticClassWord g [.H i]) (symplecticClassWord g dirty))
    (hDD : SymplecticDerives g
      (dWord a b j i hij.symm ++ dWord c e k j hjk.symm ++ [.CZ j i hij.symm])
      (dirty ++ dWord a' b' j i hij.symm ++ dWord c' e' k j hjk.symm)) :
    SymplecticDerives g (bWord a b i j hij ++ bWord c e j k hjk ++ [.CZ i j hij])
      (dirty ++ bWord a' b' i j hij ++ bWord c' e' j k hjk) := by
  let Hi := symplecticClassWord g [.H i]
  let Hk := symplecticClassWord g [.H k]
  let C := symplecticClassWord g [.CZ i j hij]
  let D := symplecticClassWord g (dWord a b j i hij.symm ++ dWord c e k j hjk.symm)
  let D' := symplecticClassWord g (dWord a' b' j i hij.symm ++ dWord c' e' k j hjk.symm)
  let B := symplecticClassWord g (bWord a b i j hij ++ bWord c e j k hjk)
  let B' := symplecticClassWord g (bWord a' b' i j hij ++ bWord c' e' j k hjk)
  let Q := symplecticClassWord g dirty
  have hB : B=Hi*D*Hk⁻¹ := symplecticClassWord_BB_dual_DD g a b c e i j k hij hjk
  have hB' : B'=Hi*D'*Hk⁻¹ := symplecticClassWord_BB_dual_DD g a' b' c' e' i j k hij hjk
  have hC : Commute Hk C := by
    exact congrArg (presentedToSymplectic g)
      (classWord_disjoint g (.H k) (.CZ i j hij)
        (by simp [Gate.support, hik, hjk, hik.symm, hjk.symm])).eq
  have hD : D*C=Q*D' := by
    have h := (symplecticClassWord_eq_iff_derives g _ _).mpr hDD
    have hcz := congrArg (presentedToSymplectic g) (classWord_CZ_symmetry g i j hij)
    simp only [presentedToSymplectic_classWord] at hcz
    simp only [symplecticClassWord_append] at h
    rw [← hcz] at h
    simpa only [D, D', Q, C, symplecticClassWord_append, mul_assoc] using h
  have he : B*C=Q*B' := by
    rw [hB, hB']
    calc
      _ = Hi*D*(Hk⁻¹*C) := by group
      _ = Hi*D*(C*Hk⁻¹) := by rw [hC.inv_left.eq]
      _ = Hi*(D*C)*Hk⁻¹ := by group
      _ = Hi*(Q*D')*Hk⁻¹ := by rw [hD]
      _ = (Hi*Q)*D'*Hk⁻¹ := by group
      _ = _ := by rw [hdirt.eq]; dsimp [Hi, Q]; group
  apply (symplecticClassWord_eq_iff_derives g _ _).mp
  simpa only [B, B', Q, C, symplecticClassWord_append, mul_assoc] using he

/-- The zero/zero B-B branch is obtained from the exact D-D zero/zero rule. -/
theorem symplecticDerives_BB_CZ_zero_zero (b e : ZMod d) (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    SymplecticDerives g (bWord 0 b i j hij ++ bWord 0 e j k hjk ++ [.CZ i j hij])
      ([.CZ k j hjk.symm] ++ bWord 0 b i j hij ++ bWord 0 e j k hjk) := by
  exact derives_symplectic g (derives_BB_CZ_zero_zero g b e i j k hij hjk hik)

/-- The zero/nonzero B-B branch transfers the exact D-D branch under Fourier duality. -/
theorem symplecticDerives_BB_CZ_zero_nonzero (b c e : ZMod d) (hc : c ≠ 0)
    (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    SymplecticDerives g (bWord 0 b i j hij ++ bWord c e j k hjk ++ [.CZ i j hij])
      ([.H k, .CZ k j hjk.symm] ++ inverseWord (d := d) [.H k] ++
        bWord 0 (b-c) i j hij ++ bWord c e j k hjk) := by
  exact derives_symplectic g (derives_BB_CZ_zero_nonzero g b c e hc i j k hij hjk hik)

/-- The nonzero/zero B-B branch comes from the exact permuted D-D branch. -/
theorem symplecticDerives_BB_CZ_nonzero_zero (a b e : ZMod d) (ha : a ≠ 0)
    (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    SymplecticDerives g (bWord a b i j hij ++ bWord 0 e j k hjk ++ [.CZ i j hij])
      ([.H j, .CZ k j hjk.symm] ++ inverseWord (d := d) [.H j] ++
        bWord a b i j hij ++ bWord 0 (e-a) j k hjk) := by
  exact derives_symplectic g (derives_BB_CZ_nonzero_zero g a b e ha i j k hij hjk hik)

/-- The two nonzero B-B pivots transfer the proved quadratic D-D case. -/
theorem symplecticDerives_BB_CZ_nonzero_nonzero (a b c e : ZMod d) (ha : a ≠ 0) (hc : c ≠ 0)
    (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    SymplecticDerives g (bWord a b i j hij ++ bWord c e j k hjk ++ [.CZ i j hij])
      ([.H j, .H k, .CZ k j hjk.symm] ++ Sexp j (-c/a) ++ inverseWord d [.H j] ++
        Sexp k (-a/c) ++ inverseWord d [.H k] ++
          bWord a (b-c) i j hij ++ bWord c (e-a) j k hjk) := by
  apply symplecticDerives_BB_CZ_of_DD g a b c e a (b-c) c (e-a) i j k hij hjk hik
    (([.H j, .H k, .CZ k j hjk.symm] : Word n) ++ Sexp j (-c/a) ++ inverseWord d [.H j] ++
      Sexp k (-a/c) ++ inverseWord d [.H k])
  · have hhj : Commute (symplecticClassWord g [.H i]) (symplecticClassWord g [.H j]) :=
      congrArg (presentedToSymplectic g)
        (classWord_disjoint g (.H i) (.H j) (by simpa [Gate.support] using hij.symm)).eq
    have hhk : Commute (symplecticClassWord g [.H i]) (symplecticClassWord g [.H k]) :=
      congrArg (presentedToSymplectic g)
        (classWord_disjoint g (.H i) (.H k) (by simpa [Gate.support] using hik.symm)).eq
    have hq : Commute (symplecticClassWord g [.H i])
        (symplecticClassWord g [.CZ k j hjk.symm]) :=
      congrArg (presentedToSymplectic g)
        (classWord_disjoint g (.H i) (.CZ k j hjk.symm)
          (by simp [Gate.support, hik, hij, hik.symm, hij.symm])).eq
    have hsj : Commute (symplecticClassWord g [.H i]) (symplecticClassWord g (Sexp j (-c/a))) := by
      have h := congrArg (presentedToSymplectic g)
        ((classWord_disjoint g (.H i) (.S j)
          (by simpa [Gate.support] using hij.symm)).pow_right (-c/a).val).eq
      simpa only [map_mul, map_pow, presentedToSymplectic_classWord, Sexp,
        symplecticClassWord_replicate] using h
    have hsk : Commute (symplecticClassWord g [.H i]) (symplecticClassWord g (Sexp k (-a/c))) := by
      have h := congrArg (presentedToSymplectic g)
        ((classWord_disjoint g (.H i) (.S k)
          (by simpa [Gate.support] using hik.symm)).pow_right (-a/c).val).eq
      simpa only [map_mul, map_pow, presentedToSymplectic_classWord, Sexp,
        symplecticClassWord_replicate] using h
    have h := (((((hhj.mul_right hhk).mul_right hq).mul_right hsj).mul_right hhj.inv_right).mul_right hsk).mul_right hhk.inv_right
    simpa only [symplecticClassWord_append, symplecticClassWord_inverseWord, mul_assoc] using h
  · exact symplectic_DD_CZ_nonzero_nonzero g a b c e ha hc k j i hjk.symm hij.symm hik.symm

end QuditClifford.NormalBoxes
