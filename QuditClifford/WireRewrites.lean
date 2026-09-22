import QuditClifford.DerivedPauliRewrites

/-! # Exact wire transport in the Figure 1 presentation

SWAP symmetry follows from its literal expansion and structural wire rules.
C10 and C11 therefore transport S and H in either direction. Closure under
products and powers transports the fully expanded X and Z words, including
all their inverse-S factors. These are contextual derivations in the actual
presentation; matrix soundness is never used in the reverse direction.
-/
noncomputable section
namespace QuditClifford.Circuit
variable {d n : ℕ} [NeZero d]

/-- Word transport is semiconjugacy in the syntactic quotient. -/
theorem classWord_semiconj_iff (g : (ZMod d)ˣ) (s u v : Word n) :
    SemiconjBy (classWord g s) (classWord g u) (classWord g v) ↔
      Derives g (s ++ u) (v ++ s) :=
  classWord_eq_iff_derives g (s ++ u) (v ++ s)

/-- Contextual transport is closed under concatenating the transported words. -/
theorem derives_transport_append (g : (ZMod d)ˣ) {s u v u' v' : Word n}
    (h : Derives g (s ++ u) (v ++ s))
    (h' : Derives g (s ++ u') (v' ++ s)) :
    Derives g (s ++ (u ++ u')) ((v ++ v') ++ s) := by
  apply (classWord_semiconj_iff g _ _ _).mp
  exact ((classWord_semiconj_iff g _ _ _).mpr h).mul_right
    ((classWord_semiconj_iff g _ _ _).mpr h')

/-- Contextual transport is closed under arbitrary nonnegative powers. -/
theorem derives_transport_power (g : (ZMod d)ˣ) {s u v : Word n}
    (h : Derives g (s ++ u) (v ++ s)) (k : ℕ) :
    Derives g (s ++ power u k) (power v k ++ s) := by
  apply (classWord_semiconj_iff g _ _ _).mp
  simpa only [classWord_power] using ((classWord_semiconj_iff g _ _ _).mpr h).pow_right k

/-- The two orientations of the expanded SWAP are structurally equal. -/
theorem derives_SWAP_symmetry (g : (ZMod d)ˣ) (i j : Fin n) (hij : i ≠ j) :
    Derives g (SWAP (d := d) i j hij) (SWAP (d := d) j i hij.symm) := by
  have hCZ : Derives g [.CZ i j hij] [.CZ j i hij.symm] :=
    .rule (Or.inl (Structural.CZ_symmetry i j hij))
  have hH : Derives g [.H i, .H j] [.H j, .H i] :=
    .rule (Or.inl (Structural.disjoint (.H i) (.H j) (by simp [Gate.support, hij, hij.symm])))
  exact (derives_power g (hCZ.append hH) 3).append_left (scalar (d * ((d-1)/2)))

/-- C10 transports S from the first wire of an expanded SWAP to the second. -/
theorem derives_SWAP_S_left (g : (ZMod d)ˣ) (i j : Fin n) (hij : i ≠ j) :
    Derives g (SWAP (d := d) i j hij ++ [.S i])
      ([.S j] ++ SWAP (d := d) i j hij) :=
  .rule (Or.inr (Figure1Rule.C10 i j hij))

/-- C11 transports H from the first wire of an expanded SWAP to the second. -/
theorem derives_SWAP_H_left (g : (ZMod d)ˣ) (i j : Fin n) (hij : i ≠ j) :
    Derives g (SWAP (d := d) i j hij ++ [.H i])
      ([.H j] ++ SWAP (d := d) i j hij) :=
  .rule (Or.inr (Figure1Rule.C11 i j hij))

/-- S transport in the other direction uses only structural SWAP symmetry and C10. -/
theorem derives_SWAP_S_right (g : (ZMod d)ˣ) (i j : Fin n) (hij : i ≠ j) :
    Derives g (SWAP (d := d) i j hij ++ [.S j])
      ([.S i] ++ SWAP (d := d) i j hij) := by
  exact ((derives_SWAP_symmetry g i j hij).append_right [.S j]).trans
    ((derives_SWAP_S_left g j i hij.symm).trans
      ((derives_SWAP_symmetry g i j hij).symm.append_left [.S i]))

/-- H transport in the other direction uses only structural SWAP symmetry and C11. -/
theorem derives_SWAP_H_right (g : (ZMod d)ˣ) (i j : Fin n) (hij : i ≠ j) :
    Derives g (SWAP (d := d) i j hij ++ [.H j])
      ([.H i] ++ SWAP (d := d) i j hij) := by
  exact ((derives_SWAP_symmetry g i j hij).append_right [.H j]).trans
    ((derives_SWAP_H_left g j i hij.symm).trans
      ((derives_SWAP_symmetry g i j hij).symm.append_left [.H i]))

/-- SWAP transports every residue power of S, including the displayed inverse. -/
theorem derives_SWAP_Sexp_left (g : (ZMod d)ˣ) (i j : Fin n) (hij : i ≠ j)
    (a : ZMod d) :
    Derives g (SWAP (d := d) i j hij ++ Sexp i a)
      (Sexp j a ++ SWAP (d := d) i j hij) := by
  apply (classWord_semiconj_iff g _ _ _).mp
  simpa only [Sexp, classWord_replicate] using
    ((classWord_semiconj_iff g _ _ _).mpr (derives_SWAP_S_left g i j hij)).pow_right a.val

/-- Exact transport of T2's fully expanded X word. -/
theorem derives_SWAP_X_left (g : (ZMod d)ˣ) (i j : Fin n) (hij : i ≠ j) :
    Derives g (SWAP (d := d) i j hij ++ X (d := d) i)
      (X (d := d) j ++ SWAP (d := d) i j hij) := by
  have hH := (classWord_semiconj_iff g _ _ _).mpr (derives_SWAP_H_left g i j hij)
  have hS := (classWord_semiconj_iff g _ _ _).mpr (derives_SWAP_S_left g i j hij)
  have hSi := (classWord_semiconj_iff g _ _ _).mpr (derives_SWAP_Sexp_left g i j hij (-1))
  apply (classWord_semiconj_iff g _ _ _).mp
  exact ((((hH.mul_right hS).mul_right hH).mul_right hH).mul_right hSi).mul_right hH

/-- Exact transport of T3's fully expanded Z word. -/
theorem derives_SWAP_Z_left (g : (ZMod d)ˣ) (i j : Fin n) (hij : i ≠ j) :
    Derives g (SWAP (d := d) i j hij ++ Z (d := d) i)
      (Z (d := d) j ++ SWAP (d := d) i j hij) := by
  have hH := (classWord_semiconj_iff g _ _ _).mpr (derives_SWAP_H_left g i j hij)
  have hS := (classWord_semiconj_iff g _ _ _).mpr (derives_SWAP_S_left g i j hij)
  have hSi := (classWord_semiconj_iff g _ _ _).mpr (derives_SWAP_Sexp_left g i j hij (-1))
  apply (classWord_semiconj_iff g _ _ _).mp
  exact ((((hH.mul_right hH).mul_right hS).mul_right hH).mul_right hH).mul_right hSi

/-- Exact transport of X in the reverse wire direction. -/
theorem derives_SWAP_X_right (g : (ZMod d)ˣ) (i j : Fin n) (hij : i ≠ j) :
    Derives g (SWAP (d := d) i j hij ++ X (d := d) j)
      (X (d := d) i ++ SWAP (d := d) i j hij) := by
  exact ((derives_SWAP_symmetry g i j hij).append_right (X j)).trans
    ((derives_SWAP_X_left g j i hij.symm).trans
      ((derives_SWAP_symmetry g i j hij).symm.append_left (X i)))

/-- Exact transport of Z in the reverse wire direction. -/
theorem derives_SWAP_Z_right (g : (ZMod d)ˣ) (i j : Fin n) (hij : i ≠ j) :
    Derives g (SWAP (d := d) i j hij ++ Z (d := d) j)
      (Z (d := d) i ++ SWAP (d := d) i j hij) := by
  exact ((derives_SWAP_symmetry g i j hij).append_right (Z j)).trans
    ((derives_SWAP_Z_left g j i hij.symm).trans
      ((derives_SWAP_symmetry g i j hij).symm.append_left (Z i)))

/-- Residue powers of the exact expanded X word transport with no added scalar. -/
theorem derives_SWAP_Xexp_left (g : (ZMod d)ˣ) (i j : Fin n) (hij : i ≠ j)
    (a : ZMod d) :
    Derives g (SWAP (d := d) i j hij ++ Xexp i a)
      (Xexp j a ++ SWAP (d := d) i j hij) :=
  derives_transport_power g (derives_SWAP_X_left g i j hij) a.val

/-- Residue powers of the exact expanded Z word transport with no added scalar. -/
theorem derives_SWAP_Zexp_left (g : (ZMod d)ˣ) (i j : Fin n) (hij : i ≠ j)
    (a : ZMod d) :
    Derives g (SWAP (d := d) i j hij ++ Zexp i a)
      (Zexp j a ++ SWAP (d := d) i j hij) :=
  derives_transport_power g (derives_SWAP_Z_left g i j hij) a.val

/-- Residue X powers transport in the other wire direction as well. -/
theorem derives_SWAP_Xexp_right (g : (ZMod d)ˣ) (i j : Fin n) (hij : i ≠ j)
    (a : ZMod d) :
    Derives g (SWAP (d := d) i j hij ++ Xexp j a)
      (Xexp i a ++ SWAP (d := d) i j hij) :=
  derives_transport_power g (derives_SWAP_X_right g i j hij) a.val

/-- Residue Z powers transport in the other wire direction as well. -/
theorem derives_SWAP_Zexp_right (g : (ZMod d)ˣ) (i j : Fin n) (hij : i ≠ j)
    (a : ZMod d) :
    Derives g (SWAP (d := d) i j hij ++ Zexp j a)
      (Zexp i a ++ SWAP (d := d) i j hij) :=
  derives_transport_power g (derives_SWAP_Z_right g i j hij) a.val

/-- T1's entire expanded multiplier, including both exact scalar factors,
transports through SWAP without any scalar correction. -/
theorem derives_SWAP_multiplier_left (g : (ZMod d)ˣ) (i j : Fin n) (hij : i ≠ j)
    (a : (ZMod d)ˣ) :
    Derives g (SWAP (d := d) i j hij ++ multiplier i a)
      (multiplier j a ++ SWAP (d := d) i j hij) := by
  have hscalar (k : ℕ) := (classWord_semiconj_iff g _ _ _).mpr
    (derives_scalar_commute g k (SWAP (d := d) i j hij)).symm
  have hZ (b : ZMod d) := (classWord_semiconj_iff g _ _ _).mpr
    (derives_SWAP_Zexp_left g i j hij b)
  have hX (b : ZMod d) := (classWord_semiconj_iff g _ _ _).mpr
    (derives_SWAP_Xexp_left g i j hij b)
  have hS (b : ZMod d) := (classWord_semiconj_iff g _ _ _).mpr
    (derives_SWAP_Sexp_left g i j hij b)
  have hH := (classWord_semiconj_iff g _ _ _).mpr (derives_SWAP_H_left g i j hij)
  apply (classWord_semiconj_iff g _ _ _).mp
  exact ((((((((hscalar _).mul_right (hscalar _)).mul_right (hZ _)).mul_right
    (hX _)).mul_right (hS _)).mul_right hH).mul_right (hS _)).mul_right hH).mul_right
      (hS _) |>.mul_right hH

/-- C7 converts any established SWAP transport equation into conjugation. -/
theorem derives_SWAP_conjugate (g : (ZMod d)ˣ) (i j : Fin n) (hij : i ≠ j)
    {u v : Word n} (h : Derives g (SWAP (d := d) i j hij ++ u)
      (v ++ SWAP (d := d) i j hij)) :
    Derives g (SWAP (d := d) i j hij ++ u ++ SWAP (d := d) i j hij) v := by
  have hh : Derives g (SWAP (d := d) i j hij ++ SWAP (d := d) i j hij) [] :=
    .rule (Or.inr (Figure1Rule.C7 i j hij))
  exact (h.append_right (SWAP (d := d) i j hij)).trans (by
    simpa only [List.append_assoc, List.append_nil] using hh.append_left v)

variable [Fact d.Prime]

/-- Inverses also transport, using the group structure proved from Figure 1. -/
theorem derives_transport_inverseWord (hd : Odd d) (g : (ZMod d)ˣ)
    (hg : orderOf g = d-1) {s u v : Word n}
    (h : Derives g (s ++ u) (v ++ s)) :
    Derives g (s ++ inverseWord d u) (inverseWord d v ++ s) := by
  letI : Fact (Odd d) := ⟨hd⟩
  letI : Fact (orderOf g = d-1) := ⟨hg⟩
  apply (classWord_semiconj_iff g _ _ _).mp
  simpa only [classWord_inverseWord] using
    ((classWord_semiconj_iff g _ _ _).mpr h).inv_right

/-- C7 identifies the inverse of the expanded SWAP inside the syntactic group. -/
theorem classWord_SWAP_inv (hd : Odd d) (g : (ZMod d)ˣ) (hg : orderOf g = d-1)
    (i j : Fin n) (hij : i ≠ j) :
    letI : Fact (Odd d) := ⟨hd⟩
    letI : Fact (orderOf g = d-1) := ⟨hg⟩
    (classWord g (SWAP (d := d) i j hij))⁻¹ = classWord g (SWAP (d := d) i j hij) := by
  letI : Fact (Odd d) := ⟨hd⟩
  letI : Fact (orderOf g = d-1) := ⟨hg⟩
  apply inv_eq_of_mul_eq_one_right
  exact (classWord_eq_iff_derives g _ _).mpr (.rule (Or.inr (Figure1Rule.C7 i j hij)))

end QuditClifford.Circuit
