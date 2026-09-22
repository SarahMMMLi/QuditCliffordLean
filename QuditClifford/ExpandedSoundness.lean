import QuditClifford.TwoWireSemantics

/-! # Exact soundness of expanded derived gates on arbitrary named wires

These statements concern the actual primitive words of `Circuit`, so their
scalar factors and their action on every idle wire are included.
-/
noncomputable section
namespace QuditClifford.Circuit
open Matrix
open scoped Kronecker
variable {d n : ℕ} [NeZero d]

@[simp] theorem onTwoWires_CZ (i j : Fin n) (h : i ≠ j) :
    onTwoWires i j (QuditClifford.CZ d) = (Gate.CZ i j h).denote d := by
  simp [QuditClifford.CZ, Gate.denote]

/-- The fully expanded controlled-addition word has the exact two-wire matrix. -/
theorem denote_CX (hd : Odd d) (i j : Fin n) (h : i ≠ j) :
    denote d (CX i j h) = onTwoWires i j (QuditClifford.CX d) := by
  rw [← CX_derived d hd]
  simp only [onTwoWires_mul i j h, onTwoWires_secondWire i j h, onTwoWires_CZ i j h,
    onWire_pow, CX, denote_cons, denote_nil, mul_one, Gate.denote]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

/-- The scalar-corrected expanded SWAP word is exactly the swap permutation. -/
theorem denote_SWAP (hd : Odd d) (i j : Fin n) (h : i ≠ j) :
    denote d (SWAP (d := d) i j h) = onTwoWires i j (QuditClifford.SWAP d) := by
  have hlayer : denote d [.CZ i j h, .H i, .H j] =
      onTwoWires i j (QuditClifford.CZ d * (QuditClifford.H d ⊗ₖ QuditClifford.H d)) := by
    rw [← firstWire_mul_secondWire]
    simp only [onTwoWires_mul i j h, onTwoWires_firstWire i j h,
      onTwoWires_secondWire i j h, onTwoWires_CZ i j h, denote_cons, denote_nil, mul_one,
      Gate.denote, mul_assoc]
  rw [SWAP, denote_append, denote_scalar, denote_power, hlayer,
    ← onTwoWires_pow i j h, swap_H_CZ_cube d hd, onTwoWires_smul]
  rw [pow_mul, scalarGenerator_pow_dimension d hd, Matrix.smul_mul, one_mul,
    smul_smul]
  have hsign : (-1 : ℂ) ^ ((d-1)/2) * (-1 : ℂ) ^ ((d-1)/2) = 1 := by
    rw [← pow_two, ← pow_mul, Nat.mul_comm, pow_mul, neg_one_sq, one_pow]
  rw [hsign, one_smul]

/-- C7 is sound for fully expanded SWAP words on arbitrary wires. -/
theorem C7_sound (hd : Odd d) (i j : Fin n) (h : i ≠ j) :
    denote d (SWAP (d := d) i j h ++ SWAP (d := d) i j h) = denote d ([] : Word n) := by
  rw [denote_append, denote_SWAP hd, ← onTwoWires_mul i j h, C7_swap_sq,
    onTwoWires_one, denote_nil]

/-- C10 is sound with the exact expanded SWAP and primitive phase gate. -/
theorem C10_sound (hd : Odd d) (i j : Fin n) (h : i ≠ j) :
    denote d (SWAP (d := d) i j h ++ [.S i]) =
      denote d ([.S j] ++ SWAP (d := d) i j h) := by
  have hh := congrArg (onTwoWires i j) (C10_swap_phase d)
  simpa only [onTwoWires_mul i j h, onTwoWires_firstWire i j h,
    onTwoWires_secondWire i j h, denote_append, denote_cons, denote_nil,
    mul_one, Gate.denote, denote_SWAP hd] using hh

/-- C11 is sound with the exact expanded SWAP and primitive Fourier gate. -/
theorem C11_sound (hd : Odd d) (i j : Fin n) (h : i ≠ j) :
    denote d (SWAP (d := d) i j h ++ [.H i]) =
      denote d ([.H j] ++ SWAP (d := d) i j h) := by
  have hh := congrArg (onTwoWires i j) (C11_swap_hadamard d)
  simpa only [onTwoWires_mul i j h, onTwoWires_firstWire i j h,
    onTwoWires_secondWire i j h, denote_append, denote_cons, denote_nil,
    mul_one, Gate.denote, denote_SWAP hd] using hh

/-- Natural powers of raw controlled addition add the corresponding multiple. -/
theorem raw_CX_pow (k : ℕ) :
    QuditClifford.CX d ^ k = basisMap (fun p : ZMod d × ZMod d =>
      (p.1, p.2 + (k : ZMod d) * p.1)) := by
  induction k with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_mul, add_zero, Prod.mk.eta]
    exact basisMap_id.symm
  | succ k ih =>
    rw [pow_succ, ih]
    simp only [QuditClifford.CX, basisMap_mul]
    apply congrArg basisMap
    funext p
    simp only [Function.comp_apply, controlledAddEquiv, Equiv.coe_fn_mk,
      Nat.cast_add, Nat.cast_one, Prod.mk.injEq, true_and]
    ring

/-- The dimension-minus-one power is the exact inverse controlled addition. -/
theorem raw_CX_pow_pred : QuditClifford.CX d ^ (d-1) = CXinv d := by
  rw [raw_CX_pow]
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hp : ((d - 1 : ℕ) : ZMod d) = -1 := by
    rw [Nat.cast_sub hd1]
    simp
  simp only [CXinv, controlledAddEquiv, Equiv.coe_fn_symm_mk, hp, neg_one_mul,
    sub_eq_add_neg]

/-- C12 is sound as a fully expanded primitive word on arbitrary wires. -/
theorem C12_sound (hd : Odd d) (i j : Fin n) (h : i ≠ j) :
    denote d (Sexp i (-1 : ZMod d) ++ Sexp j (-1 : ZMod d) ++
      power (CX i j h) (d-1) ++ [.S j] ++ CX i j h) = denote d [.CZ i j h] := by
  have hS (a : ZMod d) : QuditClifford.S d ^ a.val = phasePower d a := by
    rw [← phasePower_nat, ZMod.natCast_zmod_val]
  have hh := congrArg (onTwoWires i j) (C12_controlled_add_phase d hd)
  simp only [onTwoWires_mul i j h, onTwoWires_firstWire i j h,
    onTwoWires_secondWire i j h, onTwoWires_CZ i j h] at hh
  simpa only [denote_append, denote_Sexp, hS, denote_power, denote_CX hd,
    ← onTwoWires_pow i j h, raw_CX_pow_pred, denote_cons, denote_nil, mul_one,
    Gate.denote, mul_assoc] using hh

/-- Register permutation exchanging two named coordinates. -/
def wireSwapEquiv (i j : Fin n) : (Fin n → ZMod d) ≃ (Fin n → ZMod d) where
  toFun col k := col (Equiv.swap i j k)
  invFun col k := col (Equiv.swap i j k)
  left_inv col := by funext k; simp
  right_inv col := by funext k; simp

/-- Exact register-level basis action of the expanded SWAP. -/
theorem denote_SWAP_basisMap (hd : Odd d) (i j : Fin n) (h : i ≠ j) :
    denote d (SWAP (d := d) i j h) = basisMap (wireSwapEquiv (d := d) i j) := by
  rw [denote_SWAP hd, QuditClifford.SWAP, onTwoWires_basisMap i j h]
  apply congrArg basisMap
  funext col k
  by_cases hi : k = i
  · subst k; simp [h, wireSwapEquiv]
  by_cases hj : k = j
  · subst k; simp [wireSwapEquiv]
  simp [updateTwo_other i j k hi hj, wireSwapEquiv,
    Equiv.swap_apply_of_ne_of_ne hi hj]

/-- Exact register-level basis action of the expanded controlled addition. -/
theorem denote_CX_basisMap (hd : Odd d) (i j : Fin n) (h : i ≠ j) :
    denote d (CX i j h) = basisMap (fun col : Fin n → ZMod d =>
      Function.update col j (col j + col i)) := by
  rw [denote_CX hd, QuditClifford.CX, onTwoWires_basisMap i j h]
  apply congrArg basisMap
  funext col
  simp [updateTwo, controlledAddEquiv]

/-- The fully expanded remote phase word has exactly the distant CZ action. -/
theorem denote_CIZ (hd : Odd d) (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    denote d (CIZ (d := d) i j k hij hjk hik) = (Gate.CZ i k hik).denote d := by
  have hh := basisMap_diagonal_conjugate (wireSwapEquiv (d := d) j k)
    (fun col : Fin n → ZMod d => phase d (col i * col j))
  simpa only [CIZ, denote_append, denote_SWAP_basisMap hd, denote_cons, denote_nil,
    mul_one, Gate.denote, wireSwapEquiv, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk,
    Function.comp_def, Equiv.swap_apply_of_ne_of_ne hij hik, Equiv.swap_apply_left,
    mul_assoc] using hh

/-- C13 is sound for fully expanded SWAP words on arbitrary distinct wires. -/
theorem C13_sound (hd : Odd d) (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    denote d (SWAP (d := d) i j hij ++ SWAP (d := d) j k hjk ++ SWAP (d := d) i j hij) =
      denote d (SWAP (d := d) j k hjk ++ SWAP (d := d) i j hij ++ SWAP (d := d) j k hjk) := by
  simp only [denote_append, denote_SWAP_basisMap hd, basisMap_mul]
  apply congrArg basisMap
  funext col l
  by_cases hi : l = i
  · subst l; simp [Function.comp_apply, wireSwapEquiv, hij, hik, hjk,
      Equiv.swap_apply_of_ne_of_ne, ne_comm]
  by_cases hj : l = j
  · subst l; simp [Function.comp_apply, wireSwapEquiv, hij, hik, hjk,
      Equiv.swap_apply_of_ne_of_ne, ne_comm]
  by_cases hk : l = k
  · subst l; simp [Function.comp_apply, wireSwapEquiv, hij, hik, hjk,
      Equiv.swap_apply_of_ne_of_ne, ne_comm]
  simp [Function.comp_apply, wireSwapEquiv, Equiv.swap_apply_of_ne_of_ne hi hj,
    Equiv.swap_apply_of_ne_of_ne hj hk]

/-- C14 is sound with exact expanded SWAP words and controlled phases. -/
theorem C14_sound (hd : Odd d) (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    denote d (SWAP (d := d) j k hjk ++ SWAP (d := d) i j hij ++ [.CZ j k hjk]) =
      denote d ([.CZ i j hij] ++ SWAP (d := d) j k hjk ++ SWAP (d := d) i j hij) := by
  simp only [denote_append, denote_SWAP_basisMap hd, denote_cons, denote_nil,
    mul_one, Gate.denote]
  rw [mul_assoc (Matrix.diagonal _)]
  rw [basisMap_mul]
  symm
  apply diagonal_basisMap
  intro col
  simp [Function.comp_apply, wireSwapEquiv, hij, hik, hjk,
    Equiv.swap_apply_of_ne_of_ne, ne_comm]

/-- C15 is sound for fully expanded CX and remote-CZ words on arbitrary wires. -/
theorem C15_sound (hd : Odd d) (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    denote d ([.CZ j k hjk] ++ CX i j hij) =
      denote d (CIZ (d := d) i j k hij hjk hik ++ CX i j hij ++ [.CZ j k hjk]) := by
  simp only [denote_append, denote_CIZ hd, denote_CX_basisMap hd, denote_cons,
    denote_nil, mul_one, Gate.denote]
  ext row col
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, basisMap]
  split_ifs with heq
  · subst row
    simp [Function.update_of_ne hij, Function.update_of_ne hjk.symm,
      add_mul, mul_add, mul_comm, mul_left_comm, mul_assoc]
  · simp

/-- The remaining exact denotation obligation for the expanded T1 multiplier.
This is a proposition, not an axiom or an asserted theorem. -/
def MultiplierWordSound (d n : ℕ) [NeZero d] : Prop :=
  ∀ (i : Fin n) (a : (ZMod d)ˣ),
    denote d (multiplier i a) = onWire i (QuditClifford.multiplier d a)

omit [NeZero d] in
theorem onWire_smul (i : Fin n) (c : ℂ) (A : QuditMatrix d) :
    onWire i (c • A) = c • onWire i A := by
  classical
  ext row col
  simp only [onWire, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

/-- C2 follows from the exact T1 multiplier denotation, including its sign. -/
theorem C2_sound_of_multiplier (hd : Odd d) (hM : MultiplierWordSound d n) (i : Fin n) :
    denote d [.H i, .H i] =
      denote d (scalar (d * ((d-1)/2)) ++ multiplier (d := d) i (-1)) := by
  simp only [denote_append, denote_scalar, hM i (-1), denote_cons, denote_nil,
    mul_one, Gate.denote, ← onWire_mul, C2_hadamard_square d hd, onWire_smul,
    pow_mul, scalarGenerator_pow_dimension d hd, Matrix.smul_mul, one_mul]

/-- C3 follows from the exact T1 multiplier denotation. -/
theorem C3_sound_of_multiplier (hM : MultiplierWordSound d n)
    (i : Fin n) (a : (ZMod d)ˣ) (k : ℕ) :
    denote d (power (multiplier i a) k) = denote d (multiplier i (a ^ k)) := by
  rw [denote_power, hM, hM, ← onWire_pow, multiplier_pow]

/-- C4 follows from T1; the reciprocal coefficient matches the paper exactly. -/
theorem C4_sound_of_multiplier (hd : Odd d) (hM : MultiplierWordSound d n)
    (i : Fin n) (a : (ZMod d)ˣ) :
    denote d (multiplier i a ++ [.S i]) =
      denote d (Zexp i ((1-(a : ZMod d)) * (2*(a : ZMod d)^2)⁻¹) ++
        Sexp i ((↑a⁻¹ : ZMod d)^2) ++ multiplier i a) := by
  have hinv : (2 * (a : ZMod d)^2)⁻¹ = half d * (↑a⁻¹ : ZMod d)^2 := by
    apply ZMod.inv_eq_of_mul_eq_one
    calc
      2 * (a : ZMod d)^2 * (half d * (↑a⁻¹ : ZMod d)^2) =
        (2 * half d) * ((a : ZMod d) * (↑a⁻¹ : ZMod d))^2 := by ring
      _ = 1 := by rw [two_mul_half d hd]; simp
  have hS (b : ZMod d) : QuditClifford.S d ^ b.val = phasePower d b := by
    rw [← phasePower_nat, ZMod.natCast_zmod_val]
  simp only [denote_append, hM i a, denote_cons, denote_nil, mul_one, Gate.denote,
    denote_Zexp hd, denote_Sexp, hS, ← onWire_mul, hinv]
  apply congrArg (onWire i)
  simpa only [mul_assoc] using C4_multiplier_phase d a

/-- C9 follows from the exact T1 multiplier denotation on arbitrary wires. -/
theorem C9_sound_of_multiplier (hM : MultiplierWordSound d n)
    (i j : Fin n) (h : i ≠ j) (a : (ZMod d)ˣ) :
    denote d ([.CZ i j h] ++ multiplier i a) =
      denote d (multiplier i a ++ List.replicate (a : ZMod d).val (.CZ i j h)) := by
  have hp : CZPower d (a : ZMod d) = QuditClifford.CZ d ^ (a : ZMod d).val := by
    rw [← CZPower_nat, ZMod.natCast_zmod_val]
  have hh := congrArg (onTwoWires i j) (C9_controlled_multiplier d a)
  simpa only [onTwoWires_mul i j h, onTwoWires_firstWire i j h,
    onTwoWires_CZ i j h, hp, onTwoWires_pow i j h, denote_append,
    denote_cons, denote_nil, mul_one, hM i a, denote_replicate] using hh

/-- Every expanded Figure 1 rule is sound once the remaining exact T1
multiplier denotation has been supplied. No Gauss-sum evaluation is assumed
implicitly; the single remaining obligation is the visible hypothesis `hM`. -/
theorem figure1_rule_sound_of_multiplier (hd : Odd d) (hM : MultiplierWordSound d n)
    (g : (ZMod d)ˣ) {u v : Word n} (hr : Figure1Rule g u v) : denote d u = denote d v := by
  cases hr with
  | C0 => exact C0_sound
  | C1 i => exact C1_sound i
  | C2 i => exact C2_sound_of_multiplier hd hM i
  | C3 i k => exact C3_sound_of_multiplier hM i g k.val
  | C4 i => exact C4_sound_of_multiplier hd hM i g
  | C5 i => exact C5_sound hd i
  | C6 i j h => exact C6_sound i j h
  | C7 i j h => exact C7_sound hd i j h
  | C8 i j h => exact C8_sound i j h
  | C9 i j h => exact C9_sound_of_multiplier hM i j h g
  | C10 i j h => exact C10_sound hd i j h
  | C11 i j h => exact C11_sound hd i j h
  | C12 i j h => exact C12_sound hd i j h
  | C13 i j k hij hjk hik => exact C13_sound hd i j k hij hjk hik
  | C14 i j k hij hjk hik => exact C14_sound hd i j k hij hjk hik
  | C15 i j k hij hjk hik => exact C15_sound hd i j k hij hjk hik

/-- Full exact soundness under the explicit remaining T1 obligation. This
conditional theorem is separate from the unproved completeness direction. -/
theorem figure1_sound_of_multiplier (hd : Odd d) (hM : MultiplierWordSound d n)
    (g : (ZMod d)ˣ) : Figure1Sound (n := n) g := by
  intro u v huv
  apply Presentation.sound_derives (R := Rules g) (interpret := Gate.denote d) ?_ huv
  intro a b hr
  rcases hr with hr | hr
  · exact structural_sound hr
  · exact figure1_rule_sound_of_multiplier hd hM g hr

end QuditClifford.Circuit
