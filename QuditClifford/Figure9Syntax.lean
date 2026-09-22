import QuditClifford.AdjacentNormalCircuit

/-!
# The corrected eighteen equations of Figure 9

The source alphabet is H, S, and canonical adjacent CZ. Scalars in derived
macros are removed syntactically; expanded X and Z remain genuine words.
C9 uses the corrected exponent g in the PDF of 22 September 2026.
Lists use matrix order, reversing the temporal diagrams in the source.
-/
noncomputable section
namespace QuditClifford.Circuit
variable {d n : ℕ}

/-- Remove only primitive scalar letters, retaining every expanded Pauli gate. -/
def eraseScalar : Word n → Word n
  | [] => []
  | .scalar :: w => eraseScalar w
  | .H i :: w => .H i :: eraseScalar w
  | .S i :: w => .S i :: eraseScalar w
  | .CZ i j h :: w => .CZ i j h :: eraseScalar w

@[simp] theorem eraseScalar_nil : eraseScalar ([] : Word n) = [] := rfl
@[simp] theorem eraseScalar_scalar_cons (w : Word n) :
    eraseScalar (.scalar :: w) = eraseScalar w := rfl
@[simp] theorem eraseScalar_H_cons (i : Fin n) (w : Word n) :
    eraseScalar (.H i :: w) = .H i :: eraseScalar w := rfl
@[simp] theorem eraseScalar_S_cons (i : Fin n) (w : Word n) :
    eraseScalar (.S i :: w) = .S i :: eraseScalar w := rfl
@[simp] theorem eraseScalar_CZ_cons (i j : Fin n) (h : i ≠ j) (w : Word n) :
    eraseScalar (.CZ i j h :: w) = .CZ i j h :: eraseScalar w := rfl

@[simp] theorem eraseScalar_append (u v : Word n) :
    eraseScalar (u ++ v) = eraseScalar u ++ eraseScalar v := by
  induction u with
  | nil => rfl
  | cons a w ih => cases a <;> simp [ih]

@[simp] theorem eraseScalar_idempotent (w : Word n) :
    eraseScalar (eraseScalar w) = eraseScalar w := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp [ih]

@[simp] theorem eraseScalar_replicate (k : ℕ) (a : Gate n) :
    eraseScalar (List.replicate k a) = power (eraseScalar [a]) k := by
  induction k with
  | zero => rfl
  | succ k ih => cases a <;> simp [power, List.replicate_succ] at * <;> exact ih

@[simp] theorem eraseScalar_power (w : Word n) (k : ℕ) :
    eraseScalar (power w k) = power (eraseScalar w) k := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [power, List.replicate_succ, List.flatten_cons,
      eraseScalar_append] using congrArg (eraseScalar w ++ ·) ih

@[simp] theorem power_singleton (a : Gate n) (k : ℕ) : power [a] k = List.replicate k a := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [power, List.replicate_succ, List.flatten_cons,
      List.cons_append, List.nil_append] using congrArg (a :: ·) ih

@[simp] theorem power_nil (k : ℕ) : power ([] : Word n) k = [] := by simp [power]
@[simp] theorem eraseScalar_scalar (k : ℕ) : eraseScalar (scalar (n := n) k) = [] := by
  simp [scalar]
@[simp] theorem eraseScalar_omegaPower (a : ZMod d) :
    eraseScalar (omegaPower (n := n) a) = [] := by simp [omegaPower]
@[simp] theorem eraseScalar_Sexp (i : Fin n) (a : ZMod d) :
    eraseScalar (Sexp i a) = Sexp i a := by simp [Sexp]
@[simp] theorem eraseScalar_X (i : Fin n) : eraseScalar (X (d := d) i) = X (d := d) i := by simp [X]
@[simp] theorem eraseScalar_Z (i : Fin n) : eraseScalar (Z (d := d) i) = Z (d := d) i := by simp [Z]
@[simp] theorem eraseScalar_Xexp (i : Fin n) (a : ZMod d) :
    eraseScalar (Xexp i a) = Xexp i a := by simp [Xexp]
@[simp] theorem eraseScalar_Zexp (i : Fin n) (a : ZMod d) :
    eraseScalar (Zexp i a) = Zexp i a := by simp [Zexp]
@[simp] theorem eraseScalar_CX (i j : Fin n) (h : i ≠ j) :
    eraseScalar (CX i j h) = CX i j h := by simp [CX]

/-- Figure 2 T6: reverse controlled addition, expanded with the same canonical CZ. -/
def XC (i j : Fin n) (h : i ≠ j) : Word n := [.H i, .H i, .H i, .CZ i j h, .H i]
@[simp] theorem eraseScalar_XC (i j : Fin n) (h : i ≠ j) :
    eraseScalar (XC i j h) = XC i j h := by simp [XC]

/-- Scalar erasure preserves the canonical adjacent alphabet. -/
theorem IsAdjacentWord.eraseScalar {w : Word n} (hw : IsAdjacentWord w) :
    IsAdjacentWord (eraseScalar w) := by
  induction w with
  | nil => exact isAdjacentWord_nil
  | cons a w ih =>
    obtain ⟨ha, hw⟩ := (isAdjacentWord_cons a w).mp hw
    cases a <;> simp_all [Circuit.eraseScalar]

@[simp] theorem eraseScalar_relabel {m : ℕ} (ι : Fin m ↪ Fin n) (w : Word m) :
    eraseScalar (relabel ι w) = relabel ι (eraseScalar w) := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp [Gate.relabel, ih]

variable [NeZero d]

/-- Exactly the eighteen Figure 9 equation schemas; no Pauli deletion rule is
included. C3 retains the source's finite range k = 0,...,d-1. -/
inductive Figure9Rule (g : (ZMod d)ˣ) : Word n → Word n → Prop
  | C1 (i : Fin n) : Figure9Rule g (List.replicate d (.S i)) []
  | C2 (i : Fin n) : Figure9Rule g [.H i,.H i] (eraseScalar (multiplier (d := d) i (-1)))
  | C3 (i : Fin n) (k : Fin d) : Figure9Rule g
      (power (eraseScalar (multiplier i g)) k.val) (eraseScalar (multiplier i (g^k.val)))
  | C4 (i : Fin n) : Figure9Rule g
      (eraseScalar (multiplier i g) ++ [.S i])
      (Sexp i ((↑g⁻¹ : ZMod d)^2) ++ eraseScalar (multiplier i g))
  | C5 (i : Fin n) : Figure9Rule g
      [.S i,.H i,.H i,.S i,.H i,.H i] [.H i,.H i,.S i,.H i,.H i,.S i]
  | C6 (i j : Fin n) (h : i ≠ j) : Figure9Rule g (List.replicate d (.CZ i j h)) []
  | C7 (i j : Fin n) (h : i ≠ j) : Figure9Rule g
      (eraseScalar (SWAP (d := d) i j h) ++ eraseScalar (SWAP (d := d) i j h)) []
  | C8 (i j : Fin n) (h : i ≠ j) : Figure9Rule g [.CZ i j h,.S i] [.S i,.CZ i j h]
  | C9 (i j : Fin n) (h : i ≠ j) : Figure9Rule g
      ([.CZ i j h] ++ eraseScalar (multiplier i g))
      (eraseScalar (multiplier i g) ++ List.replicate (g : ZMod d).val (.CZ i j h))
  | C10 (i j : Fin n) (h : i ≠ j) : Figure9Rule g
      (eraseScalar (SWAP (d := d) i j h) ++ [.S i])
      ([.S j] ++ eraseScalar (SWAP (d := d) i j h))
  | C11 (i j : Fin n) (h : i ≠ j) : Figure9Rule g
      (eraseScalar (SWAP (d := d) i j h) ++ [.H i])
      ([.H j] ++ eraseScalar (SWAP (d := d) i j h))
  | C12 (i j : Fin n) (h : i ≠ j) : Figure9Rule g
      (eraseScalar (SWAP (d := d) i j h) ++ [.CZ i j h])
      ([.CZ i j h] ++ eraseScalar (SWAP (d := d) i j h))
  | C13 (i j : Fin n) (h : i ≠ j) : Figure9Rule g
      (XC i j h ++ [.S i])
      ([.S j,.S i] ++ List.replicate (d-1) (.CZ i j h) ++ XC i j h)
  | C14 (i j : Fin n) (h : i ≠ j) : Figure9Rule g
      (XC i j h ++ [.CZ i j h])
      (Sexp j (-2 : ZMod d) ++ [.CZ i j h] ++ XC i j h)
  | C15 (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (_hik : i ≠ k) : Figure9Rule g
      [.CZ i j hij,.CZ j k hjk] [.CZ j k hjk,.CZ i j hij]
  | C16 (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (_hik : i ≠ k) : Figure9Rule g
      (eraseScalar (SWAP (d := d) i j hij) ++ eraseScalar (SWAP (d := d) j k hjk) ++
        eraseScalar (SWAP (d := d) i j hij))
      (eraseScalar (SWAP (d := d) j k hjk) ++ eraseScalar (SWAP (d := d) i j hij) ++
        eraseScalar (SWAP (d := d) j k hjk))
  | C17 (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (_hik : i ≠ k) : Figure9Rule g
      (eraseScalar (SWAP (d := d) j k hjk) ++ eraseScalar (SWAP (d := d) i j hij) ++ [.CZ j k hjk])
      ([.CZ i j hij] ++ eraseScalar (SWAP (d := d) j k hjk) ++ eraseScalar (SWAP (d := d) i j hij))
  | C18 (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) : Figure9Rule g
      ([.CZ j k hjk] ++ CX i j hij)
      (eraseScalar (CIZ (d := d) i j k hij hjk hik) ++ CX i j hij ++ [.CZ j k hjk])

/-- Source rules may be used only when both sides lie in the scalar-free
canonical adjacent alphabet. Structural wiring supplies disjoint commutation. -/
def Figure9Rules (g : (ZMod d)ˣ) (u v : Word n) : Prop :=
  (Structural u v ∨ Figure9Rule g u v) ∧ IsAdjacentWord u ∧ IsAdjacentWord v ∧
    eraseScalar u = u ∧ eraseScalar v = v

abbrev Figure9Derives (g : (ZMod d)ˣ) := Presentation.Derives (Figure9Rules (n := n) g)

theorem Figure9Rule.eraseScalar {g : (ZMod d)ˣ} {u v : Word n}
    (h : Figure9Rule g u v) : eraseScalar u = u ∧ eraseScalar v = v := by
  cases h <;> simp

/-- Introduce a source equation once both adjacency certificates are supplied. -/
theorem figure9Derives_rule {g : (ZMod d)ˣ} {u v : Word n}
    (h : Figure9Rule g u v) (hu : IsAdjacentWord u) (hv : IsAdjacentWord v) :
    Figure9Derives g u v := .rule ⟨Or.inr h, hu, hv, h.eraseScalar⟩

end QuditClifford.Circuit
