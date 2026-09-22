import QuditClifford.Centralizer
import QuditClifford.Gates
import QuditClifford.Presentation

/-!
# Concrete named-wire circuits and Figure 1 helper schemas

A circuit is a word of `-ω,H,S,CZ` gates on named wires.
Lists are in MATRIX order (the rightmost gate acts first). Derived X, Z, M,
CX and SWAP are actual words, not additional primitive generators.

The propositions at the end separate exact soundness from rewrite
completeness. `MultiplierSoundness.lean` proves soundness of these fully
expanded words in odd prime dimension. Exact completeness is proved for zero
and one wire. Arbitrary named CZ letters enlarge the paper's adjacent alphabet;
the source-faithful target lives in `AdjacentPresentation.lean`.
-/

noncomputable section
namespace QuditClifford
namespace Circuit

/-- Primitive gates. Controlled-Z operands must be distinct. -/
inductive Gate (n : ℕ) where
  | scalar
  | H (wire : Fin n)
  | S (wire : Fin n)
  | CZ (i j : Fin n) (distinct : i ≠ j)
  deriving DecidableEq

abbrev Word (n : ℕ) := List (Gate n)

variable {d n : ℕ} [NeZero d]

/-- Lift a single-qudit matrix to a chosen wire, leaving all other wires intact. -/
def onWire (i : Fin n) (A : QuditMatrix d) : QuditOperator d n :=
  fun row col => if ∀ k, k ≠ i → row k = col k then A (row i) (col i) else 0

omit [NeZero d] in
@[simp] theorem onWire_one (i : Fin n) :
    onWire i (1 : QuditMatrix d) = (1 : QuditOperator d n) := by
  classical
  ext row col
  simp only [onWire, Matrix.one_apply]
  by_cases h : row = col
  · subst row; simp
  · by_cases hr : ∀ k, k ≠ i → row k = col k
    · have hi : row i ≠ col i := by
        intro hi
        apply h
        funext k
        by_cases hk : k = i
        · simpa [hk] using hi
        · exact hr k hk
      simp [hr, hi, h]
    · simp [hr, h]

/-- Exact complex interpretation of a primitive gate on the full basis. -/
def Gate.denote (d : ℕ) [NeZero d] : Gate n → QuditOperator d n
  | .scalar => QuditClifford.scalarGenerator d • 1
  | .H i => onWire i (QuditClifford.H d)
  | .S i => onWire i (QuditClifford.S d)
  | .CZ i j _ => Matrix.diagonal (fun x => phase d (x i * x j))

/-- Exact denotation; no projective quotient is taken. -/
def denote (d : ℕ) [NeZero d] (w : Word n) : QuditOperator d n :=
  Presentation.eval (Gate.denote d) w

@[simp] theorem denote_nil : denote d ([] : Word n) = 1 := rfl
@[simp] theorem denote_append (u v : Word n) :
    denote d (u ++ v) = denote d u * denote d v := Presentation.eval_append _ _ _

/-- A natural power of a circuit, in matrix order. -/
def power (w : Word n) (k : ℕ) : Word n := (List.replicate k w).flatten

@[simp] theorem denote_power (w : Word n) (k : ℕ) : denote d (power w k) = denote d w ^ k := by
  induction k with
  | zero => simp [power]
  | succ k ih =>
    simp only [power, List.replicate_succ, List.flatten_cons, denote_append] at *
    rw [ih, pow_succ']

/-- Natural powers of the only primitive scalar `-ω`. -/
def scalar (k : ℕ) : Word n := List.replicate k .scalar

/-- The scalar `ω^a=(-ω)^((d+1)*a.val)` in odd dimension. -/
def omegaPower (a : ZMod d) : Word n := scalar ((d + 1) * a.val)

/-- `S^a`, where `a` is a residue and the exponent is its natural representative. -/
def Sexp (i : Fin n) (a : ZMod d) : Word n := List.replicate a.val (.S i)

/-- T3, in matrix order: `Z=H² S H² S⁻¹`. -/
def Z (i : Fin n) : Word n := [.H i, .H i, .S i, .H i, .H i] ++ Sexp i (-1 : ZMod d)

/-- T2, in matrix order: `X=H S H² S⁻¹ H`. -/
def X (i : Fin n) : Word n := [.H i, .S i, .H i, .H i] ++ Sexp i (-1 : ZMod d) ++ [.H i]

def Xexp (i : Fin n) (a : ZMod d) : Word n := power (X (d := d) i) a.val
def Zexp (i : Fin n) (a : ZMod d) : Word n := power (Z (d := d) i) a.val

/-- The Legendre sign encoded by zero or one copies of `(-ω)^d`.
For prime d and a unit a, this is precisely the Legendre-symbol definition. -/
def legendreSign (a : (ZMod d)ˣ) : ℕ := if IsSquare (a : ZMod d) then 0 else 1

/-- T1, expanded entirely into the primitive alphabet, including both scalars. -/
def multiplier (i : Fin n) (a : (ZMod d)ˣ) : Word n :=
  scalar (d * legendreSign a) ++
  omegaPower ((-(a : ZMod d)^2 + 4*(a : ZMod d) - 2) * (8*(a : ZMod d))⁻¹) ++
  Zexp i ((1-(a : ZMod d)) * (2*(a : ZMod d))⁻¹) ++
  Xexp i ((1-(a : ZMod d)) * (2 : ZMod d)⁻¹) ++
  Sexp i (↑a⁻¹ : ZMod d) ++ [.H i] ++
  Sexp i (a : ZMod d) ++ [.H i] ++ Sexp i (↑a⁻¹ : ZMod d) ++ [.H i]

/-- T5: control i, target j; `CX=(H_j)^3 CZ_ij H_j`. -/
def CX (i j : Fin n) (h : i ≠ j) : Word n := [.H j, .H j, .H j, .CZ i j h, .H j]

/-- T4 with its essential `lambda²=(-1)^((d-1)/2)` scalar. -/
def SWAP (i j : Fin n) (h : i ≠ j) : Word n :=
  scalar (d * ((d-1)/2)) ++ power [.CZ i j h, .H i, .H j] 3

/-- T7: the remote controlled phase is a derived word, not an extra primitive
in the C15 rule. The intermediate wire `j` is restored by the two SWAPs. -/
def CIZ (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (_hik : i ≠ k) : Word n :=
  SWAP (d := d) j k hjk ++ [.CZ i j hij] ++ SWAP (d := d) j k hjk

/-- The support excludes scalar gates, which are structurally central. -/
def Gate.support : Gate n → Finset (Fin n)
  | .scalar => ∅
  | .H i => {i}
  | .S i => {i}
  | .CZ i j _ => {i,j}

/-- Equations supplied by the circuit wiring convention, before Figure 1. -/
inductive Structural : Word n → Word n → Prop
  | disjoint (a b : Gate n) (h : Disjoint a.support b.support) :
      Structural [a,b] [b,a]
  | CZ_symmetry (i j : Fin n) (h : i ≠ j) :
      Structural [.CZ i j h] [.CZ j i h.symm]

/-- The sixteen Figure 1 schemas. They are syntactic relations on fully
expanded primitive words. `k : Fin d` in C3 respects the displayed finite
family; this definition does not silently use all integer-power relations. -/
inductive Figure1Rule (g : (ZMod d)ˣ) : Word n → Word n → Prop
  | C0 : Figure1Rule g (scalar (2*d)) []
  | C1 (i : Fin n) : Figure1Rule g (List.replicate d (.S i)) []
  | C2 (i : Fin n) : Figure1Rule g [.H i, .H i]
      (scalar (d * ((d-1)/2)) ++ multiplier (d := d) i (-1))
  | C3 (i : Fin n) (k : Fin d) : Figure1Rule g
      (power (multiplier i g) k.val) (multiplier i (g^k.val))
  | C4 (i : Fin n) : Figure1Rule g
      (multiplier i g ++ [.S i])
      (Zexp i ((1-(g : ZMod d)) * (2*(g : ZMod d)^2)⁻¹) ++
        Sexp i ((↑g⁻¹ : ZMod d)^2) ++ multiplier i g)
  | C5 (i : Fin n) : Figure1Rule g
      [.S i, .H i, .H i, .S i, .H i, .H i]
      [.H i, .H i, .S i, .H i, .H i, .S i]
  | C6 (i j : Fin n) (h : i ≠ j) : Figure1Rule g (List.replicate d (.CZ i j h)) []
  | C7 (i j : Fin n) (h : i ≠ j) : Figure1Rule g
      (SWAP (d := d) i j h ++ SWAP (d := d) i j h) []
  | C8 (i j : Fin n) (h : i ≠ j) : Figure1Rule g [.CZ i j h, .S i] [.S i, .CZ i j h]
  | C9 (i j : Fin n) (h : i ≠ j) : Figure1Rule g
      ([.CZ i j h] ++ multiplier i g)
      (multiplier i g ++ List.replicate (g : ZMod d).val (.CZ i j h))
  | C10 (i j : Fin n) (h : i ≠ j) : Figure1Rule g
      (SWAP (d := d) i j h ++ [.S i]) ([.S j] ++ SWAP (d := d) i j h)
  | C11 (i j : Fin n) (h : i ≠ j) : Figure1Rule g
      (SWAP (d := d) i j h ++ [.H i]) ([.H j] ++ SWAP (d := d) i j h)
  | C12 (i j : Fin n) (h : i ≠ j) : Figure1Rule g
      (Sexp i (-1 : ZMod d) ++ Sexp j (-1 : ZMod d) ++
        power (CX i j h) (d-1) ++ [.S j] ++ CX i j h) [.CZ i j h]
  | C13 (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (_hik : i ≠ k) : Figure1Rule g
      (SWAP (d := d) i j hij ++ SWAP (d := d) j k hjk ++ SWAP (d := d) i j hij)
      (SWAP (d := d) j k hjk ++ SWAP (d := d) i j hij ++ SWAP (d := d) j k hjk)
  | C14 (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (_hik : i ≠ k) : Figure1Rule g
      (SWAP (d := d) j k hjk ++ SWAP (d := d) i j hij ++ [.CZ j k hjk])
      ([.CZ i j hij] ++ SWAP (d := d) j k hjk ++ SWAP (d := d) i j hij)
  | C15 (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) : Figure1Rule g
      ([.CZ j k hjk] ++ CX i j hij)
      (CIZ (d := d) i j k hij hjk hik ++ CX i j hij ++ [.CZ j k hjk])

/-- The base relation includes wiring coherence and the sixteen schemas only. -/
def Rules (g : (ZMod d)ˣ) (a b : Word n) : Prop := Structural a b ∨ Figure1Rule g a b

/-- Exact derivability, with sequential contexts. Gates may act on arbitrary
named wires, so idle-wire extensions and injections are covered by the schemas. -/
def Derives (g : (ZMod d)ˣ) : Word n → Word n → Prop := Presentation.Derives (Rules g)

/-- Exact soundness of the expanded Figure 1 presentation. Proved for odd
prime dimension by `figure1_sound` in `MultiplierSoundness.lean`. -/
def Figure1Sound (g : (ZMod d)ˣ) : Prop :=
  ∀ a b : Word n, Derives g a b → denote d a = denote d b

/-- Completeness of the enlarged named-wire presentation at a fixed arity.
It is proved for arities zero and one. For three or more wires this target
is stronger than the paper's adjacent-generator presentation: a remote CZ
here is an independent primitive, whereas Figure 4 T7 expands it using SWAPs.
See `AdjacentPresentation` for the source-faithful completeness target. -/
def Figure1Complete (g : (ZMod d)ˣ) : Prop :=
  ∀ a b : Word n, denote d a = denote d b → Derives g a b

/-- The former, overly broad named-wire target. It is retained under an explicit
name for auditing and is not the paper's main theorem. No proof assumes it. -/
def NamedWireMainTheorem (d : ℕ) [NeZero d] : Prop :=
  d.Prime → Odd d → ∀ g : (ZMod d)ˣ, orderOf g = d-1 →
    ∀ n, Figure1Sound (n := n) g ∧ Figure1Complete (n := n) g

end Circuit
end QuditClifford
