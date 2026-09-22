import QuditClifford.SymplecticRewrites
import Mathlib.Tactic.FinCases

/-!
# A finite countermodel to unrestricted named-wire completeness

This model keeps the local symplectic H and S matrices but reverses every
primitive CZ coupling. All displayed relations still hold. On three wires
the remote SWAP expansion has the opposite coupling to the primitive CZ on
the same two endpoints, exposing the missing named-wire coherence equation.
-/
namespace QuditClifford.Circuit.NamedWireCountermodel

abbrev Mat := Matrix (Fin 6) (Fin 6) (ZMod 3)

def gate : Gate 3 → Mat
  | .scalar => 1
  | .H i => fun r c =>
      if r.val = i.val then if c.val = i.val+3 then 1 else 0
      else if r.val = i.val+3 then if c.val = i.val then -1 else 0
      else if r=c then 1 else 0
  | .S i => fun r c =>
      if r.val=i.val ∧ c.val=i.val+3 then 1 else if r=c then 1 else 0
  | .CZ i j _ => fun r c =>
      if (r.val=i.val ∧ c.val=j.val+3) ∨ (r.val=j.val ∧ c.val=i.val+3)
      then -1 else if r=c then 1 else 0

def eval (w : Word 3) : Mat := Presentation.eval gate w

@[simp] theorem eval_nil : eval []=1 := rfl
@[simp] theorem eval_cons (x : Gate 3) (w : Word 3) : eval (x::w)=gate x*eval w := rfl
@[simp] theorem eval_append (u v : Word 3) : eval (u++v)=eval u*eval v :=
  Presentation.eval_append _ _ _
@[simp] theorem eval_replicate (k : ℕ) (x : Gate 3) : eval (List.replicate k x)=(gate x)^k := by
  induction k with
  | zero => simp
  | succ k ih => simp only [List.replicate_succ, eval_cons, ih, pow_succ']
@[simp] theorem eval_scalar (k : ℕ) : eval (scalar k)=1 := by simp [scalar, gate]
@[simp] theorem eval_omegaPower (a : ZMod 3) : eval (omegaPower a)=1 := eval_scalar _
@[simp] theorem eval_power (w : Word 3) (k : ℕ) : eval (power w k)=eval w^k := by
  induction k with
  | zero => simp [power]
  | succ k ih =>
    simp only [power, List.replicate_succ, List.flatten_cons, eval_append] at *
    rw [ih, pow_succ']

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem eval_X : ∀ i : Fin 3, eval (X (d := 3) i)=1 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem eval_Z : ∀ i : Fin 3, eval (Z (d := 3) i)=1 := by decide

@[simp] theorem eval_Xexp (i : Fin 3) (a : ZMod 3) : eval (Xexp i a)=1 := by
  simp only [Xexp, eval_power, eval_X, one_pow]
@[simp] theorem eval_Zexp (i : Fin 3) (a : ZMod 3) : eval (Zexp i a)=1 := by
  simp only [Zexp, eval_power, eval_Z, one_pow]

/-- Scalar and Pauli factors of the literal multiplier vanish in this model. -/
theorem eval_multiplier (i : Fin 3) (a : (ZMod 3)ˣ) :
    eval (multiplier i a)=
      eval (Sexp i (↑a⁻¹ : ZMod 3))*gate (.H i)*eval (Sexp i (a : ZMod 3))*
        gate (.H i)*eval (Sexp i (↑a⁻¹ : ZMod 3))*gate (.H i) := by
  simp only [multiplier, eval_append, eval_scalar, eval_omegaPower, eval_Zexp, eval_Xexp,
    eval_cons, eval_nil, mul_one, one_mul]

def generator : (ZMod 3)ˣ := -1

def phaseMatrix (i : Fin 3) (a : ZMod 3) : Mat := fun r c =>
  if r.val=i.val ∧ c.val=i.val+3 then a else if r=c then 1 else 0

def phaseHMatrix (i : Fin 3) (a : ZMod 3) : Mat := fun r c =>
  if r.val=i.val then if c.val=i.val then -a else if c.val=i.val+3 then 1 else 0
  else if r.val=i.val+3 then if c.val=i.val then -1 else 0
  else if r=c then 1 else 0

def multiplierMatrix (i : Fin 3) (a : (ZMod 3)ˣ) : Mat := fun r c =>
  if r=c then if r.val=i.val then (a⁻¹ : (ZMod 3)ˣ) else if r.val=i.val+3 then a else 1 else 0

def swapCoreMatrix (i j : Fin 3) : Mat := fun r c =>
  if r.val=i.val then if c.val=i.val+3 ∨ c.val=j.val then 1 else 0
  else if r.val=j.val then if c.val=j.val+3 ∨ c.val=i.val then 1 else 0
  else if r.val=i.val+3 then if c.val=i.val then -1 else 0
  else if r.val=j.val+3 then if c.val=j.val then -1 else 0
  else if r=c then 1 else 0

def swapMatrix (i j : Fin 3) : Mat := fun r c =>
  if r.val=i.val then if c.val=j.val then -1 else 0
  else if r.val=j.val then if c.val=i.val then -1 else 0
  else if r.val=i.val+3 then if c.val=j.val+3 then -1 else 0
  else if r.val=j.val+3 then if c.val=i.val+3 then -1 else 0
  else if r=c then 1 else 0

def cxMatrix (i j : Fin 3) : Mat := fun r c =>
  if r.val=i.val ∧ c.val=j.val then 1
  else if r.val=j.val+3 ∧ c.val=i.val+3 then -1
  else if r=c then 1 else 0

def remoteMatrix (i k : Fin 3) : Mat := fun r c =>
  if (r.val=i.val ∧ c.val=k.val+3) ∨ (r.val=k.val ∧ c.val=i.val+3)
  then 1 else if r=c then 1 else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem eval_Sexp : ∀ (i : Fin 3) (a : ZMod 3), eval (Sexp i a)=phaseMatrix i a := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem phaseH_eq : ∀ (i : Fin 3) (a : ZMod 3), phaseMatrix i a*gate (.H i)=phaseHMatrix i a := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem eval_multiplier_matrix (i : Fin 3) (a : (ZMod 3)ˣ) :
    eval (multiplier i a)=multiplierMatrix i a := by
  rw [eval_multiplier]
  simp only [eval_Sexp]
  calc
    _ = (phaseMatrix i (↑a⁻¹ : ZMod 3)*gate (.H i))*(phaseMatrix i (a : ZMod 3)*gate (.H i))*
        (phaseMatrix i (↑a⁻¹ : ZMod 3)*gate (.H i)) := by simp only [mul_assoc]
    _ = _ := by
      simp only [phaseH_eq]
      revert i a
      decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem eval_swapCore : ∀ (i j : Fin 3) (hij : i ≠ j),
    eval [.CZ i j hij, .H i, .H j]=swapCoreMatrix i j := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem eval_SWAP (i j : Fin 3) (hij : i ≠ j) :
    eval (SWAP (d := 3) i j hij)=swapMatrix i j := by
  simp only [SWAP, eval_append, eval_scalar, one_mul, eval_power, eval_swapCore]
  revert i j hij
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem eval_CX : ∀ (i j : Fin 3) (hij : i ≠ j), eval (CX i j hij)=cxMatrix i j := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem eval_CIZ (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    eval (CIZ (d := 3) i j k hij hjk hik)=remoteMatrix i k := by
  simp only [CIZ, eval_append, eval_SWAP, eval_cons, eval_nil, mul_one]
  revert i j k hij hjk hik
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All sixteen schemas, including their exact expanded scalar and Pauli
factors, preserve the finite reversed-edge model. -/
theorem figure1_sound {u v : Word 3} (h : Figure1Rule generator u v) : eval u=eval v := by
  cases h with
  | C0 => simp
  | C1 i => revert i; decide
  | C2 i =>
    simp only [eval_append, eval_scalar, one_mul, eval_multiplier_matrix]
    revert i; decide
  | C3 i k =>
    simp only [eval_power, eval_multiplier_matrix]
    revert i k; decide
  | C4 i =>
    simp only [eval_append, eval_Zexp, one_mul, eval_multiplier_matrix, eval_Sexp]
    revert i; decide
  | C5 i => revert i; decide
  | C6 i j hij => revert i j hij; decide
  | C7 i j hij =>
    simp only [eval_append, eval_SWAP, eval_nil]
    revert i j hij; decide
  | C8 i j hij => revert i j hij; decide
  | C9 i j hij =>
    simp only [eval_append, eval_multiplier_matrix]
    revert i j hij; decide
  | C10 i j hij =>
    simp only [eval_append, eval_SWAP]
    revert i j hij; decide
  | C11 i j hij =>
    simp only [eval_append, eval_SWAP]
    revert i j hij; decide
  | C12 i j hij =>
    simp only [eval_append, eval_power, eval_CX, eval_Sexp]
    revert i j hij; decide
  | C13 i j k hij hjk hik =>
    simp only [eval_append, eval_SWAP]
    revert i j k hij hjk hik; decide
  | C14 i j k hij hjk hik =>
    simp only [eval_append, eval_SWAP]
    revert i j k hij hjk hik; decide
  | C15 i j k hij hjk hik =>
    simp only [eval_append, eval_CX, eval_CIZ]
    revert i j k hij hjk hik; decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem structural_sound {u v : Word 3} (h : Structural u v) : eval u=eval v := by
  cases h with
  | CZ_symmetry i j hij => revert i j hij; decide
  | disjoint a b hab =>
    have hHH : ∀ i j : Fin 3, gate (.H i)*gate (.H j)=gate (.H j)*gate (.H i) := by decide
    have hSS : ∀ i j : Fin 3, gate (.S i)*gate (.S j)=gate (.S j)*gate (.S i) := by decide
    have hHS : ∀ i j : Fin 3, Disjoint (Gate.H i).support (Gate.S j).support →
        gate (.H i)*gate (.S j)=gate (.S j)*gate (.H i) := by decide
    have hHC : ∀ (i j k : Fin 3) (hjk : j ≠ k),
        Disjoint (Gate.H i).support (Gate.CZ j k hjk).support →
          gate (.H i)*gate (.CZ j k hjk)=gate (.CZ j k hjk)*gate (.H i) := by decide
    have hSC : ∀ (i j k : Fin 3) (hjk : j ≠ k),
        Disjoint (Gate.S i).support (Gate.CZ j k hjk).support →
          gate (.S i)*gate (.CZ j k hjk)=gate (.CZ j k hjk)*gate (.S i) := by decide
    have hCC : ∀ (i j k l : Fin 3) (hij : i ≠ j) (hkl : k ≠ l),
        gate (.CZ i j hij)*gate (.CZ k l hkl)=gate (.CZ k l hkl)*gate (.CZ i j hij) := by decide
    simp only [eval_cons, eval_nil, mul_one]
    cases a with
    | scalar => simp [gate]
    | H i =>
      cases b with
      | scalar => simp [gate]
      | H j => exact hHH i j
      | S j => exact hHS i j hab
      | CZ j k hjk => exact hHC i j k hjk hab
    | S i =>
      cases b with
      | scalar => simp [gate]
      | H j => exact (hHS j i hab.symm).symm
      | S j => exact hSS i j
      | CZ j k hjk => exact hSC i j k hjk hab
    | CZ i j hij =>
      cases b with
      | scalar => simp [gate]
      | H k => exact (hHC k i j hij hab.symm).symm
      | S k => exact (hSC k i j hij hab.symm).symm
      | CZ k l hkl => exact hCC i j k l hij hkl

theorem symplecticRules_sound {u v : Word 3} (h : SymplecticRules generator u v) :
    eval u=eval v := by
  rcases h with ((h | h) | ⟨rfl, rfl⟩) | ⟨i, (rfl | rfl), rfl⟩
  · exact structural_sound h
  · exact figure1_sound h
  · simp [gate]
  · exact eval_X i
  · exact eval_Z i

/-- Every derivation, including all explicit scalar and Pauli erasures,
preserves the finite countermodel. -/
theorem symplecticDerives_sound {u v : Word 3} (h : SymplecticDerives generator u v) :
    eval u=eval v :=
  Presentation.sound_derives (fun _ _ h => symplecticRules_sound h) h

/-- The entry `z₀ ← x₂` distinguishes direct CZ from its proposed remote expansion. -/
theorem direct_CZ_ne_CIZ : eval [.CZ 0 2 (by decide)] ≠
    eval (CIZ (d := 3) 0 1 2 (by decide) (by decide) (by decide)) := by
  intro h
  have he := congrArg (fun M : Mat => M 0 5) h
  dsimp only at he
  have hd : eval [.CZ 0 2 (by decide)] 0 5=2 := by decide
  have hr : eval (CIZ (d := 3) 0 1 2 (by decide) (by decide) (by decide)) 0 5=1 := by
    rw [eval_CIZ]; decide
  rw [hd, hr] at he
  exact (by decide : (2 : ZMod 3) ≠ 1) he

/-- The proposed extra named-wire coherence equation is not derivable even
after scalar and Pauli erasure from the current Figure 1 presentation. -/
theorem not_symplecticDerives_direct_CZ_CIZ :
    ¬ SymplecticDerives (n := 3) generator [.CZ 0 2 (by decide)]
      (CIZ (d := 3) 0 1 2 (by decide) (by decide) (by decide)) :=
  fun h => direct_CZ_ne_CIZ (symplecticDerives_sound h)

/-- In particular the missing coherence is not an exact Figure 1 consequence. -/
theorem not_derives_direct_CZ_CIZ :
    ¬ Derives (n := 3) generator [.CZ 0 2 (by decide)]
      (CIZ (d := 3) 0 1 2 (by decide) (by decide) (by decide)) :=
  fun h => not_symplecticDerives_direct_CZ_CIZ (derives_symplectic generator h)

/-- The unrestricted named-wire completeness proposition is false already
for three qutrits: its two equal exact denotations are not derivably equal. -/
theorem not_figure1Complete : ¬ Figure1Complete (n := 3) generator := by
  intro h
  apply not_derives_direct_CZ_CIZ
  apply h
  rw [denote_CIZ (by decide : Odd 3)]
  simp only [denote_cons, denote_nil, mul_one]

/-- The countermodel uses an actual generator of the qutrit multiplicative group. -/
theorem generator_order : orderOf generator=3-1 := by
  rw [generator, ← orderOf_units, Units.coe_neg_one, orderOf_neg_one, ringChar.eq (ZMod 3) 3]
  norm_num

/-- The former all-named-wire target cannot be the paper's main theorem. -/
theorem not_namedWireMainTheorem_three : ¬ NamedWireMainTheorem 3 := by
  intro h
  exact not_figure1Complete ((h (by decide) (by decide) generator generator_order 3).2)

end QuditClifford.Circuit.NamedWireCountermodel
