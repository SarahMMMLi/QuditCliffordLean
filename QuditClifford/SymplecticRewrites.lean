import QuditClifford.ProjectiveRewrites
import QuditClifford.GeneratedRealization

/-! # Explicit Pauli erasure of the Figure 1 presentation

The symplectic relation adds only deletion of the expanded X and Z words to
the scalar-erased Figure 1 relation. The quotient remains syntactic: equality
of exponent actions is proved sound, but is never a generating relation.
This supplies a concrete target for the remaining box-normalization proof.
-/
noncomputable section
namespace QuditClifford.Circuit
variable {d n : ℕ} [NeZero d]

/-- Forget the scalar and Pauli subgroup using explicit deletion equations. -/
def SymplecticRules (g : (ZMod d)ˣ) (u v : Word n) : Prop :=
  ProjectiveRules g u v ∨ ∃ i : Fin n, (u = X (d := d) i ∨ u = Z (d := d) i) ∧ v = []

def SymplecticDerives (g : (ZMod d)ˣ) : Word n → Word n → Prop :=
  Presentation.Derives (SymplecticRules g)

theorem projectiveDerives_symplectic (g : (ZMod d)ˣ) {u v : Word n}
    (h : ProjectiveDerives g u v) : SymplecticDerives g u v :=
  h.mono (fun _ _ hr => .rule (Or.inl hr))

theorem derives_symplectic (g : (ZMod d)ˣ) {u v : Word n}
    (h : Derives g u v) : SymplecticDerives g u v :=
  projectiveDerives_symplectic g (derives_projective g h)

theorem symplecticDerives_X (g : (ZMod d)ˣ) (i : Fin n) :
    SymplecticDerives g (X (d := d) i) [] := .rule (Or.inr ⟨i, Or.inl rfl, rfl⟩)

theorem symplecticDerives_Z (g : (ZMod d)ˣ) (i : Fin n) :
    SymplecticDerives g (Z (d := d) i) [] := .rule (Or.inr ⟨i, Or.inr rfl, rfl⟩)

theorem symplecticDerives_scalar (g : (ZMod d)ˣ) (k : ℕ) :
    SymplecticDerives (n := n) g (scalar k) [] :=
  projectiveDerives_symplectic g (projectiveDerives_scalar g k)

/-- Words modulo the displayed syntactic symplectic erasures. -/
def PresentedSymplectic (g : (ZMod d)ˣ) (n : ℕ) :=
  Quotient (Presentation.rewriteSetoid (SymplecticRules (n := n) g))

def symplecticClassWord (g : (ZMod d)ˣ) (w : Word n) : PresentedSymplectic g n :=
  Quotient.mk _ w

theorem symplecticClassWord_eq_iff_derives (g : (ZMod d)ˣ) (u v : Word n) :
    symplecticClassWord g u = symplecticClassWord g v ↔ SymplecticDerives g u v :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

theorem symplecticClassWord_surjective (g : (ZMod d)ˣ) :
    Function.Surjective (symplecticClassWord (n := n) g) := Quotient.exists_rep

instance (g : (ZMod d)ˣ) : One (PresentedSymplectic g n) := ⟨symplecticClassWord g []⟩
instance (g : (ZMod d)ˣ) : Mul (PresentedSymplectic g n) :=
  ⟨Quotient.map₂ (· ++ ·) (fun _ _ h₁ _ _ h₂ => h₁.append h₂)⟩

@[simp] theorem symplecticClassWord_nil (g : (ZMod d)ˣ) :
    symplecticClassWord (n := n) g [] = 1 := rfl

@[simp] theorem symplecticClassWord_append (g : (ZMod d)ˣ) (u v : Word n) :
    symplecticClassWord g (u ++ v) = symplecticClassWord g u * symplecticClassWord g v := rfl

instance (g : (ZMod d)ˣ) : Monoid (PresentedSymplectic g n) where
  mul_assoc := by
    intro a b c
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b =>
        induction c using Quotient.inductionOn with | h c =>
          change symplecticClassWord g ((a ++ b) ++ c) = symplecticClassWord g (a ++ (b ++ c))
          rw [List.append_assoc]
  one_mul := by intro a; induction a using Quotient.inductionOn with | h a => rfl
  mul_one := by
    intro a
    induction a using Quotient.inductionOn with | h a =>
      change symplecticClassWord g (a ++ []) = symplecticClassWord g a
      rw [List.append_nil]

/-- The exact syntactic quotient maps to its explicitly Pauli-erased quotient. -/
def presentedToSymplectic (g : (ZMod d)ˣ) : PresentedCircuit g n →* PresentedSymplectic g n where
  toFun := Quotient.map id (fun _ _ h => derives_symplectic g h)
  map_one' := rfl
  map_mul' := by
    intro a b
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b => rfl

@[simp] theorem presentedToSymplectic_classWord (g : (ZMod d)ˣ) (w : Word n) :
    presentedToSymplectic g (classWord g w) = symplecticClassWord g w := rfl

theorem symplecticClassWord_cons (g : (ZMod d)ˣ) (a : Gate n) (w : Word n) :
    symplecticClassWord g (a::w) = symplecticClassWord g [a] * symplecticClassWord g w := rfl

theorem symplecticClassWord_power (g : (ZMod d)ˣ) (w : Word n) (k : ℕ) :
    symplecticClassWord g (power w k) = symplecticClassWord g w ^ k := by
  simpa using congrArg (presentedToSymplectic g) (classWord_power g w k)

theorem symplecticClassWord_replicate (g : (ZMod d)ˣ) (a : Gate n) (k : ℕ) :
    symplecticClassWord g (List.replicate k a) = symplecticClassWord g [a] ^ k := by
  simpa using congrArg (presentedToSymplectic g) (classWord_replicate g a k)

@[simp] theorem symplecticClassWord_scalar (g : (ZMod d)ˣ) (k : ℕ) :
    symplecticClassWord (n := n) g (scalar k) = 1 :=
  Quotient.sound (symplecticDerives_scalar g k)

@[simp] theorem symplecticClassWord_omegaPower (g : (ZMod d)ˣ) (a : ZMod d) :
    symplecticClassWord (n := n) g (omegaPower a) = 1 := symplecticClassWord_scalar g _

@[simp] theorem symplecticClassWord_X (g : (ZMod d)ˣ) (i : Fin n) :
    symplecticClassWord g (X (d := d) i) = 1 := Quotient.sound (symplecticDerives_X g i)

@[simp] theorem symplecticClassWord_Z (g : (ZMod d)ˣ) (i : Fin n) :
    symplecticClassWord g (Z (d := d) i) = 1 := Quotient.sound (symplecticDerives_Z g i)

@[simp] theorem symplecticClassWord_Xexp (g : (ZMod d)ˣ) (i : Fin n) (a : ZMod d) :
    symplecticClassWord g (Xexp i a) = 1 := by simp [Xexp, symplecticClassWord_power]

@[simp] theorem symplecticClassWord_Zexp (g : (ZMod d)ˣ) (i : Fin n) (a : ZMod d) :
    symplecticClassWord g (Zexp i a) = 1 := by simp [Zexp, symplecticClassWord_power]

variable [Fact d.Prime]

private theorem symplectic_cancel_left (hd : Odd d) (g : (ZMod d)ˣ) (hg : orderOf g = d-1)
    {u v w : Word n} (h : SymplecticDerives g (w ++ u) (w ++ v)) : SymplecticDerives g u v := by
  have hc := derives_symplectic g (derives_inverseWord_append hd g hg w)
  have hu : SymplecticDerives g (inverseWord d w ++ (w ++ u)) u := by
    simpa only [List.append_assoc, List.nil_append] using hc.append_right u
  have hv : SymplecticDerives g (inverseWord d w ++ (w ++ v)) v := by
    simpa only [List.append_assoc, List.nil_append] using hc.append_right v
  exact hu.symm.trans ((h.append_left (inverseWord d w)).trans hv)

theorem symplecticDerives_inverseWord (hd : Odd d) (g : (ZMod d)ˣ) (hg : orderOf g = d-1)
    {u v : Word n} (h : SymplecticDerives g u v) :
    SymplecticDerives g (inverseWord d u) (inverseWord d v) := by
  apply symplectic_cancel_left hd g hg (w := u)
  exact (derives_symplectic g (derives_append_inverseWord hd g hg u)).trans
    ((derives_symplectic g (derives_append_inverseWord hd g hg v)).symm.trans
      (h.symm.append_right (inverseWord d v)))

instance (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)] :
    Inv (PresentedSymplectic g n) :=
  ⟨Quotient.map (inverseWord d) (fun _ _ h => symplecticDerives_inverseWord Fact.out g Fact.out h)⟩

instance (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)] :
    Group (PresentedSymplectic g n) where
  inv_mul_cancel := by
    intro a
    induction a using Quotient.inductionOn with | h a =>
      exact Quotient.sound (derives_symplectic g (derives_inverseWord_append Fact.out g Fact.out a))

@[simp] theorem symplecticClassWord_inverseWord (g : (ZMod d)ˣ) [Fact (Odd d)]
    [Fact (orderOf g = d-1)] (w : Word n) :
    symplecticClassWord g (inverseWord d w) = (symplecticClassWord g w)⁻¹ := rfl

/-- Every generating equation preserves the actual exponent action. -/
theorem symplecticRules_sound (hd : Odd d) (g : (ZMod d)ˣ) {u v : Word n}
    (h : SymplecticRules g u v) (p : PhaseSpace d n) :
    symplecticAction d u p = symplecticAction d v p := by
  rcases h with (he | ⟨rfl, rfl⟩) | ⟨i, he, rfl⟩
  · have hw : generatedWord (d := d) u = generatedWord v :=
      Subtype.ext (Subtype.ext (figure1_sound hd g u v (.rule he)))
    have hf := congrArg (generatedSymplecticHom hd) hw
    simpa only [generatedSymplecticHom_word] using
      congrArg (fun F : symplecticGroup d n => F.val p) hf
  · rfl
  · rcases he with rfl | rfl <;> simp

/-- The contextual symplectic erasure relation is sound for exponent actions. -/
theorem symplecticDerives_sound (hd : Odd d) (g : (ZMod d)ˣ) {u v : Word n}
    (h : SymplecticDerives g u v) :
    ∀ p : PhaseSpace d n, symplecticAction d u p = symplecticAction d v p := by
  induction h with
  | refl w => intro p; rfl
  | rule h => exact symplecticRules_sound hd g h
  | symm h ih => intro p; exact (ih p).symm
  | trans h₁ h₂ ih₁ ih₂ => intro p; exact (ih₁ p).trans (ih₂ p)
  | context l r h ih => intro p; simp only [symplecticAction_append, ih]

/-- Interpretation of the syntactic quotient in the independently constructed
symplectic group. Its faithfulness remains the normalization obligation. -/
def presentedSymplecticInterpret (hd : Odd d) (g : (ZMod d)ˣ) :
    PresentedSymplectic g n →* symplecticGroup d n where
  toFun := Quotient.lift (fun w => generatedSymplecticHom hd (generatedWord w)) (by
    intro u v h
    apply Subtype.ext
    apply LinearEquiv.ext
    intro p
    simpa only [generatedSymplecticHom_word] using symplecticDerives_sound hd g h p)
  map_one' := by change generatedSymplecticHom hd (generatedWord []) = 1; simp
  map_mul' := by
    intro a b
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b =>
        change generatedSymplecticHom hd (generatedWord (a++b)) =
          generatedSymplecticHom hd (generatedWord a) *
            generatedSymplecticHom hd (generatedWord b)
        rw [generatedWord_append, map_mul]

@[simp] theorem presentedSymplecticInterpret_classWord (hd : Odd d) (g : (ZMod d)ˣ)
    (w : Word n) :
    presentedSymplecticInterpret hd g (symplecticClassWord g w) =
      generatedSymplecticHom hd (generatedWord w) := rfl

@[simp] theorem presentedSymplecticInterpret_apply (hd : Odd d) (g : (ZMod d)ˣ)
    (w : Word n) (p : PhaseSpace d n) :
    (presentedSymplecticInterpret hd g (symplecticClassWord g w)).val p =
      symplecticAction d w p := generatedSymplecticHom_word hd w p

/-- Forgetting syntactic Pauli data agrees with the actual matrix exponent action. -/
theorem presentedSymplecticInterpret_comp (hd : Odd d) (g : (ZMod d)ˣ) :
    (presentedSymplecticInterpret (n := n) hd g).comp (presentedToSymplectic g) =
      (generatedSymplecticHom hd).comp (presentedToGenerated hd g) := by
  apply MonoidHom.ext
  intro q
  induction q using Quotient.inductionOn with | h w => rfl

theorem presentedSymplecticInterpret_surjective (hd : Odd d) (g : (ZMod d)ˣ) :
    Function.Surjective (presentedSymplecticInterpret (n := n) hd g) := by
  intro F
  obtain ⟨U, hU⟩ := generatedSymplecticHom_surjective hd F
  obtain ⟨w, rfl⟩ := generatedWord_surjective hd U
  exact ⟨symplecticClassWord g w, hU⟩

/-- The explicit Pauli-erased completeness target, separate from both exact
Figure 1 completeness and a literal presentation of Figure 9's eighteen rules. -/
def SymplecticErasureComplete (g : (ZMod d)ˣ) : Prop :=
  ∀ u v : Word n, (∀ p, symplecticAction d u p = symplecticAction d v p) →
    SymplecticDerives g u v

theorem symplecticErasureComplete_iff_interpret_injective (hd : Odd d) (g : (ZMod d)ˣ) :
    SymplecticErasureComplete (n := n) g ↔
      Function.Injective (presentedSymplecticInterpret (n := n) hd g) := by
  constructor
  · intro hc a b hab
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b =>
        apply Quotient.sound
        apply hc a b
        intro p
        change presentedSymplecticInterpret hd g (symplecticClassWord g a) =
          presentedSymplecticInterpret hd g (symplecticClassWord g b) at hab
        simpa only [presentedSymplecticInterpret_apply] using
          congrArg (fun F : symplecticGroup d n => F.val p) hab
  · intro hi u v huv
    apply (symplecticClassWord_eq_iff_derives g u v).mp
    apply hi
    apply Subtype.ext
    apply LinearEquiv.ext
    intro p
    simpa only [presentedSymplecticInterpret_apply] using huv p

end QuditClifford.Circuit
