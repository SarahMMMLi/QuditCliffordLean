import QuditClifford.CircuitInverses
import QuditClifford.MultiplierSoundness
import QuditClifford.GeneratedClifford

/-!
# The group genuinely presented by Figure 1

The quotient identifies words exactly when they are connected by contextual
Figure 1 and structural rewrites. Its group structure follows from the derived
primitive inverse words. Matrix interpretation is a separate homomorphism;
its injectivity is equivalent to the still separate completeness obligation.
-/

noncomputable section
namespace QuditClifford.Circuit

variable {d n : ℕ} [NeZero d]

/-- Primitive circuit words modulo the actual proposed rewrite derivations. -/
def PresentedCircuit (g : (ZMod d)ˣ) (n : ℕ) :=
  Quotient (Presentation.rewriteSetoid (Rules (n := n) g))

/-- The class of a primitive circuit word in the syntactic quotient. -/
def classWord (g : (ZMod d)ˣ) (w : Word n) : PresentedCircuit g n := Quotient.mk _ w

/-- Equality in the quotient is exactly contextual derivability, not semantic equality. -/
theorem classWord_eq_iff_derives (g : (ZMod d)ˣ) (u v : Word n) :
    classWord g u = classWord g v ↔ Derives g u v :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- Every presented element is represented by a primitive word. -/
theorem classWord_surjective (g : (ZMod d)ˣ) : Function.Surjective (classWord (n := n) g) := by
  intro q
  exact Quotient.exists_rep q

instance (g : (ZMod d)ˣ) : One (PresentedCircuit g n) := ⟨classWord g []⟩
instance (g : (ZMod d)ˣ) : Mul (PresentedCircuit g n) :=
  ⟨Quotient.map₂ (· ++ ·) (fun _ _ h₁ _ _ h₂ => h₁.append h₂)⟩

@[simp] theorem classWord_nil (g : (ZMod d)ˣ) : classWord (n := n) g [] = 1 := rfl

@[simp] theorem classWord_append (g : (ZMod d)ˣ) (u v : Word n) :
    classWord g (u ++ v) = classWord g u * classWord g v := rfl

instance (g : (ZMod d)ˣ) : Monoid (PresentedCircuit g n) where
  mul_assoc := by
    intro a b c
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b =>
        induction c using Quotient.inductionOn with | h c =>
          change classWord g ((a ++ b) ++ c) = classWord g (a ++ (b ++ c))
          rw [List.append_assoc]
  one_mul := by
    intro a
    induction a using Quotient.inductionOn with | h a => rfl
  mul_one := by
    intro a
    induction a using Quotient.inductionOn with | h a =>
      change classWord g (a ++ []) = classWord g a
      rw [List.append_nil]

variable [Fact d.Prime]

/-- Derived inverses respect contextual equivalence, by syntactic cancellation. -/
theorem derives_inverseWord (hd : Odd d) (g : (ZMod d)ˣ) (hg : orderOf g = d-1)
    {u v : Word n} (h : Derives g u v) :
    Derives g (inverseWord d u) (inverseWord d v) := by
  apply derives_cancel_left hd g hg (w := u)
  exact (derives_append_inverseWord hd g hg u).trans
    ((derives_append_inverseWord hd g hg v).symm.trans
      (h.symm.append_right (inverseWord d v)))

instance (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)] :
    Inv (PresentedCircuit g n) :=
  ⟨Quotient.map (inverseWord d) (fun _ _ h => derives_inverseWord Fact.out g Fact.out h)⟩

instance (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)] :
    Group (PresentedCircuit g n) where
  inv_mul_cancel := by
    intro a
    induction a using Quotient.inductionOn with | h a =>
      exact Quotient.sound (derives_inverseWord_append Fact.out g Fact.out a)

@[simp] theorem classWord_inverseWord (g : (ZMod d)ˣ) [Fact (Odd d)]
    [Fact (orderOf g = d-1)] (w : Word n) :
    classWord g (inverseWord d w) = (classWord g w)⁻¹ := rfl

/-- Exact unitary interpretation of the syntactically presented circuit monoid.
The map is defined by the proved soundness theorem; injectivity is not assumed. -/
def presentedInterpret (hd : Odd d) (g : (ZMod d)ˣ) :
    PresentedCircuit g n →* Matrix.unitaryGroup (Pauli.Basis d n) ℂ where
  toFun := Quotient.lift (unitaryDenote (d := d))
    (fun u v h => Subtype.ext (figure1_sound hd g u v h))
  map_one' := rfl
  map_mul' := by
    intro a b
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b =>
        exact unitaryDenote_append a b

@[simp] theorem presentedInterpret_classWord (hd : Odd d) (g : (ZMod d)ˣ) (w : Word n) :
    presentedInterpret hd g (classWord g w) = unitaryDenote (d := d) w := rfl

/-- Figure 1 completeness is precisely faithfulness of the syntactic quotient's
exact matrix interpretation. Neither side is presumed true. -/
theorem figure1Complete_iff_presentedInterpret_injective (hd : Odd d) (g : (ZMod d)ˣ) :
    Figure1Complete (n := n) g ↔ Function.Injective (presentedInterpret (n := n) hd g) := by
  constructor
  · intro hc a b hab
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b =>
        apply Quotient.sound
        apply hc a b
        exact congrArg Subtype.val hab
  · intro hi u v huv
    apply (classWord_eq_iff_derives g u v).mp
    apply hi
    exact Subtype.ext huv

/-- Exact interpretation corestricted to the actual matrix subgroup generated by the primitives. -/
def presentedToGenerated (hd : Odd d) (g : (ZMod d)ˣ) :
    PresentedCircuit g n →* generatedCliffordGroup d n where
  toFun := Quotient.lift (generatedWord (d := d))
    (fun u v h => Subtype.ext (Subtype.ext (figure1_sound hd g u v h)))
  map_one' := rfl
  map_mul' := by
    intro a b
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b =>
        exact generatedWord_append a b

@[simp] theorem presentedToGenerated_classWord (hd : Odd d) (g : (ZMod d)ˣ) (w : Word n) :
    presentedToGenerated hd g (classWord g w) = generatedWord (d := d) w := rfl

/-- The syntactically presented group covers the actual generated matrix group. -/
theorem presentedToGenerated_surjective (hd : Odd d) (g : (ZMod d)ˣ) :
    Function.Surjective (presentedToGenerated (n := n) hd g) := by
  intro U
  obtain ⟨w, hw⟩ := generatedWord_surjective hd U
  exact ⟨classWord g w, hw⟩

/-- Corestriction does not change the exact unitary interpretation. -/
@[simp] theorem presentedToGenerated_val (hd : Odd d) (g : (ZMod d)ˣ)
    (q : PresentedCircuit g n) :
    (presentedToGenerated hd g q).val = presentedInterpret hd g q := by
  induction q using Quotient.inductionOn with | h w => rfl

/-- Completeness is exactly the unresolved injectivity of the surjective
homomorphism from the proposed presentation to the actual generated group. -/
theorem figure1Complete_iff_presentedToGenerated_injective (hd : Odd d) (g : (ZMod d)ˣ) :
    Figure1Complete (n := n) g ↔ Function.Injective (presentedToGenerated (n := n) hd g) := by
  rw [figure1Complete_iff_presentedInterpret_injective hd g]
  constructor
  · intro hi a b hab
    apply hi
    simpa using congrArg Subtype.val hab
  · intro hi a b hab
    apply hi
    apply Subtype.ext
    simpa using hab

/-- Once completeness is proved, the syntactic and generated matrix groups are
canonically isomorphic. The completeness argument remains an explicit input. -/
def presentedGeneratedEquiv (hd : Odd d) (g : (ZMod d)ˣ)
    (hc : Figure1Complete (n := n) g) : PresentedCircuit g n ≃* generatedCliffordGroup d n :=
  MulEquiv.ofBijective (presentedToGenerated hd g)
    ⟨(figure1Complete_iff_presentedToGenerated_injective hd g).mp hc,
      presentedToGenerated_surjective hd g⟩

end QuditClifford.Circuit
