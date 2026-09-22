import QuditClifford.AdjacentCircuitInverses

/-!
# The group presented by the adjacent Figure 1 alphabet

Representatives carry a proof that each CZ acts on an ordered neighboring pair.
Equality is precisely derivability in the restricted presentation. Group
operations come from explicit circuit words and the syntactic inverse proofs.
Exact matrix interpretation is a separate homomorphism, with no assumed
faithfulness or completeness.
-/

noncomputable section
namespace QuditClifford.Circuit
variable {d n : ℕ} [NeZero d]

/-- A broad word certified to use only the paper's canonical adjacent alphabet. -/
abbrev AdjacentCertifiedWord (n : ℕ) := {w : Word n // IsAdjacentWord w}

/-- The restricted rewrite relation on certified adjacent representatives. -/
def adjacentRewriteSetoid (g : (ZMod d)ˣ) (n : ℕ) : Setoid (AdjacentCertifiedWord n) where
  r u v := AdjacentDerives g u.val v.val
  iseqv := ⟨fun _ => .refl _, fun h => h.symm, fun h k => h.trans k⟩

/-- The syntactic quotient of adjacent words by guarded Figure 1 rewrites. -/
def AdjacentPresentedCircuit (g : (ZMod d)ˣ) (n : ℕ) :=
  Quotient (adjacentRewriteSetoid g n)

/-- The class of an adjacent word. Its value does not depend on the adjacency proof. -/
def adjacentClassWord (g : (ZMod d)ˣ) (w : Word n) (hw : IsAdjacentWord w) :
    AdjacentPresentedCircuit g n := Quotient.mk _ ⟨w, hw⟩

/-- Quotient equality is exactly restricted syntactic derivability. -/
theorem adjacentClassWord_eq_iff_derives (g : (ZMod d)ˣ) (u v : Word n)
    (hu : IsAdjacentWord u) (hv : IsAdjacentWord v) :
    adjacentClassWord g u hu = adjacentClassWord g v hv ↔ AdjacentDerives g u v :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- Every quotient element has an adjacent word representative. -/
theorem adjacentClassWord_exists (g : (ZMod d)ˣ) (q : AdjacentPresentedCircuit g n) :
    ∃ w : Word n, ∃ hw : IsAdjacentWord w, adjacentClassWord g w hw = q := by
  obtain ⟨⟨w, hw⟩, h⟩ := Quotient.exists_rep q
  exact ⟨w, hw, h⟩

instance (g : (ZMod d)ˣ) : One (AdjacentPresentedCircuit g n) :=
  ⟨adjacentClassWord g [] isAdjacentWord_nil⟩
instance (g : (ZMod d)ˣ) : Mul (AdjacentPresentedCircuit g n) :=
  ⟨Quotient.map₂
    (fun u v => ⟨u.val ++ v.val, (isAdjacentWord_append _ _).mpr ⟨u.property, v.property⟩⟩)
    (fun _ _ h₁ _ _ h₂ => h₁.append h₂)⟩

@[simp] theorem adjacentClassWord_nil (g : (ZMod d)ˣ) :
    adjacentClassWord (n := n) g [] isAdjacentWord_nil = 1 := rfl

@[simp] theorem adjacentClassWord_append (g : (ZMod d)ˣ) (u v : Word n)
    (hu : IsAdjacentWord u) (hv : IsAdjacentWord v) :
    adjacentClassWord g (u ++ v) ((isAdjacentWord_append _ _).mpr ⟨hu, hv⟩) =
      adjacentClassWord g u hu * adjacentClassWord g v hv := rfl

/-- A certificate for an append supplies both certificates needed by the
simplifier, even when it is not syntactically constructed as a pair. -/
@[simp] theorem adjacentClassWord_append_certified (g : (ZMod d)ˣ) (u v : Word n)
    (hw : IsAdjacentWord (u ++ v)) :
    adjacentClassWord g (u ++ v) hw =
      adjacentClassWord g u ((isAdjacentWord_append u v).mp hw).1 *
        adjacentClassWord g v ((isAdjacentWord_append u v).mp hw).2 := rfl

instance (g : (ZMod d)ˣ) : Monoid (AdjacentPresentedCircuit g n) where
  mul_assoc := by
    intro a b c
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b =>
        induction c using Quotient.inductionOn with | h c =>
          apply Quotient.sound
          change AdjacentDerives g ((a.val ++ b.val) ++ c.val) (a.val ++ (b.val ++ c.val))
          rw [List.append_assoc]
          exact .refl _
  one_mul := by
    intro a
    induction a using Quotient.inductionOn with | h a => rfl
  mul_one := by
    intro a
    induction a using Quotient.inductionOn with | h a =>
      apply Quotient.sound
      change AdjacentDerives g (a.val ++ []) a.val
      rw [List.append_nil]
      exact .refl _

@[simp] theorem adjacentClassWord_power (g : (ZMod d)ˣ) (w : Word n)
    (hw : IsAdjacentWord w) (k : ℕ) :
    adjacentClassWord g (power w k) (hw.power k) = (adjacentClassWord g w hw)^k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [power_succ]
    rw [adjacentClassWord_append g w (power w k) hw (hw.power k), ih, pow_succ']

@[simp] theorem adjacentClassWord_replicate (g : (ZMod d)ˣ) (a : Gate n)
    (ha : a.IsAdjacent) (k : ℕ) :
    adjacentClassWord g (List.replicate k a) (IsAdjacentWord.replicate ha k) =
      (adjacentClassWord g [a] ((isAdjacentWord_cons _ _).mpr ⟨ha, isAdjacentWord_nil⟩))^k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hl : List.replicate (k+1) a = [a] ++ List.replicate k a := by
      simp only [List.replicate_succ, List.cons_append, List.nil_append]
    simp only [hl]
    rw [adjacentClassWord_append g [a] (List.replicate k a)
      ((isAdjacentWord_cons _ _).mpr ⟨ha, isAdjacentWord_nil⟩)
      (IsAdjacentWord.replicate ha k), ih, pow_succ']

/-- Forgetting the alphabet certificate gives a homomorphism to the broader
named-wire presentation. No claim of injectivity is made. -/
def adjacentPresentedToPresented (g : (ZMod d)ˣ) :
    AdjacentPresentedCircuit g n →* PresentedCircuit g n where
  toFun := Quotient.lift (fun w => classWord g w.val)
    (fun u v h => Quotient.sound (AdjacentDerives.toDerives g h))
  map_one' := rfl
  map_mul' := by
    intro a b
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b => rfl

@[simp] theorem adjacentPresentedToPresented_classWord (g : (ZMod d)ˣ)
    (w : Word n) (hw : IsAdjacentWord w) :
    adjacentPresentedToPresented g (adjacentClassWord g w hw) = classWord g w := rfl

variable [Fact d.Prime]

instance (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)] :
    Inv (AdjacentPresentedCircuit g n) :=
  ⟨Quotient.map (fun w => ⟨inverseWord d w.val, w.property.inverseWord d⟩)
    (fun u v h => adjacentDerives_inverseWord Fact.out g Fact.out u.property v.property h)⟩

instance (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)] :
    Group (AdjacentPresentedCircuit g n) where
  inv_mul_cancel := by
    intro a
    induction a using Quotient.inductionOn with | h a =>
      exact Quotient.sound (adjacentDerives_inverseWord_append Fact.out g Fact.out a.val a.property)

@[simp] theorem adjacentClassWord_inverseWord (g : (ZMod d)ˣ) [Fact (Odd d)]
    [Fact (orderOf g = d-1)] (w : Word n) (hw : IsAdjacentWord w) :
    adjacentClassWord g (inverseWord d w) (hw.inverseWord d) =
      (adjacentClassWord g w hw)⁻¹ := rfl

/-- Exact unitary interpretation, justified only by soundness of the rewrites. -/
def adjacentPresentedInterpret (hd : Odd d) (g : (ZMod d)ˣ) :
    AdjacentPresentedCircuit g n →* Matrix.unitaryGroup (Pauli.Basis d n) ℂ :=
  (presentedInterpret hd g).comp (adjacentPresentedToPresented g)

@[simp] theorem adjacentPresentedInterpret_classWord (hd : Odd d) (g : (ZMod d)ˣ)
    (w : Word n) (hw : IsAdjacentWord w) :
    adjacentPresentedInterpret hd g (adjacentClassWord g w hw) = unitaryDenote (d := d) w := rfl

/-- Exact interpretation corestricted to the generated Clifford matrix group. -/
def adjacentPresentedToGenerated (hd : Odd d) (g : (ZMod d)ˣ) :
    AdjacentPresentedCircuit g n →* generatedCliffordGroup d n :=
  (presentedToGenerated hd g).comp (adjacentPresentedToPresented g)

@[simp] theorem adjacentPresentedToGenerated_classWord (hd : Odd d) (g : (ZMod d)ˣ)
    (w : Word n) (hw : IsAdjacentWord w) :
    adjacentPresentedToGenerated hd g (adjacentClassWord g w hw) = generatedWord (d := d) w := rfl

/-- Corestriction retains the same exact unitary matrix. -/
@[simp] theorem adjacentPresentedToGenerated_val (hd : Odd d) (g : (ZMod d)ˣ)
    (q : AdjacentPresentedCircuit g n) :
    (adjacentPresentedToGenerated hd g q).val = adjacentPresentedInterpret hd g q := by
  induction q using Quotient.inductionOn with | h w => rfl

/-- Completeness for the source alphabet is equivalent to injectivity of its
exact interpretation; this statement does not presume either property. -/
theorem adjacentFigure1Complete_iff_adjacentPresentedInterpret_injective
    (hd : Odd d) (g : (ZMod d)ˣ) :
    AdjacentFigure1Complete (n := n) g ↔
      Function.Injective (adjacentPresentedInterpret (n := n) hd g) := by
  constructor
  · intro hc a b hab
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b =>
        apply Quotient.sound
        apply hc a.val b.val a.property b.property
        exact congrArg Subtype.val hab
  · intro hi u v hu hv huv
    apply (adjacentClassWord_eq_iff_derives g u v hu hv).mp
    apply hi
    exact Subtype.ext huv

end QuditClifford.Circuit
