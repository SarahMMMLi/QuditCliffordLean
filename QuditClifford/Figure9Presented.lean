import QuditClifford.Figure9Inverses

/-! # The group presented by Figure 9

Scalar letters are removed before comparing representatives, because the source
alphabet contains only H, S, and adjacent CZ. Its equivalence relation consists
solely of the eighteen equations and wiring rules. Each class has an explicitly
scalar-free representative; no Pauli-deletion equation is assumed.
-/

noncomputable section
namespace QuditClifford.Circuit
variable {d n : ℕ} [NeZero d]

/-- A broad word certified to use only the paper's canonical adjacent alphabet. -/
abbrev Figure9CertifiedWord (n : ℕ) := {w : Word n // IsAdjacentWord w}

/-- The restricted rewrite relation on certified adjacent representatives. -/
def figure9RewriteSetoid (g : (ZMod d)ˣ) (n : ℕ) : Setoid (Figure9CertifiedWord n) where
  r u v := Figure9Derives g (eraseScalar u.val) (eraseScalar v.val)
  iseqv := ⟨fun _ => .refl _, fun h => h.symm, fun h k => h.trans k⟩

/-- The syntactic quotient of adjacent words by guarded Figure 9 rewrites. -/
def Figure9Presented (g : (ZMod d)ˣ) (n : ℕ) :=
  Quotient (figure9RewriteSetoid g n)

/-- The class of an adjacent word. Its value does not depend on the adjacency proof. -/
def figure9ClassWord (g : (ZMod d)ˣ) (w : Word n) (hw : IsAdjacentWord w) :
    Figure9Presented g n := Quotient.mk _ ⟨w, hw⟩

/-- Quotient equality is exactly scalar-free Figure 9 derivability. -/
theorem figure9ClassWord_eq_iff_derives (g : (ZMod d)ˣ) (u v : Word n)
    (hu : IsAdjacentWord u) (hv : IsAdjacentWord v) :
    figure9ClassWord g u hu = figure9ClassWord g v hv ↔ Figure9Derives g (eraseScalar u) (eraseScalar v) :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- A derivation of adjacent source words yields equality of their classes. -/
theorem figure9ClassWord_eq_of_derives (g : (ZMod d)ˣ) {u v : Word n}
    (hu : IsAdjacentWord u) (hv : IsAdjacentWord v) (h : Figure9Derives g u v) :
    figure9ClassWord g u hu = figure9ClassWord g v hv :=
  (figure9ClassWord_eq_iff_derives g u v hu hv).mpr (h.eraseScalar g)

/-- Each generating equation is equality of its two classes. -/
theorem figure9ClassWord_eq_of_rule (g : (ZMod d)ˣ) {u v : Word n}
    (h : Figure9Rules g u v) :
    figure9ClassWord g u h.2.1 = figure9ClassWord g v h.2.2.1 := by
  apply (figure9ClassWord_eq_iff_derives g u v h.2.1 h.2.2.1).mpr
  rw [h.2.2.2.1, h.2.2.2.2]
  exact .rule h

/-- Every quotient element has an adjacent word representative. -/
theorem figure9ClassWord_exists (g : (ZMod d)ˣ) (q : Figure9Presented g n) :
    ∃ w : Word n, ∃ hw : IsAdjacentWord w, figure9ClassWord g w hw = q := by
  obtain ⟨⟨w, hw⟩, h⟩ := Quotient.exists_rep q
  exact ⟨w, hw, h⟩

instance (g : (ZMod d)ˣ) : One (Figure9Presented g n) :=
  ⟨figure9ClassWord g [] isAdjacentWord_nil⟩
instance (g : (ZMod d)ˣ) : Mul (Figure9Presented g n) :=
  ⟨Quotient.map₂
    (fun u v => ⟨u.val ++ v.val, (isAdjacentWord_append _ _).mpr ⟨u.property, v.property⟩⟩)
    (fun u v h₁ w x h₂ => by
      change Figure9Derives g (eraseScalar (u.val ++ w.val)) (eraseScalar (v.val ++ x.val))
      simpa only [eraseScalar_append] using h₁.append h₂)⟩

@[simp] theorem figure9ClassWord_nil (g : (ZMod d)ˣ) :
    figure9ClassWord (n := n) g [] isAdjacentWord_nil = 1 := rfl

@[simp] theorem figure9ClassWord_append (g : (ZMod d)ˣ) (u v : Word n)
    (hu : IsAdjacentWord u) (hv : IsAdjacentWord v) :
    figure9ClassWord g (u ++ v) ((isAdjacentWord_append _ _).mpr ⟨hu, hv⟩) =
      figure9ClassWord g u hu * figure9ClassWord g v hv := rfl

/-- A certificate for an append supplies both certificates needed by the
simplifier, even when it is not syntactically constructed as a pair. -/
@[simp] theorem figure9ClassWord_append_certified (g : (ZMod d)ˣ) (u v : Word n)
    (hw : IsAdjacentWord (u ++ v)) :
    figure9ClassWord g (u ++ v) hw =
      figure9ClassWord g u ((isAdjacentWord_append u v).mp hw).1 *
        figure9ClassWord g v ((isAdjacentWord_append u v).mp hw).2 := rfl

instance (g : (ZMod d)ˣ) : Monoid (Figure9Presented g n) where
  mul_assoc := by
    intro a b c
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b =>
        induction c using Quotient.inductionOn with | h c =>
          apply Quotient.sound
          change Figure9Derives g (eraseScalar ((a.val ++ b.val) ++ c.val))
            (eraseScalar (a.val ++ (b.val ++ c.val)))
          rw [List.append_assoc]
          exact .refl _
  one_mul := by
    intro a
    induction a using Quotient.inductionOn with | h a => rfl
  mul_one := by
    intro a
    induction a using Quotient.inductionOn with | h a =>
      apply Quotient.sound
      change Figure9Derives g (eraseScalar (a.val ++ [])) (eraseScalar a.val)
      rw [List.append_nil]
      exact .refl _

@[simp] theorem figure9ClassWord_power (g : (ZMod d)ˣ) (w : Word n)
    (hw : IsAdjacentWord w) (k : ℕ) :
    figure9ClassWord g (power w k) (hw.power k) = (figure9ClassWord g w hw)^k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [power_succ]
    rw [figure9ClassWord_append g w (power w k) hw (hw.power k), ih, pow_succ']

@[simp] theorem figure9ClassWord_replicate (g : (ZMod d)ˣ) (a : Gate n)
    (ha : a.IsAdjacent) (k : ℕ) :
    figure9ClassWord g (List.replicate k a) (IsAdjacentWord.replicate ha k) =
      (figure9ClassWord g [a] ((isAdjacentWord_cons _ _).mpr ⟨ha, isAdjacentWord_nil⟩))^k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hl : List.replicate (k+1) a = [a] ++ List.replicate k a := by
      simp only [List.replicate_succ, List.cons_append, List.nil_append]
    simp only [hl]
    rw [figure9ClassWord_append g [a] (List.replicate k a)
      ((isAdjacentWord_cons _ _).mpr ⟨ha, isAdjacentWord_nil⟩)
      (IsAdjacentWord.replicate ha k), ih, pow_succ']


/-- Each class admits the explicit scalar-free representative obtained by erasure. -/
theorem figure9ClassWord_eraseScalar (g : (ZMod d)ˣ) (w : Word n)
    (hw : IsAdjacentWord w) :
    figure9ClassWord g (eraseScalar w) (hw.eraseScalar) = figure9ClassWord g w hw := by
  apply Quotient.sound
  change Figure9Derives g (eraseScalar (eraseScalar w)) (eraseScalar w)
  rw [eraseScalar_idempotent]
  exact .refl _

variable [Fact d.Prime]

instance (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)] :
    Inv (Figure9Presented g n) :=
  ⟨Quotient.map (fun w => ⟨inverseWord d w.val, w.property.inverseWord d⟩)
    (fun u v h => figure9Derives_inverseWord Fact.out g Fact.out u.property v.property h)⟩

instance (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)] :
    Group (Figure9Presented g n) where
  inv_mul_cancel := by
    intro a
    induction a using Quotient.inductionOn with | h a =>
      exact Quotient.sound (figure9Derives_inverseWord_append Fact.out g Fact.out a.val a.property)

@[simp] theorem figure9ClassWord_inverseWord (g : (ZMod d)ˣ) [Fact (Odd d)]
    [Fact (orderOf g = d-1)] (w : Word n) (hw : IsAdjacentWord w) :
    figure9ClassWord g (inverseWord d w) (hw.inverseWord d) =
      (figure9ClassWord g w hw)⁻¹ := rfl

end QuditClifford.Circuit
