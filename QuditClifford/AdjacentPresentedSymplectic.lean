import QuditClifford.AdjacentPresentedCircuit
import QuditClifford.AdjacentSymplecticRewrites

/-!
# The adjacent presentation with explicit Pauli erasure

This quotient uses guarded symplectic derivations on certified adjacent words.
Its inverse operations are proved by exact adjacent cancellation followed by
erasure. Exponent interpretation is soundness in the forward direction only;
no injectivity or kernel characterization is assumed.
-/

noncomputable section
namespace QuditClifford.Circuit
variable {d n : ℕ} [NeZero d]

/-- The restricted Pauli-erased rewrite relation on certified adjacent representatives. -/
def adjacentSymplecticRewriteSetoid (g : (ZMod d)ˣ) (n : ℕ) : Setoid (AdjacentCertifiedWord n) where
  r u v := AdjacentSymplecticDerives g u.val v.val
  iseqv := ⟨fun _ => .refl _, fun h => h.symm, fun h k => h.trans k⟩

/-- The syntactic quotient of adjacent words by guarded Figure 1 rewrites and explicit Pauli erasure. -/
def AdjacentPresentedSymplectic (g : (ZMod d)ˣ) (n : ℕ) :=
  Quotient (adjacentSymplecticRewriteSetoid g n)

/-- The class of an adjacent word. Its value does not depend on the adjacency proof. -/
def adjacentSymplecticClassWord (g : (ZMod d)ˣ) (w : Word n) (hw : IsAdjacentWord w) :
    AdjacentPresentedSymplectic g n := Quotient.mk _ ⟨w, hw⟩

/-- Quotient equality is exactly restricted syntactic derivability. -/
theorem adjacentSymplecticClassWord_eq_iff_derives (g : (ZMod d)ˣ) (u v : Word n)
    (hu : IsAdjacentWord u) (hv : IsAdjacentWord v) :
    adjacentSymplecticClassWord g u hu = adjacentSymplecticClassWord g v hv ↔ AdjacentSymplecticDerives g u v :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- Every quotient element has an adjacent word representative. -/
theorem adjacentSymplecticClassWord_exists (g : (ZMod d)ˣ) (q : AdjacentPresentedSymplectic g n) :
    ∃ w : Word n, ∃ hw : IsAdjacentWord w, adjacentSymplecticClassWord g w hw = q := by
  obtain ⟨⟨w, hw⟩, h⟩ := Quotient.exists_rep q
  exact ⟨w, hw, h⟩

instance (g : (ZMod d)ˣ) : One (AdjacentPresentedSymplectic g n) :=
  ⟨adjacentSymplecticClassWord g [] isAdjacentWord_nil⟩
instance (g : (ZMod d)ˣ) : Mul (AdjacentPresentedSymplectic g n) :=
  ⟨Quotient.map₂
    (fun u v => ⟨u.val ++ v.val, (isAdjacentWord_append _ _).mpr ⟨u.property, v.property⟩⟩)
    (fun _ _ h₁ _ _ h₂ => h₁.append h₂)⟩

@[simp] theorem adjacentSymplecticClassWord_nil (g : (ZMod d)ˣ) :
    adjacentSymplecticClassWord (n := n) g [] isAdjacentWord_nil = 1 := rfl

@[simp] theorem adjacentSymplecticClassWord_append (g : (ZMod d)ˣ) (u v : Word n)
    (hu : IsAdjacentWord u) (hv : IsAdjacentWord v) :
    adjacentSymplecticClassWord g (u ++ v) ((isAdjacentWord_append _ _).mpr ⟨hu, hv⟩) =
      adjacentSymplecticClassWord g u hu * adjacentSymplecticClassWord g v hv := rfl

/-- A certificate for an append supplies both certificates needed by the
simplifier, even when it is not syntactically constructed as a pair. -/
@[simp] theorem adjacentSymplecticClassWord_append_certified (g : (ZMod d)ˣ) (u v : Word n)
    (hw : IsAdjacentWord (u ++ v)) :
    adjacentSymplecticClassWord g (u ++ v) hw =
      adjacentSymplecticClassWord g u ((isAdjacentWord_append u v).mp hw).1 *
        adjacentSymplecticClassWord g v ((isAdjacentWord_append u v).mp hw).2 := rfl

instance (g : (ZMod d)ˣ) : Monoid (AdjacentPresentedSymplectic g n) where
  mul_assoc := by
    intro a b c
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b =>
        induction c using Quotient.inductionOn with | h c =>
          apply Quotient.sound
          change AdjacentSymplecticDerives g ((a.val ++ b.val) ++ c.val) (a.val ++ (b.val ++ c.val))
          rw [List.append_assoc]
          exact .refl _
  one_mul := by
    intro a
    induction a using Quotient.inductionOn with | h a => rfl
  mul_one := by
    intro a
    induction a using Quotient.inductionOn with | h a =>
      apply Quotient.sound
      change AdjacentSymplecticDerives g (a.val ++ []) a.val
      rw [List.append_nil]
      exact .refl _

@[simp] theorem adjacentSymplecticClassWord_power (g : (ZMod d)ˣ) (w : Word n)
    (hw : IsAdjacentWord w) (k : ℕ) :
    adjacentSymplecticClassWord g (power w k) (hw.power k) = (adjacentSymplecticClassWord g w hw)^k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [power_succ]
    rw [adjacentSymplecticClassWord_append g w (power w k) hw (hw.power k), ih, pow_succ']

@[simp] theorem adjacentSymplecticClassWord_replicate (g : (ZMod d)ˣ) (a : Gate n)
    (ha : a.IsAdjacent) (k : ℕ) :
    adjacentSymplecticClassWord g (List.replicate k a) (IsAdjacentWord.replicate ha k) =
      (adjacentSymplecticClassWord g [a] ((isAdjacentWord_cons _ _).mpr ⟨ha, isAdjacentWord_nil⟩))^k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hl : List.replicate (k+1) a = [a] ++ List.replicate k a := by
      simp only [List.replicate_succ, List.cons_append, List.nil_append]
    simp only [hl]
    rw [adjacentSymplecticClassWord_append g [a] (List.replicate k a)
      ((isAdjacentWord_cons _ _).mpr ⟨ha, isAdjacentWord_nil⟩)
      (IsAdjacentWord.replicate ha k), ih, pow_succ']

/-- The exact adjacent presentation maps to its explicit Pauli erasure. -/
def adjacentPresentedToSymplectic (g : (ZMod d)ˣ) :
    AdjacentPresentedCircuit g n →* AdjacentPresentedSymplectic g n where
  toFun := Quotient.map id (fun _ _ h => adjacentDerives_symplectic g h)
  map_one' := rfl
  map_mul' := by
    intro a b
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b => rfl

@[simp] theorem adjacentPresentedToSymplectic_classWord (g : (ZMod d)ˣ)
    (w : Word n) (hw : IsAdjacentWord w) :
    adjacentPresentedToSymplectic g (adjacentClassWord g w hw) =
      adjacentSymplecticClassWord g w hw := rfl

/-- Exact classes cover all explicitly erased adjacent classes. -/
theorem adjacentPresentedToSymplectic_surjective (g : (ZMod d)ˣ) :
    Function.Surjective (adjacentPresentedToSymplectic (n := n) g) := by
  intro q
  obtain ⟨w, hw, rfl⟩ := adjacentSymplecticClassWord_exists g q
  exact ⟨adjacentClassWord g w hw, rfl⟩

/-- Forgetting the adjacency certificate preserves the erased rewrite relation. -/
def adjacentSymplecticToPresentedSymplectic (g : (ZMod d)ˣ) :
    AdjacentPresentedSymplectic g n →* PresentedSymplectic g n where
  toFun := Quotient.lift (fun w => symplecticClassWord g w.val)
    (fun _ _ h => Quotient.sound (AdjacentSymplecticDerives.toSymplecticDerives g h))
  map_one' := rfl
  map_mul' := by
    intro a b
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b => rfl

@[simp] theorem adjacentSymplecticToPresentedSymplectic_classWord (g : (ZMod d)ˣ)
    (w : Word n) (hw : IsAdjacentWord w) :
    adjacentSymplecticToPresentedSymplectic g (adjacentSymplecticClassWord g w hw) =
      symplecticClassWord g w := rfl

/-- Primitive scalar deletion is an explicit guarded generating rule. -/
theorem adjacentSymplecticDerives_scalar (g : (ZMod d)ˣ) (k : ℕ) :
    AdjacentSymplecticDerives (n := n) g (scalar k) [] := by
  induction k with
  | zero => exact .refl _
  | succ k ih =>
    have h : AdjacentSymplecticDerives (n := n) g [.scalar] [] :=
      .rule ⟨Or.inl (Or.inr ⟨rfl, rfl⟩), by simp, isAdjacentWord_nil⟩
    simpa only [scalar, List.replicate_succ, List.cons_append, List.nil_append] using h.append ih

/-- Expanded X and Z deletion remain guarded by the one-wire alphabet. -/
theorem adjacentSymplecticDerives_X (g : (ZMod d)ˣ) (i : Fin n) :
    AdjacentSymplecticDerives g (X (d := d) i) [] :=
  .rule ⟨Or.inr ⟨i, Or.inl rfl, rfl⟩, isAdjacentWord_X i, isAdjacentWord_nil⟩

theorem adjacentSymplecticDerives_Z (g : (ZMod d)ˣ) (i : Fin n) :
    AdjacentSymplecticDerives g (Z (d := d) i) [] :=
  .rule ⟨Or.inr ⟨i, Or.inr rfl, rfl⟩, isAdjacentWord_Z i, isAdjacentWord_nil⟩

@[simp] theorem adjacentSymplecticClassWord_scalar (g : (ZMod d)ˣ) (k : ℕ) :
    adjacentSymplecticClassWord (n := n) g (scalar k) (isAdjacentWord_scalar k) = 1 :=
  Quotient.sound (adjacentSymplecticDerives_scalar g k)

@[simp] theorem adjacentSymplecticClassWord_X (g : (ZMod d)ˣ) (i : Fin n) :
    adjacentSymplecticClassWord g (X (d := d) i) (isAdjacentWord_X i) = 1 :=
  Quotient.sound (adjacentSymplecticDerives_X g i)

@[simp] theorem adjacentSymplecticClassWord_Z (g : (ZMod d)ˣ) (i : Fin n) :
    adjacentSymplecticClassWord g (Z (d := d) i) (isAdjacentWord_Z i) = 1 :=
  Quotient.sound (adjacentSymplecticDerives_Z g i)

variable [Fact d.Prime]

/-- Common adjacent left contexts cancel after the exact inverse proof is erased. -/
theorem adjacentSymplecticDerives_cancel_left (hd : Odd d) (g : (ZMod d)ˣ)
    (hg : orderOf g = d-1) {u v w : Word n} (hw : IsAdjacentWord w)
    (h : AdjacentSymplecticDerives g (w ++ u) (w ++ v)) :
    AdjacentSymplecticDerives g u v := by
  have hc := adjacentDerives_symplectic g
    (adjacentDerives_inverseWord_append hd g hg w hw)
  have hu : AdjacentSymplecticDerives g (inverseWord d w ++ (w ++ u)) u := by
    simpa only [List.append_assoc, List.nil_append] using hc.append_right u
  have hv : AdjacentSymplecticDerives g (inverseWord d w ++ (w ++ v)) v := by
    simpa only [List.append_assoc, List.nil_append] using hc.append_right v
  exact hu.symm.trans ((h.append_left (inverseWord d w)).trans hv)

/-- Inverse words respect the guarded erased presentation by syntactic cancellation. -/
theorem adjacentSymplecticDerives_inverseWord (hd : Odd d) (g : (ZMod d)ˣ)
    (hg : orderOf g = d-1) {u v : Word n} (hu : IsAdjacentWord u)
    (hv : IsAdjacentWord v) (h : AdjacentSymplecticDerives g u v) :
    AdjacentSymplecticDerives g (inverseWord d u) (inverseWord d v) := by
  apply adjacentSymplecticDerives_cancel_left hd g hg hu
  exact (adjacentDerives_symplectic g (adjacentDerives_append_inverseWord hd g hg u hu)).trans
    ((adjacentDerives_symplectic g (adjacentDerives_append_inverseWord hd g hg v hv)).symm.trans
      (h.symm.append_right (inverseWord d v)))

instance (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)] :
    Inv (AdjacentPresentedSymplectic g n) :=
  ⟨Quotient.map (fun w => ⟨inverseWord d w.val, w.property.inverseWord d⟩)
    (fun u v h => adjacentSymplecticDerives_inverseWord Fact.out g Fact.out
      u.property v.property h)⟩

instance (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)] :
    Group (AdjacentPresentedSymplectic g n) where
  inv_mul_cancel := by
    intro a
    induction a using Quotient.inductionOn with | h a =>
      exact Quotient.sound (adjacentDerives_symplectic g
        (adjacentDerives_inverseWord_append Fact.out g Fact.out a.val a.property))

@[simp] theorem adjacentSymplecticClassWord_inverseWord (g : (ZMod d)ˣ) [Fact (Odd d)]
    [Fact (orderOf g = d-1)] (w : Word n) (hw : IsAdjacentWord w) :
    adjacentSymplecticClassWord g (inverseWord d w) (hw.inverseWord d) =
      (adjacentSymplecticClassWord g w hw)⁻¹ := rfl

/-- The sound exponent interpretation of the adjacent erased presentation. -/
def adjacentPresentedSymplecticInterpret (hd : Odd d) (g : (ZMod d)ˣ) :
    AdjacentPresentedSymplectic g n →* symplecticGroup d n :=
  (presentedSymplecticInterpret hd g).comp (adjacentSymplecticToPresentedSymplectic g)

@[simp] theorem adjacentPresentedSymplecticInterpret_classWord (hd : Odd d) (g : (ZMod d)ˣ)
    (w : Word n) (hw : IsAdjacentWord w) :
    adjacentPresentedSymplecticInterpret hd g (adjacentSymplecticClassWord g w hw) =
      generatedSymplecticHom hd (generatedWord w) := rfl

@[simp] theorem adjacentPresentedSymplecticInterpret_apply (hd : Odd d) (g : (ZMod d)ˣ)
    (w : Word n) (hw : IsAdjacentWord w) (p : PhaseSpace d n) :
    (adjacentPresentedSymplecticInterpret hd g (adjacentSymplecticClassWord g w hw)).val p =
      symplecticAction d w p := generatedSymplecticHom_word hd w p

/-- Syntactic erasure commutes with the exponent action of the exact matrix map. -/
theorem adjacentPresentedSymplecticInterpret_comp (hd : Odd d) (g : (ZMod d)ˣ) :
    (adjacentPresentedSymplecticInterpret (n := n) hd g).comp (adjacentPresentedToSymplectic g) =
      (generatedSymplecticHom hd).comp (adjacentPresentedToGenerated hd g) := by
  apply MonoidHom.ext
  intro q
  induction q using Quotient.inductionOn with | h w => rfl

end QuditClifford.Circuit
